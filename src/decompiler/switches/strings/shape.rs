//! The four structured forms of a lowered string switch.

use crate::decompiler::exps::{ExitType, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::stats::{StatementKind, stat_edge::EdgeType};
use crate::engine::Cx;
use crate::types::VarType;

use super::{condition, default_case, switch, switch_head};

#[derive(Clone, Copy)]
pub(super) enum Shape {
    Split,
    InlineSplit,
    NullableSplit {
        assignment: ExprId,
        null_check: StatId,
    },
    Merged,
}

#[derive(Clone, Copy)]
pub(super) struct StringSwitch {
    pub first: StatId,
    pub target: StatId,
    pub shape: Shape,
}

impl StringSwitch {
    pub(super) fn match_shape(cx: &Cx, first: StatId) -> Option<Self> {
        let ir = &cx.ir;
        if let Some(target) = regular_switch_successor(ir, first)
            && let Some(split) = (Self {
                first,
                target,
                shape: Shape::Split,
            })
            .valid(cx)
        {
            return Some(split);
        }

        if let Some(default) = default_case(ir, first) {
            let target = match ir[default].kind {
                StatementKind::Switch(_) => Some(default),
                StatementKind::Sequence => ir[default]
                    .first
                    .filter(|&st| matches!(ir[st].kind, StatementKind::Switch(_))),
                _ => None,
            };
            if let Some(target) = target
                && let Some(split) = (Self {
                    first,
                    target,
                    shape: Shape::InlineSplit,
                })
                .valid(cx)
            {
                return Some(split);
            }
        }

        if let Some(split) = Self::nullable_split(ir, first).and_then(|shape| shape.valid(cx)) {
            return Some(split);
        }
        Self {
            first,
            target: first,
            shape: Shape::Merged,
        }
        .valid(cx)
    }

    fn nullable_split(ir: &Ir, first: StatId) -> Option<Self> {
        let null_check = ir[first].parent?;
        let StatementKind::If(branch) = ir[null_check].kind else {
            return None;
        };
        if !first
            .get_successor_edges(ir, EdgeType::Regular.mask())
            .is_empty()
        {
            return None;
        }
        let ExprKind::Function {
            op: FunctionType::Ne,
            operands,
            ..
        } = &ir[condition(ir, branch)].kind
        else {
            return None;
        };
        let [_, right] = operands.as_slice() else {
            return None;
        };
        if !branch.has_else
            || !matches!(&ir[*right].kind, ExprKind::Constant { var_type, .. } if *var_type == VarType::VARTYPE_NULL)
        {
            return None;
        }
        let otherwise = branch.else_stat?;
        if !matches!(ir[otherwise].kind, StatementKind::BasicBlock { .. }) {
            return None;
        }
        let [assignment] = ir[ir[otherwise].exprents?].as_slice() else {
            return None;
        };
        ir[*assignment].as_assignment()?;
        Some(Self {
            first,
            target: regular_switch_successor(ir, null_check)?,
            shape: Shape::NullableSplit {
                assignment: *assignment,
                null_check,
            },
        })
    }

    fn valid(self, cx: &Cx) -> Option<Self> {
        let ir = &cx.ir;
        let (_, selector) = switch_head(ir, self.first).expect("Missing switch header");
        let ExprKind::Invocation(invocation) = &ir[selector].kind else {
            return None;
        };
        let cases = &switch(ir, self.first).cases;
        if invocation.name != "hashCode"
            || invocation.classname.as_deref() != Some("java/lang/String")
            || !matches!(ir[cases[0].statement].kind, StatementKind::If(_))
        {
            return None;
        }
        let intermediate = if matches!(self.shape, Shape::Merged) {
            None
        } else {
            let (_, value) = switch_head(ir, self.target).expect("Missing switch header");
            Expr::variable(ir, value)?;
            if let Shape::NullableSplit { assignment, .. } = self.shape {
                let (left, _) = ir[assignment].as_assignment().unwrap();
                if !Expr::equals(cx, left, value) {
                    return None;
                }
            }
            Some(value)
        };
        let dup = self.synthetic_dup(cx);

        for case in cases {
            if switch(ir, self.first)
                .default_edge
                .is_some_and(|edge| case.edges.contains(&edge))
            {
                continue;
            }
            let mut branch = Some(case.statement);
            while let Some(stat) = branch {
                let StatementKind::If(if_) = ir[stat].kind else {
                    return None;
                };
                let cond = remove_condition_wrapper(ir, condition(ir, if_), true);
                let is_equals = |call| equals_on(cx, call, invocation.instance, dup);
                if let ExprKind::Function { operands, .. } = &ir[cond].kind {
                    if !operands.iter().copied().all(is_equals) {
                        return None;
                    }
                } else if !is_equals(cond) {
                    return None;
                }

                let head = stat.get_basic_head(ir);
                let if_break = if_.if_stat.is_none()
                    && if_.else_stat.is_none()
                    && if_.if_edge.is_some()
                    && if_.else_edge.is_none()
                    && !head
                        .get_successor_edges(ir, EdgeType::Regular.mask())
                        .is_empty()
                    && head.get_successor_edges(ir, EdgeType::Break.mask()).len() == 1;
                if if_break {
                    if let Some(default) = default_case(ir, self.first) {
                        let next = ir[default]
                            .first_successor()
                            .expect("Default case has no successor");
                        let test = &ir[if_.if_edge.unwrap()];
                        if test.edge_type != EdgeType::Break
                            || test.destination != ir[next].destination
                        {
                            return None;
                        }
                    }
                } else {
                    let expressions = ir[if_.if_stat?].exprents?;
                    let [only] = ir[expressions].as_slice() else {
                        return None;
                    };
                    let valid = if let Some(intermediate) = intermediate {
                        ir[*only].as_assignment().is_some_and(|(left, right)| {
                            matches!(ir[right].kind, ExprKind::Constant { .. })
                                && Expr::equals(cx, left, intermediate)
                        })
                    } else {
                        matches!(ir[*only].kind, ExprKind::Exit { kind: ExitType::Return, value: Some(value), .. }
                            if matches!(ir[value].kind, ExprKind::Constant { .. }))
                    };
                    if !valid {
                        return None;
                    }
                }
                branch = if_.else_stat;
            }
        }
        Some(self)
    }

    pub(super) fn synthetic_dup(self, cx: &Cx) -> Option<SyntheticDup> {
        let ir = &cx.ir;
        let (head, selector) = switch_head(ir, self.target)?;
        let dup_block = match self.shape {
            Shape::NullableSplit { null_check, .. } => null_check,
            _ => self.target,
        };
        let dup_index = if matches!(self.shape, Shape::NullableSplit { .. }) {
            2
        } else {
            1
        };
        let list = ir[dup_block.get_basic_head(ir)].exprents?;
        let index = ir[list].len().checked_sub(dup_index)?;
        let (variable, replacement) = ir[ir[list][index]].as_assignment()?;
        let temp = Expr::variable(ir, variable)?;

        let selector = match &ir[selector].kind {
            ExprKind::Invocation(invoke) => invoke
                .instance
                .expect("String switch invocation has no receiver"),
            _ => selector,
        };
        let used = Expr::variable(ir, selector).expect("String switch selector is not a variable");
        if temp.pair() != used.pair()
            && Expr::is_var_referenced_in_stat(
                ir,
                variable,
                ir[self.first].parent.unwrap(),
                &[selector],
            )
        {
            let mut used_in_all_cases = true;
            for case in &switch(ir, self.first).cases {
                let StatementKind::If(branch) = ir[case.statement].kind else {
                    continue;
                };
                let condition = remove_condition_wrapper(ir, condition(ir, branch), false);
                if let ExprKind::Invocation(invoke) = &ir[condition].kind {
                    used_in_all_cases &= invoke
                        .instance
                        .and_then(|instance| Expr::variable(ir, instance))
                        .is_some_and(|instance| instance.pair() == temp.pair());
                }
            }
            if temp.pair() != used.pair() || !used_in_all_cases {
                return None;
            }
        }
        Some(SyntheticDup {
            head,
            list,
            index,
            variable,
            replacement,
        })
    }
}

#[derive(Clone, Copy)]
pub(super) struct SyntheticDup {
    pub head: ExprId,
    pub list: ExprListId,
    pub index: usize,
    pub variable: ExprId,
    pub replacement: ExprId,
}

fn equals_on(cx: &Cx, expr: ExprId, selector: Option<ExprId>, dup: Option<SyntheticDup>) -> bool {
    let ExprKind::Invocation(invoke) = &cx.ir[expr].kind else {
        return false;
    };
    if invoke.name != "equals" {
        return false;
    }
    let instance = invoke.instance.expect("String equals call has no receiver");
    selector.is_some_and(|value| Expr::equals(cx, instance, value))
        || dup.is_none_or(|dup| Expr::equals(cx, instance, dup.variable))
}

pub(super) fn remove_condition_wrapper(ir: &Ir, condition: ExprId, bool_not: bool) -> ExprId {
    match &ir[condition].kind {
        ExprKind::Function { op, operands, .. }
            if *op == FunctionType::Ne || bool_not && *op == FunctionType::BoolNot =>
        {
            operands[0]
        }
        _ => condition,
    }
}

fn regular_switch_successor(ir: &Ir, source: StatId) -> Option<StatId> {
    let edges = source.get_successor_edges(ir, EdgeType::Regular.mask());
    let [edge] = edges.as_slice() else {
        return None;
    };
    let target = ir[*edge].destination;
    matches!(ir[target].kind, StatementKind::Switch(_)).then_some(target)
}
