//! Expression order used by the statement and SSA passes.

use std::slice;

use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::stats::{LoopType, StatementKind};

use super::{Expr, ExprKind, FunctionType};

impl Expr {
    /// The immediate expressions in `Exprent.getAllExprents()` order.
    /// Aliased expressions are yielded at each position where they occur.
    pub fn children(ir: &Ir, expr: ExprId) -> impl Iterator<Item = ExprId> + '_ {
        let (first, second) = Self::child_slices(ir, expr);
        first.iter().chain(second).copied()
    }

    fn child_slices(ir: &Ir, expr: ExprId) -> (&[ExprId], &[ExprId]) {
        match &ir[expr].kind {
            ExprKind::Assert { condition, message } => (condition.as_slice(), message.as_slice()),
            ExprKind::Constant { .. } | ExprKind::Variable(_) | ExprKind::Switch { .. } => {
                (&[], &[])
            }
            ExprKind::Assignment { left, right, .. } => {
                (slice::from_ref(left), slice::from_ref(right))
            }
            ExprKind::Array { array, index, .. } => {
                (slice::from_ref(array), slice::from_ref(index))
            }
            ExprKind::Field(field) => (field.instance.as_slice(), &[]),
            ExprKind::Invocation(invoke) => (invoke.instance.as_slice(), &invoke.parameters),
            ExprKind::Function { operands, .. } => (operands, &[]),
            ExprKind::Pattern(pattern) => (&pattern.children, &[]),
            ExprKind::New {
                new_type,
                dimensions,
                array_elements,
                ..
            } if new_type.array_dim != 0 => (dimensions, array_elements),
            ExprKind::New {
                constructor: Some(constructor),
                ..
            } => {
                // An object allocation exposes the constructor's receiver and arguments.
                let ExprKind::Invocation(invoke) = &ir[*constructor].kind else {
                    unreachable!("NewExprent constructor must be an invocation");
                };
                (invoke.instance.as_slice(), &invoke.parameters)
            }
            ExprKind::New {
                constructor: None, ..
            } => (&[], &[]),
            ExprKind::Exit { value, .. } => (value.as_slice(), &[]),
            ExprKind::Monitor { value, .. }
            | ExprKind::SwitchHead { value, .. }
            | ExprKind::Yield { value, .. } => (slice::from_ref(value), &[]),
            ExprKind::If { condition } => (slice::from_ref(condition), &[]),
        }
    }

    /// `Exprent.getAllExprents(recursive, self)`.
    pub fn all_exprents(ir: &Ir, expr: ExprId, recursive: bool, include_self: bool) -> Vec<ExprId> {
        let mut result = Vec::new();
        Self::append_exprents(ir, expr, recursive, &mut result);
        if include_self {
            result.push(expr);
        }
        result
    }

    /// Appends the direct children first, then visits their descendants in
    /// reverse child order, as in `Exprent.getAllExprents`.
    pub(crate) fn append_exprents(ir: &Ir, expr: ExprId, recursive: bool, out: &mut Vec<ExprId>) {
        let start = out.len();
        let (first, second) = Self::child_slices(ir, expr);
        out.reserve(first.len() + second.len());
        out.extend_from_slice(first);
        out.extend_from_slice(second);
        if recursive {
            for index in (start..out.len()).rev() {
                Self::append_exprents(ir, out[index], true, out);
            }
        }
    }

    /// The variables defined by a binding, in component order.
    pub fn pattern_vars(ir: &Ir, pattern: ExprId) -> Vec<ExprId> {
        let mut variables = Vec::new();
        Self::append_pattern_vars(ir, pattern, &mut variables);
        variables
    }

    fn append_pattern_vars(ir: &Ir, expr: ExprId, variables: &mut Vec<ExprId>) {
        match &ir[expr].kind {
            ExprKind::Variable(_) => variables.push(expr),
            ExprKind::Pattern(pattern) => {
                for &child in &pattern.children {
                    Self::append_pattern_vars(ir, child, variables);
                }
            }
            _ => panic!("Illegal input in PatternExprent"),
        }
    }
}

impl StatId {
    /// All expression occurrences in Java StatementIterator order, including
    /// declarations. Aliases appear at each live position.
    pub(crate) fn all_exprents(self, ir: &Ir) -> Vec<ExprId> {
        fn append(ir: &Ir, stat: StatId, expressions: &mut Vec<ExprId>) {
            fn extend(
                ir: &Ir,
                ids: impl IntoIterator<Item = ExprId>,
                expressions: &mut Vec<ExprId>,
            ) {
                for expr in ids {
                    Expr::append_exprents(ir, expr, true, expressions);
                    expressions.push(expr);
                }
            }
            extend(ir, ir[stat].var_definitions.iter().copied(), expressions);
            if let Some(body) = ir[stat].exprents {
                extend(ir, ir[body].iter().copied(), expressions);
            } else {
                for &child in &ir[stat].stats {
                    append(ir, child, expressions);
                }
                extend(ir, stat.stat_exprents(ir), expressions);
            }
        }

        let mut result = Vec::new();
        append(ir, self, &mut result);
        result
    }

    /// `Statement.getImplicitlyDefinedVars`, in declaration and expression order.
    pub(crate) fn implicitly_defined_vars(self, ir: &Ir) -> Vec<ExprId> {
        match &ir[self].kind {
            StatementKind::BasicBlock { .. } => pattern_vars_in(
                ir,
                ir[self]
                    .exprents
                    .into_iter()
                    .flat_map(|list| ir[list].iter().copied()),
            ),
            StatementKind::If(branch) => {
                let head = ir[branch.head_exprents.expect("Missing if header")][0];
                let ExprKind::If { condition } = ir[head].kind else {
                    unreachable!("If header must be an IfExprent");
                };
                pattern_vars_in(ir, [condition])
            }
            StatementKind::Do(header) => {
                let expr = if header.ty == LoopType::ForEach {
                    Some(header.increment(ir).expect("Foreach iterable is missing"))
                } else {
                    header.condition(ir)
                };
                pattern_vars_in(ir, expr)
            }
            StatementKind::Switch(switch) => pattern_vars_in(
                ir,
                switch
                    .case_values()
                    .flatten()
                    .flatten()
                    .chain(switch.case_guards.iter().flatten())
                    .copied(),
            ),
            StatementKind::Catch {
                vars, resources, ..
            } => vars
                .iter()
                .copied()
                .chain(
                    resources
                        .iter()
                        .flat_map(|&list| &ir[list])
                        .filter_map(|&expr| match ir[expr].kind {
                            ExprKind::Assignment { left, .. } => Some(left),
                            _ => None,
                        }),
                )
                .collect(),
            StatementKind::CatchAll { vars, .. } => vars.clone(),
            _ => Vec::new(),
        }
    }

    /// `Statement.getStatExprents`, including compound statement headers and
    /// catch resources. A statement's body is held separately in `exprents`.
    pub fn stat_exprents(self, ir: &Ir) -> Vec<ExprId> {
        let list = |id: Option<ExprListId>| id.map_or(&[][..], |id| ir[id].as_slice());
        match &ir[self].kind {
            StatementKind::Do(loop_stat) => match loop_stat.ty {
                LoopType::Infinite => Vec::new(),
                LoopType::While | LoopType::DoWhile => {
                    vec![loop_stat.condition(ir).expect("Loop condition is missing")]
                }
                LoopType::For => loop_stat
                    .init(ir)
                    .into_iter()
                    .chain([
                        loop_stat.condition(ir).expect("Loop condition is missing"),
                        loop_stat.increment(ir).expect("Loop increment is missing"),
                    ])
                    .collect(),
                LoopType::ForEach => vec![
                    loop_stat.init(ir).expect("Foreach variable is missing"),
                    loop_stat
                        .increment(ir)
                        .expect("Foreach iterable is missing"),
                ],
            },
            StatementKind::If(branch) => list(branch.head_exprents).to_vec(),
            StatementKind::Synchronized { head_exprents, .. } => list(*head_exprents).to_vec(),
            StatementKind::Catch {
                resources, vars, ..
            } => list(*resources).iter().chain(vars).copied().collect(),
            StatementKind::Switch(switch) => list(switch.head_exprents)
                .iter()
                .copied()
                .chain(switch.case_guards.iter().flatten().copied())
                .chain(switch.case_values().flatten().flatten().copied())
                .collect(),
            _ => Vec::new(),
        }
    }
}

fn pattern_vars_in(ir: &Ir, expressions: impl IntoIterator<Item = ExprId>) -> Vec<ExprId> {
    let mut variables = Vec::new();
    let mut descendants = Vec::new();
    for expr in expressions {
        Expr::append_exprents(ir, expr, true, &mut descendants);
        descendants.push(expr);
        for child in descendants.drain(..) {
            if let ExprKind::Function {
                op: FunctionType::InstanceOf,
                operands,
                ..
            } = &ir[child].kind
                && let Some(&binding) = operands.get(2)
            {
                Expr::append_pattern_vars(ir, binding, &mut variables);
            }
        }
    }
    variables
}

impl StatId {
    /// Statement.replaceExprent only replaces a header owned by its statement.
    /// A switch searches guards by expression equality after checking its head.
    pub(crate) fn replace_header(self, cx: &mut crate::engine::Cx, old: ExprId, new: ExprId) {
        let slots = match &cx.ir[self].kind {
            StatementKind::Do(header) => [header.init, header.condition, header.increment],
            StatementKind::If(branch) => [branch.head_exprents, None, None],
            StatementKind::Synchronized { head_exprents, .. } => [*head_exprents, None, None],
            StatementKind::Switch(switch) => {
                if switch
                    .head_exprents
                    .is_none_or(|slot| cx.ir[slot].first() != Some(&old))
                {
                    let index = switch
                        .case_guards
                        .iter()
                        .position(|guard| guard.is_some_and(|expr| Expr::equals(cx, old, expr)));
                    if let Some(index) = index
                        && let StatementKind::Switch(switch) = &mut cx.ir[self].kind
                    {
                        switch.case_guards[index] = Some(new);
                    }
                    return;
                }
                [switch.head_exprents, None, None]
            }
            _ => return,
        };
        for slot in slots.into_iter().flatten() {
            if cx.ir[slot].first() == Some(&old) {
                cx.ir[slot][0] = new;
            }
        }
    }
}
