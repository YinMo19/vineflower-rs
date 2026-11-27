//! Equality, use flags, and child replacement of expression objects.

use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::{Cx, counter_container::CounterContainer};

use super::{Expr, ExprKind, FunctionType, Variable};

impl Expr {
    pub(crate) fn as_assignment(&self) -> Option<(ExprId, ExprId)> {
        match self.kind {
            ExprKind::Assignment { left, right, .. } => Some((left, right)),
            _ => None,
        }
    }

    /// IfExprent.negateIf retains the wrapper and the condition's bytecode positions.
    pub(crate) fn negate_if(ir: &mut Ir, counters: &mut CounterContainer, head: ExprId) {
        let ExprKind::If { condition } = ir[head].kind else {
            unreachable!("Conditional header must be an IfExprent");
        };
        let offsets = ir[condition].bytecode.clone();
        let condition = Self::function(
            ir,
            counters,
            FunctionType::BoolNot,
            vec![condition],
            offsets,
        );
        ir[head].kind = ExprKind::If { condition };
    }

    pub const MULTIPLE_USES: u8 = 1;
    pub const SIDE_EFFECTS_FREE: u8 = 2;

    pub(crate) fn variable(ir: &Ir, expr: ExprId) -> Option<&Variable> {
        match &ir[expr].kind {
            ExprKind::Variable(var) => Some(var),
            _ => None,
        }
    }

    /// `MergeHelper.containsVar` compares the index irrespective of SSA version.
    pub(crate) fn contains_var_index(ir: &Ir, tree: ExprId, index: i32) -> bool {
        any_variable(ir, tree, &|_, var| var.index == index)
    }

    /// `Exprent.containsVar` matches both the index and SSA version.
    pub(crate) fn contains_var(ir: &Ir, tree: ExprId, pair: VarVersionPair) -> bool {
        any_variable(ir, tree, &|_, var| var.pair() == pair)
    }

    /// `VarExprent.isVarReferenced(Exprent, ...)`. Exceptions use expression
    /// identity, whereas other references are matched by index and version.
    pub(crate) fn is_var_referenced(
        ir: &Ir,
        var: ExprId,
        tree: ExprId,
        whitelist: &[ExprId],
    ) -> bool {
        let pair = Self::variable(ir, var)
            .expect("Expected a variable expression")
            .pair();
        any_variable(ir, tree, &|expr, other| {
            expr != var && !whitelist.contains(&expr) && other.pair() == pair
        })
    }

    /// `VarExprent.isVarReferenced(Statement, ...)`.
    pub(crate) fn is_var_referenced_in_stat(
        ir: &Ir,
        var: ExprId,
        stat: StatId,
        whitelist: &[ExprId],
    ) -> bool {
        let referenced = |expr| Self::is_var_referenced(ir, var, expr, whitelist);
        if let Some(list) = ir[stat].exprents {
            return ir[list].iter().copied().any(referenced);
        }

        ir[stat]
            .stats
            .iter()
            .any(|&child| Self::is_var_referenced_in_stat(ir, var, child, whitelist))
            || stat.stat_exprents(ir).into_iter().any(referenced)
    }

    /// Java `Exprent.equals`, including each subclass's semantic fields.
    pub fn equals(cx: &Cx, left: ExprId, right: ExprId) -> bool {
        if left == right {
            return true;
        }
        let eq = |left, right| Self::equals(cx, left, right);
        match (&cx.ir[left].kind, &cx.ir[right].kind) {
            (
                ExprKind::Constant {
                    value: a_val,
                    var_type: a_ty,
                    ..
                },
                ExprKind::Constant {
                    value: b_val,
                    var_type: b_ty,
                    ..
                },
            ) => a_ty == b_ty && a_val == b_val,
            (ExprKind::Variable(a), ExprKind::Variable(b)) => {
                a.index == b.index && a.version == b.version && a.expr_type(cx) == b.expr_type(cx)
            }
            (
                ExprKind::Assignment {
                    left: a_left,
                    right: a_right,
                    compound: a_op,
                },
                ExprKind::Assignment {
                    left: b_left,
                    right: b_right,
                    compound: b_op,
                },
            ) => eq(*a_left, *b_left) && eq(*a_right, *b_right) && a_op == b_op,
            (
                ExprKind::Array {
                    array: a_array,
                    index: a_index,
                    ..
                },
                ExprKind::Array {
                    array: b_array,
                    index: b_index,
                    ..
                },
            ) => eq(*a_array, *b_array) && eq(*a_index, *b_index),
            (ExprKind::Field(a), ExprKind::Field(b)) => {
                a.name == b.name
                    && a.classname == b.classname
                    && a.is_static() == b.is_static()
                    && equal_optional(cx, a.instance, b.instance)
                    && a.descriptor == b.descriptor
            }
            (ExprKind::Invocation(a), ExprKind::Invocation(b)) => {
                a.name == b.name
                    && a.classname == b.classname
                    && a.is_static == b.is_static
                    && equal_optional(cx, a.instance, b.instance)
                    && a.descriptor == b.descriptor
                    && a.function == b.function
                    && equal_lists(cx, &a.parameters, &b.parameters)
            }
            (
                ExprKind::Function {
                    op: a_op,
                    operands: a_operands,
                    ..
                },
                ExprKind::Function {
                    op: b_op,
                    operands: b_operands,
                    ..
                },
            ) => a_op == b_op && equal_lists(cx, a_operands, b_operands),
            (
                ExprKind::New {
                    new_type: a_ty,
                    dimensions: a_dims,
                    constructor: a_ctor,
                    array_elements: a_elements,
                    direct_array_init: a_direct,
                    ..
                },
                ExprKind::New {
                    new_type: b_ty,
                    dimensions: b_dims,
                    constructor: b_ctor,
                    array_elements: b_elements,
                    direct_array_init: b_direct,
                    ..
                },
            ) => {
                a_ty == b_ty
                    && equal_lists(cx, a_dims, b_dims)
                    && equal_optional(cx, *a_ctor, *b_ctor)
                    && a_direct == b_direct
                    && equal_lists(cx, a_elements, b_elements)
            }
            (
                ExprKind::Exit {
                    kind: a_kind,
                    value: a_val,
                    ..
                },
                ExprKind::Exit {
                    kind: b_kind,
                    value: b_val,
                    ..
                },
            ) => a_kind == b_kind && equal_optional(cx, *a_val, *b_val),
            (
                ExprKind::Monitor {
                    kind: a_kind,
                    value: a_val,
                    ..
                },
                ExprKind::Monitor {
                    kind: b_kind,
                    value: b_val,
                    ..
                },
            ) => a_kind == b_kind && eq(*a_val, *b_val),
            (ExprKind::If { condition: a }, ExprKind::If { condition: b })
            | (ExprKind::SwitchHead { value: a, .. }, ExprKind::SwitchHead { value: b, .. }) => {
                eq(*a, *b)
            }
            // Patterns, switch expressions and yields use expression identity.
            _ => false,
        }
    }

    /// `Exprent.containsExprent` tests structural equality over the tree and its root.
    pub fn contains(cx: &Cx, tree: ExprId, needle: ExprId) -> bool {
        Self::all_exprents(&cx.ir, tree, true, true)
            .into_iter()
            .any(|expr| Self::equals(cx, expr, needle))
    }

    /// Replace direct references equal by identity to `old`, as `replaceExprent` does.
    pub fn replace(ir: &mut Ir, parent: ExprId, old: ExprId, new: ExprId) {
        let replace = |slot: &mut ExprId| {
            if *slot == old {
                *slot = new;
            }
        };
        let replace_optional = |slot: &mut Option<ExprId>| {
            if let Some(id) = slot {
                replace(id);
            }
        };
        match &mut ir[parent].kind {
            ExprKind::Assert { condition, message } => {
                replace_optional(condition);
                replace_optional(message);
            }
            // PatternExprent exposes its children for traversal and uses
            // Exprent's default replaceExprent implementation.
            ExprKind::Constant { .. } | ExprKind::Variable(_) | ExprKind::Pattern(_) => {}
            ExprKind::Switch { .. } => {}
            ExprKind::Assignment { left, right, .. } => {
                replace(left);
                replace(right);
            }
            ExprKind::Array { array, index, .. } => {
                replace(array);
                replace(index);
            }
            ExprKind::Field(field) => replace_optional(&mut field.instance),
            ExprKind::Invocation(invocation) => {
                replace_optional(&mut invocation.instance);
                invocation.parameters.iter_mut().for_each(replace);
            }
            ExprKind::Function { operands, .. } => operands.iter_mut().for_each(replace),
            ExprKind::New { constructor, .. } => {
                if let Some(ctor) = *constructor {
                    let ctor = if ctor == old { new } else { ctor };
                    assert!(
                        matches!(ir[ctor].kind, ExprKind::Invocation(_)),
                        "New expression constructor must be an invocation"
                    );
                    let ExprKind::New { constructor, .. } = &mut ir[parent].kind else {
                        unreachable!()
                    };
                    *constructor = Some(ctor);
                    Self::replace(ir, ctor, old, new);
                }
                let ExprKind::New {
                    dimensions,
                    array_elements,
                    ..
                } = &mut ir[parent].kind
                else {
                    unreachable!()
                };
                dimensions.iter_mut().for_each(replace);
                array_elements.iter_mut().for_each(replace);
            }
            ExprKind::Exit { value, .. } => replace_optional(value),
            ExprKind::Monitor { value, .. }
            | ExprKind::SwitchHead { value, .. }
            | ExprKind::Yield { value, .. } => replace(value),
            ExprKind::If { condition } => replace(condition),
        }
    }

    /// `Exprent.getExprentUse`.
    pub fn usage(ir: &Ir, id: ExprId) -> u8 {
        const BOTH: u8 = Expr::MULTIPLE_USES | Expr::SIDE_EFFECTS_FREE;
        match &ir[id].kind {
            ExprKind::Constant { .. } | ExprKind::Variable(_) => BOTH,
            ExprKind::Array { array, index, .. } => {
                Self::usage(ir, *array) & Self::usage(ir, *index) & Self::MULTIPLE_USES
            }
            ExprKind::Field(field) => field.instance.map_or(Self::MULTIPLE_USES, |instance| {
                Self::usage(ir, instance) & Self::MULTIPLE_USES
            }),
            ExprKind::Function { op, operands, .. } if !op.is_inc_dec() => operands
                .iter()
                .fold(BOTH, |usage, &expr| usage & Self::usage(ir, expr)),
            _ => 0,
        }
    }
}

fn any_variable(ir: &Ir, tree: ExprId, matches: &impl Fn(ExprId, &Variable) -> bool) -> bool {
    Expr::variable(ir, tree).is_some_and(|var| matches(tree, var))
        || Expr::children(ir, tree).any(|child| any_variable(ir, child, matches))
}

fn equal_optional(cx: &Cx, left: Option<ExprId>, right: Option<ExprId>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => Expr::equals(cx, left, right),
        (None, None) => true,
        _ => false,
    }
}

fn equal_lists(cx: &Cx, left: &[ExprId], right: &[ExprId]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(&left, &right)| Expr::equals(cx, left, right))
}
