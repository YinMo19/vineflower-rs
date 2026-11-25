// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Expression-list rewrites from `SimplifyExprentsHelper`.

mod arrays;
mod constructors;
mod increments;

use crate::decompiler::exps::{ExitType, Expr, ExprKind, FunctionType, MonitorType, Variable};
use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::sforms::SsaResult;
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::engine::counter_container::CounterContainer;
use crate::structs::StructClass;

pub(super) fn simplify_list(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    list: ExprListId,
    ssa: Option<&SsaResult>,
    class: &StructClass,
    first_invocation: bool,
) -> bool {
    let mut changed = false;
    let mut index = 0;
    while let Some(&current) = cx.ir[list].get(index) {
        if let Some(replacement) = constructors::simple(&mut cx.ir, current)
            .or_else(|| constructors::lambda(cx, counters, current, class))
        {
            cx.ir[list][index] = replacement;
        } else if removable_monitor_exit(&cx.ir, current)
            || trivial_stack_assignment(&cx.ir, current)
        {
            cx.ir[list].remove(index);
        } else {
            let Some(&next) = cx.ir[list].get(index + 1) else {
                break;
            };

            if index > 0 && constructors::swap(&mut cx.ir, list, index, current, next) {
                cx.ir[list].remove(index - 1);
                cx.ir[list].remove(index);
            } else if assignment_return(cx, stat, list, current, next)
                || constructors::remote(cx, counters, list, index, current)
                || cx.options.remove_getclass
                    && constructors::qualified_new_get_class(cx, current, next)
            {
                cx.ir[list].remove(index);
            } else {
                let array_count = arrays::initializer(cx, counters, list, index, current);
                if array_count > 0 {
                    cx.ir[list].drain(index + 1..=index + array_count);
                } else if arrays::add_element(cx, counters, current, next) {
                    cx.ir[list].remove(index + 1);
                } else if let Some(replacement) = increments::prefix(cx, counters, current) {
                    cx.ir[list][index] = replacement;
                } else if increments::postfix(cx, current, next)
                    || increments::postfix_assignment(cx, counters, current, next)
                    || stack_assignment(cx, current, next)
                {
                    cx.ir[list].remove(index + 1);
                } else if ssa.is_some_and(|ssa| {
                    constructors::inline_method_reference_assignment(cx, ssa, class, current, next)
                }) {
                    cx.ir[list].remove(index);
                } else if !first_invocation && stack_assignment_two(cx, counters, current, next) {
                    cx.ir[list].remove(index + 1);
                } else if first_invocation && increments::inline_prefix(&mut cx.ir, current, next) {
                    cx.ir[list].remove(index);
                } else {
                    index += 1;
                    continue;
                }
            }
        }
        changed = true;
    }
    changed
}

pub(super) fn has_qualified_new_get_class(cx: &mut Cx, parent: StatId, child: StatId) -> bool {
    if !matches!(cx.ir[child].kind, StatementKind::BasicBlock { .. }) {
        return false;
    }
    let Some(list) = cx.ir[child].exprents else {
        return false;
    };
    let Some(&last) = cx.ir[list].last() else {
        return false;
    };
    let StatementKind::If(branch) = &cx.ir[parent].kind else {
        return false;
    };
    let Some(condition) = if_condition(&cx.ir, branch.head_exprents) else {
        return false;
    };
    if !constructors::qualified_new_get_class(cx, last, condition) {
        return false;
    }

    // ArrayList.remove(Object) starts with the first equal expression.
    let index = cx.ir[list]
        .iter()
        .position(|&expr| Expr::equals(cx, last, expr))
        .unwrap();
    cx.ir[list].remove(index);
    true
}

fn removable_monitor_exit(ir: &Ir, current: ExprId) -> bool {
    matches!(ir[current].kind, ExprKind::Monitor { kind: MonitorType::Exit, value, remove: true } if variable(ir, value).is_some_and(|var| !var.stack))
}

fn trivial_stack_assignment(ir: &Ir, current: ExprId) -> bool {
    let Some((left, right)) = ir[current].as_assignment() else {
        return false;
    };
    matches!((variable(ir, left), variable(ir, right)), (Some(left), Some(right)) if left.stack && left.index == right.index)
}

fn assignment_return(
    cx: &mut Cx,
    stat: StatId,
    list: ExprListId,
    current: ExprId,
    next: ExprId,
) -> bool {
    let ExprKind::Assignment {
        left,
        right,
        compound: None,
    } = cx.ir[current].kind
    else {
        return false;
    };
    let ExprKind::Exit {
        kind: ExitType::Return,
        value: Some(value),
        ..
    } = cx.ir[next].kind
    else {
        return false;
    };
    if variable(&cx.ir, left).is_none_or(|var| var.stack)
        || variable(&cx.ir, value).is_none()
        || !Expr::equals(cx, left, value)
    {
        return false;
    }
    if let Some(parent) = cx.ir[stat].parent
        && let StatementKind::If(branch) = &cx.ir[parent].kind
        && !branch.pattern_matched
        && matches!(
            cx.ir[right].kind,
            ExprKind::Function {
                op: FunctionType::Cast,
                ..
            }
        )
        && Expr::equals(cx, current, cx.ir[list][0])
        && let Some(condition) = if_condition(&cx.ir, branch.head_exprents)
    {
        let mut root = parent;
        while let Some(parent) = cx.ir[root].parent {
            root = parent;
        }
        if root
            .method(&cx.ir)
            .bytecode_version
            .has_if_pattern_matching()
            && Expr::all_exprents(&cx.ir, condition, true, true)
                .into_iter()
                .any(|expr| {
                    matches!(
                        cx.ir[expr].kind,
                        ExprKind::Function {
                            op: FunctionType::InstanceOf,
                            ..
                        }
                    )
                })
        {
            // Preserve folded casts for the later if-pattern matcher.
            return false;
        }
    }
    let ExprKind::Exit { value, .. } = &mut cx.ir[next].kind else {
        unreachable!()
    };
    *value = Some(right);
    true
}

fn if_condition(ir: &Ir, head: Option<ExprListId>) -> Option<ExprId> {
    let head = *ir[head?].first()?;
    match ir[head].kind {
        ExprKind::If { condition } => Some(condition),
        _ => None,
    }
}

fn stack_assignment(cx: &mut Cx, mut first: ExprId, second: ExprId) -> bool {
    let Some((target, rhs)) = cx.ir[second].as_assignment() else {
        return false;
    };
    while let Some((left, right)) = cx.ir[first].as_assignment() {
        if Expr::equals(cx, right, rhs)
            && is_stack_variable(&cx.ir, left)
            && !is_stack_variable(&cx.ir, target)
            && !Expr::contains(cx, target, left)
        {
            set_assignment_right(&mut cx.ir, first, second);
            return true;
        }
        first = right;
    }
    false
}

fn stack_assignment_two(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    first: ExprId,
    second: ExprId,
) -> bool {
    let (Some((left, right)), Some((target, rhs))) =
        (cx.ir[first].as_assignment(), cx.ir[second].as_assignment())
    else {
        return false;
    };
    if !is_stack_variable(&cx.ir, left)
        || is_stack_variable(&cx.ir, target)
        || !Expr::equals(cx, left, rhs)
    {
        return false;
    }
    let offsets = cx.ir[second].bytecode.clone();
    let combined = Expr::new(
        &mut cx.ir,
        counters,
        ExprKind::Assignment {
            left: target,
            right,
            compound: None,
        },
        offsets,
    );
    set_assignment_right(&mut cx.ir, first, combined);
    true
}

fn set_assignment_right(ir: &mut Ir, expr: ExprId, value: ExprId) {
    let ExprKind::Assignment { right, .. } = &mut ir[expr].kind else {
        unreachable!()
    };
    *right = value;
}

fn variable(ir: &Ir, expr: ExprId) -> Option<&Variable> {
    match &ir[expr].kind {
        ExprKind::Variable(var) => Some(var),
        _ => None,
    }
}

fn is_stack_variable(ir: &Ir, expr: ExprId) -> bool {
    variable(ir, expr).is_some_and(|var| var.stack)
}
