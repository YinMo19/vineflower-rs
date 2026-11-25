// SPDX-License-Identifier: Apache-2.0

//! Combine nested reference casts using bounds from their uses.

use std::io;

use crate::code::code_constants::{ACC_ENUM, ACC_INTERFACE, INIT_NAME};
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, FunctionType, Invocation};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructMember;
use crate::types::{CodeType, TypeFamily, VarType};
use crate::util::jhash::JHashSet;

pub(crate) fn make_casts(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    let cx = &mut *cx.enter_method(counters);
    // This pass mutates operands but never replaces a top-level expression.
    // Reuse this order when searching the same method for uses of an assigned local.
    let mut roots = Vec::new();
    collect_roots(&cx.ir, root, &mut roots);
    let mut changed = false;
    for &expr in &roots {
        changed |= rewrite(cx, counters, &roots, expr)?;
    }
    Ok(changed)
}

fn collect_roots(ir: &Ir, stat: StatId, roots: &mut Vec<ExprId>) {
    for &child in &ir[stat].stats {
        collect_roots(ir, child, roots);
    }
    if let Some(list) = ir[stat].exprents {
        roots.extend_from_slice(&ir[list]);
    } else {
        roots.extend(stat.stat_exprents(ir));
    }
}

fn rewrite(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    roots: &[ExprId],
    expr: ExprId,
) -> io::Result<bool> {
    match &cx.ir[expr].kind {
        ExprKind::Invocation(invocation) => {
            let count = invocation.parameters.len();
            let mut changed = false;
            for index in 0..count {
                let ExprKind::Invocation(invocation) = &cx.ir[expr].kind else {
                    unreachable!()
                };
                let cast = invocation.parameters[index];
                if let Some(mut chain) = CastChain::read(cx, cast) {
                    let missing: Vec<_> = parameter_bounds(cx, expr, index)?
                        .into_iter()
                        .filter(|bound| !chain.covers(cx, bound))
                        .collect();
                    if !missing.is_empty()
                        && missing.iter().all(|bound| chain.inner_satisfies(cx, bound))
                    {
                        chain.add_inner_type(cx, counters);
                    }
                    changed |= chain.replace(cx, cast);
                }
            }
            if changed {
                return Ok(true);
            }
        }
        ExprKind::Assignment { left, right, .. } => {
            let (var, cast) = (*left, *right);
            if let Some(pair) = Expr::variable(&cx.ir, var).map(|var| var.pair())
                && let Some(mut chain) = CastChain::read(cx, cast)
            {
                let mut bounds = JHashSet::new();
                for &root in roots {
                    collect_bounds(cx, root, pair, &mut bounds)?;
                }
                // Upstream collects the uncovered bounds into a second HashSet
                // before its short-circuiting hierarchy queries on the source type.
                let mut missing = JHashSet::new();
                missing.extend(
                    bounds
                        .iter()
                        .filter(|bound| !chain.covers(cx, bound))
                        .cloned(),
                );
                if missing.iter().any(|bound| chain.inner_satisfies(cx, bound)) {
                    chain.add_inner_type(cx, counters);
                }
                if chain.replace(cx, cast) {
                    let ExprKind::Variable(var) = &mut cx.ir[var].kind else {
                        unreachable!()
                    };
                    var.intersection_type = true;
                    return Ok(true);
                }
            }
        }
        _ => {}
    }
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    let mut changed = false;
    for child in children {
        changed |= rewrite(cx, counters, roots, child)?;
    }
    Ok(changed)
}

struct CastChain {
    inner: ExprId,
    types: Vec<ExprId>,
}

impl CastChain {
    fn read(cx: &Cx, mut expr: ExprId) -> Option<Self> {
        let mut types = Vec::new();
        while let ExprKind::Function {
            op: FunctionType::Cast,
            operands,
            ..
        } = &cx.ir[expr].kind
        {
            let &[inner, target] = operands.as_slice() else {
                break;
            };
            let ty = Expr::expr_type(cx, target);
            if ty.type_family != TypeFamily::Object || ty.array_dim != 0 {
                break;
            }
            types.push(target);
            expr = inner;
        }
        (!types.is_empty()).then_some(Self { inner: expr, types })
    }

    fn covers(&self, cx: &Cx, bound: &VarType) -> bool {
        self.types.iter().any(|&ty| satisfies(cx, ty, bound))
    }

    fn inner_satisfies(&self, cx: &Cx, bound: &VarType) -> bool {
        satisfies(cx, self.inner, bound)
    }

    fn add_inner_type(&mut self, cx: &mut Cx, counters: &mut CounterContainer) {
        let ty = Expr::expr_type(cx, self.inner);
        self.types.push(Expr::new(
            &mut cx.ir,
            counters,
            Expr::constant(ty, ConstantValue::Null, false),
            None,
        ));
    }

    fn replace(mut self, cx: &mut Cx, cast: ExprId) -> bool {
        if self.types.len() < 2 {
            return false;
        }
        let mut concrete = None;
        for &ty in &self.types {
            if Expr::expr_type(cx, ty)
                .value
                .as_deref()
                .and_then(|name| cx.classes().get_class(name))
                .is_some_and(|class| !class.has_modifier(ACC_INTERFACE))
            {
                if concrete.is_some() {
                    return false;
                }
                concrete = Some(ty);
            }
        }
        if let Some(class) = concrete {
            let index = self
                .types
                .iter()
                .position(|&ty| Expr::equals(cx, class, ty))
                .unwrap();
            self.types.remove(index);
            self.types.insert(0, class);
        }
        let ExprKind::Function { operands, .. } = &mut cx.ir[cast].kind else {
            unreachable!()
        };
        operands.clear();
        operands.push(self.inner);
        operands.extend(self.types);
        true
    }
}

fn satisfies(cx: &Cx, expr: ExprId, bound: &VarType) -> bool {
    let ty = Expr::expr_type(cx, expr);
    ty.value
        .as_deref()
        .zip(bound.value.as_deref())
        .is_some_and(|(class, parent)| cx.classes().instance_of(class, parent))
}

fn collect_bounds(
    cx: &mut Cx,
    expr: ExprId,
    var: VarVersionPair,
    bounds: &mut JHashSet<VarType>,
) -> io::Result<()> {
    let matches_var = |ir, expr| Expr::variable(ir, expr).is_some_and(|other| var == other.pair());
    match &cx.ir[expr].kind {
        ExprKind::Invocation(invocation) => {
            let positions: Vec<_> = invocation
                .parameters
                .iter()
                .enumerate()
                .filter_map(|(index, &param)| matches_var(&cx.ir, param).then_some(index))
                .collect();
            for index in positions {
                bounds.extend(parameter_bounds(cx, expr, index)?);
            }
        }
        ExprKind::Function {
            op: FunctionType::Cast,
            operands,
            ..
        } => {
            if let &[source, target] = operands.as_slice()
                && matches_var(&cx.ir, source)
            {
                bounds.insert(Expr::expr_type(cx, target));
            }
        }
        _ => {}
    }
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for child in children {
        collect_bounds(cx, child, var, bounds)?;
    }
    Ok(())
}

fn parameter_bounds(cx: &mut Cx, expr: ExprId, index: usize) -> io::Result<Vec<VarType>> {
    let method = Invocation::resolve_description(cx, expr);
    let Some(method) = method else {
        return Ok(Vec::new());
    };
    let Some(signature) = method.signature() else {
        return Ok(Vec::new());
    };
    let class = cx
        .classes()
        .get_class(&method.class_qualified_name)
        .ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "Missing generic method owner")
        })?;
    let offset = if class.has_modifier(ACC_ENUM) && method.name == INIT_NAME {
        2
    } else {
        0
    };
    let ty = index
        .checked_sub(offset)
        .and_then(|i| signature.parameter_types.get(i))
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Parameter missing from generic method signature",
            )
        })?;
    if ty.ty != CodeType::Genvar {
        return Ok(Vec::new());
    }
    Ok(signature
        .type_parameters
        .iter()
        .position(|name| Some(name.as_str()) == ty.value.as_deref())
        .map(|i| signature.type_parameter_bounds[i].clone())
        .unwrap_or_default())
}
