//! Local slot reassignment used by the finally pass.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::code::instruction::Instruction;
use crate::decompiler::exps::{Expr, ExprKind, STACK_BASE};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::counter_container::{CounterContainer, VAR_COUNTER};

use super::{Ssa, variable};

/// Instruction identities and their reassigned local indices. The retained
/// Arcs keep each allocation alive for as long as its rewrite is addressable.
#[derive(Default)]
pub struct InstructionRewrites {
    entries: FxHashMap<usize, (Arc<Instruction>, i32)>,
}

impl InstructionRewrites {
    pub fn get(&self, instruction: &Arc<Instruction>) -> Option<i32> {
        self.entries
            .get(&Arc::as_ptr(instruction).addr())
            .map(|(_, index)| *index)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Arc<Instruction>, i32)> + '_ {
        self.entries
            .values()
            .map(|(instruction, index)| (instruction, *index))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn insert(&mut self, instruction: &Arc<Instruction>, index: i32) {
        self.entries.insert(
            Arc::as_ptr(instruction).addr(),
            (Arc::clone(instruction), index),
        );
    }
}

/// `SimpleSSAReassign.reassignSSAForm`.
pub fn reassign_ssa(
    ir: &mut Ir,
    root: StatId,
    ssa: &Ssa,
    counters: &CounterContainer,
) -> InstructionRewrites {
    let versions = ssa.simple_reverse_phi_lookup();
    let variables = all_variables(ir, root);
    let locals: FxHashSet<_> = variables
        .iter()
        .copied()
        .map(|expr| variable(ir, expr).var)
        .filter(|&index| index < STACK_BASE)
        .collect();
    let mut rewrites = InstructionRewrites::default();
    if locals.is_empty() {
        return rewrites;
    }

    let mut counter = counters.get_counter(VAR_COUNTER);
    let mut new_indices = FxHashMap::default();
    for &expr in &variables {
        let pair = variable(ir, expr);
        let version = versions.get(&pair).copied().unwrap_or(pair.version);
        if version > 1 && locals.contains(&pair.var) {
            let base = VarVersionPair::new(pair.var, version);
            let new_index = *new_indices.entry(base).or_insert_with(|| {
                counter = counter.wrapping_add(1);
                counter
            });
            if base != pair {
                new_indices.insert(pair, new_index);
            }
        }
    }

    for expr in variables {
        let ExprKind::Variable(var) = &mut ir[expr].kind else {
            unreachable!()
        };
        if let Some(&index) = new_indices.get(&VarVersionPair::new(var.index, var.version)) {
            var.index = index;
            var.version = 1;
            if let Some(instruction) = &var.backing_instruction {
                rewrites.insert(instruction, index);
            }
        }
    }
    rewrites
}

/// `StackVarsProcessor.setVersionsToNull`.
pub fn reset_versions(ir: &mut Ir, root: StatId) {
    for expr in all_variables(ir, root) {
        let ExprKind::Variable(var) = &mut ir[expr].kind else {
            unreachable!()
        };
        var.version = 0;
    }
}

fn all_variables(ir: &Ir, root: StatId) -> Vec<ExprId> {
    let mut variables = Vec::new();
    collect_variables(ir, root, &mut Vec::new(), &mut variables);
    variables
}

fn collect_variables(
    ir: &Ir,
    stat: StatId,
    scratch: &mut Vec<ExprId>,
    variables: &mut Vec<ExprId>,
) {
    if let Some(body) = ir[stat].exprents {
        for &expr in &ir[body] {
            collect_expression_variables(ir, expr, scratch, variables);
        }
    } else {
        for &child in ir[stat].stats.iter() {
            collect_variables(ir, child, scratch, variables);
        }
        for expr in stat.stat_exprents(ir) {
            collect_expression_variables(ir, expr, scratch, variables);
        }
    }
}

fn collect_expression_variables(
    ir: &Ir,
    expr: ExprId,
    scratch: &mut Vec<ExprId>,
    variables: &mut Vec<ExprId>,
) {
    Expr::append_exprents(ir, expr, true, scratch);
    scratch.push(expr);
    variables.extend(
        scratch
            .drain(..)
            .filter(|&child| matches!(ir[child].kind, ExprKind::Variable(_))),
    );
}
