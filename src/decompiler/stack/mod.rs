// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! StackVarsProcessor and its interleaved statement and expression rewrites.

mod conditionals;
mod effectively_final;
mod inline;
mod simplify_list;

use std::io;

use rustc_hash::FxHashSet;

use crate::decompiler::decompose::{finish::condense_sequences, if_helper::merge_ifs};
use crate::decompiler::ir::StatId;
use crate::decompiler::sforms::{SsaResult, reset_versions, split_ssa, split_ssau};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructClass;

#[derive(Default)]
pub struct StackSimplifyOptions {
    pub inline_regular_vars: bool,
}

/// Alternate local rewrites with SSAU substitution until neither changes the
/// tree. The final SSAU pass removes assignments made redundant in the last round.
pub fn simplify_stack_vars(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
    options: &StackSimplifyOptions,
) {
    let method = std::sync::Arc::clone(root.method(&cx.ir));
    let mut reordered = FxHashSet::default();
    let mut first = true;
    loop {
        let ssa = split_ssa(&mut cx.ir, root, &method);
        let mut changed = false;
        while simplify_statement(cx, counters, root, &mut reordered, &ssa, class, first) {
            changed = true;
        }
        reset_versions(&mut cx.ir, root);
        condense_sequences(cx, counters, root);
        let mut ssau = split_ssau(&mut cx.ir, root, &method);
        if first {
            effectively_final::mark(cx, root, &ssau.versions);
            first = false;
        }
        changed |= inline::iterate_statements(cx, counters, root, &mut ssau, options);
        reset_versions(&mut cx.ir, root);
        if !changed {
            break;
        }
    }
    let mut ssau = split_ssau(&mut cx.ir, root, &method);
    inline::iterate_statements(cx, counters, root, &mut ssau, options);
    reset_versions(&mut cx.ir, root);
}

/// One `SimplifyExprentsHelper.simplifyStackVarsStatement` traversal. A
/// successful rewrite of a child restarts its parent's search at the first child.
pub fn simplify_statement(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    reordered: &mut FxHashSet<i32>,
    ssa: &SsaResult,
    class: &StructClass,
    first: bool,
) -> bool {
    simplify_statement_with_optional_ssa(cx, counters, stat, reordered, Some(ssa), class, first)
        .expect("SSA is available to simplify stack variables")
}

pub(crate) fn simplify_statement_without_ssa(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    reordered: &mut FxHashSet<i32>,
    class: &StructClass,
) -> io::Result<bool> {
    simplify_statement_with_optional_ssa(cx, counters, stat, reordered, None, class, false)
}

fn simplify_statement_with_optional_ssa(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    reordered: &mut FxHashSet<i32>,
    ssa: Option<&SsaResult>,
    class: &StructClass,
    first: bool,
) -> io::Result<bool> {
    if let Some(list) = cx.ir[stat].exprents {
        return Ok(simplify_list::simplify_list(
            cx, counters, stat, list, ssa, class, first,
        ));
    }
    let mut found = false;
    loop {
        let mut changed = false;
        for i in 0..cx.ir[stat].stats.len() {
            let child = cx.ir[stat].stats[i];
            found |= simplify_statement_with_optional_ssa(
                cx, counters, child, reordered, ssa, class, first,
            )?;
            changed = merge_ifs(cx, counters, child, reordered, class)
                || conditionals::build_iff(cx, counters, child, ssa)?
                || cx.options.decompile_java4
                    && conditionals::collapse_class_literal(cx, counters, child, class);
            if changed {
                break;
            }
            if let Some(&head) = cx.ir[child].stats.first()
                && simplify_list::has_qualified_new_get_class(cx, child, head)
            {
                break;
            }
        }
        if !changed {
            return Ok(found);
        }
        found = true;
    }
}
