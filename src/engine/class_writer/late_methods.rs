// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use crate::decompiler::{
    exps::ExprKind,
    ir::{Ir, StatId},
    stats::{Statement, StatementKind, stat_edge::EdgeType},
    switches,
};
use crate::engine::{
    Cx,
    class_nodes::ClassNodeId,
    class_wrapper::{MethodSlot, catch_method_failure},
    counter_container::CounterContainer,
};
use std::{io, sync::Arc};

/// ClassWriter resets the current method for every wrapper, even when a
/// native or failed method has no statement tree.
pub(super) fn reset_method(cx: &mut Cx, slot: MethodSlot) {
    let method = slot.get(cx);
    let ids = method.counters.expressions.clone();
    cx.current_method = Some((Arc::clone(&method.method), method.variables));
    cx.expression_ids = ids;
}

pub(super) fn process(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    for index in 0..cx.class_nodes[node].class.methods.len() {
        let slot = MethodSlot { node, index };
        reset_method(cx, slot);
        let method = slot.get(cx);
        let Some(root) = method.root() else { continue };
        let mut counters = method.counters.shared();
        let result = catch_method_failure(|| {
            switches::simplify(cx, &mut counters, root)?;
            if cx.options.prettify_ifs {
                prettify_ifs(&mut cx.ir, &mut counters, root);
            }
            Ok(())
        });
        if let Err(error) = result {
            if error.kind() == io::ErrorKind::Interrupted {
                return Err(error);
            }
            log::warn!(
                "Could not prepare {}.{} for writing: {error}",
                cx.class_nodes[node].class.qualified_name,
                slot.get(cx).method
            );
            slot.get_mut(cx).write_error = Some(error);
        }
    }
    Ok(())
}

/// Prettify nested branches first. An if inside a switch stays in its case.
fn prettify_ifs(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) {
    for child in ir[stat].stats.iter().copied().collect::<Vec<_>>() {
        if matches!(ir[child].kind, StatementKind::Switch(_)) {
            continue;
        }
        prettify_ifs(ir, counters, child);
        let StatementKind::If(branch) = ir[child].kind else {
            continue;
        };
        if branch.has_else
            && !branch.pattern_matched
            && let (Some(yes), Some(no), Some(edge)) =
                (branch.if_stat, branch.else_stat, branch.else_edge)
            && exits(ir, yes)
        {
            let force = ir[yes].exprents.is_some_and(|list| ir[list].len() == 1)
                && ir[no].exprents.is_some_and(|list| ir[list].len() > 1);
            if !force
                && (exits(ir, no)
                    || matches!(&ir[no].kind, StatementKind::If(alt) if alt.if_stat.is_some_and(|stat|exits(ir,stat))))
            {
                continue;
            }

            let sequence = Statement::new_sequence(ir, counters, &[child, no]);
            let no_id = ir[no].id;
            let statement = &mut ir[child];
            statement.stats.remove_with_key(&no_id);
            let StatementKind::If(branch) = &mut statement.kind else {
                unreachable!()
            };
            branch.has_else = false;
            branch.else_stat = None;
            branch.else_edge = None;
            child.replace_with(ir, sequence);
            edge.change_source(ir, child);
            sequence.set_all_parent(ir);
        }
    }
}

fn exits(ir: &Ir, stat: StatId) -> bool {
    matches!(ir[stat].kind, StatementKind::BasicBlock { .. })
        && ir[stat].direct_successors().first().is_some_and(|&e| {
            ir[e].edge_type == EdgeType::Break
                && matches!(ir[ir[e].destination].kind, StatementKind::DummyExit { .. })
        })
        && ir[stat]
            .exprents
            .and_then(|list| ir[list].last())
            .is_some_and(|&e| matches!(ir[e].kind, ExprKind::Exit { .. }))
}
