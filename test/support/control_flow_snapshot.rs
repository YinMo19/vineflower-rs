// SPDX-License-Identifier: Apache-2.0

use std::fmt::Write;

use itertools::Itertools;

use vineflower_rs::code::cfg::ControlFlowGraph;
use vineflower_rs::decompiler::ir::{BlockId, Ir};

// Match ControlFlowReference.java. Once cleanup can iterate identity sets,
// compare protected membership and incoming exit edges as multisets. Preserve
// block order, both successor lists, the exception table and its types, and RPO.
pub(super) fn snapshot(ir: &Ir, graph: &ControlFlowGraph, constructed: bool) -> String {
    let mut result = format!(
        "first={};last={};last-id={}",
        ir[graph.first].id, ir[graph.last].id, graph.last_id
    );
    let ids = |blocks: &[BlockId]| blocks.iter().map(|&block| ir[block].id).join(",");
    let member_ids = |blocks: &[BlockId]| {
        if constructed {
            ids(blocks)
        } else {
            blocks.iter().map(|&block| ir[block].id).sorted().join(",")
        }
    };
    for &block in &graph.blocks {
        let block = &ir[block];
        let instructions = block
            .seq
            .iter()
            .map(|inst| {
                let operands = (0..inst.operands_count())
                    .map(|i| inst.operand(i))
                    .join(" ");
                format!(
                    "{}@{}+{}/{}/{}[{operands}]",
                    inst.opcode, inst.start_offset, inst.length, inst.group, inst.wide
                )
            })
            .join(",");
        write!(
            result,
            ";block={};instructions={instructions};offsets={};edges={};exception-edges={}",
            block.id,
            block.instr_old_offsets.iter().join(","),
            ids(&block.succs),
            ids(&block.succ_exceptions)
        )
        .unwrap();
    }
    write!(
        result,
        ";exit-predecessors={}",
        member_ids(&ir[graph.last].preds)
    )
    .unwrap();
    for range in &graph.exceptions {
        let types = range
            .exception_types
            .as_ref()
            .map(|types| types.iter().join(","))
            .unwrap_or_else(|| "*".to_owned());
        write!(
            result,
            ";range={}:{}:{}",
            ir[range.handler].id,
            types,
            member_ids(&range.protected_range)
        )
        .unwrap();
    }
    write!(
        result,
        ";finally-exits={};rpo={};error-comment={};comments={}",
        graph
            .finally_exits
            .iter()
            .map(|&block| ir[block].id)
            .sorted()
            .join(","),
        ids(&graph.get_reverse_post_order(ir)),
        graph.add_error_comment,
        graph.comment_lines.iter().join(",")
    )
    .unwrap();
    if constructed {
        let subroutines = graph
            .subroutines
            .iter()
            .map(|(&call, &exit)| format!("{}:{}", ir[call].id, ir[exit].id))
            .sorted()
            .join(",");
        write!(result, ";subroutines={subroutines}").unwrap();
    }
    result
}
