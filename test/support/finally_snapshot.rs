// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use itertools::Itertools;
use vineflower_rs::code::cfg::ControlFlowGraph;
use vineflower_rs::code::code_constants::{OPC_JSR, OPC_JSR_W};
use vineflower_rs::code::instruction::InstructionKind;
use vineflower_rs::decompiler::ir::{BlockId, Ir, StatId};
use vineflower_rs::decompiler::stats::StatementKind;
use vineflower_rs::engine::Cx;
use vineflower_rs::engine::method_processor::StructuredMethod;
use vineflower_rs::structs::StructClass;

pub fn run(
    cx: &mut Cx,
    structured: StructuredMethod,
    class: &StructClass,
    coverage: &mut Coverage,
) -> String {
    let mut snapshot = format!("input={}", graph_snapshot(&cx.ir, &structured.flow.graph));
    coverage.record_input(&cx.ir, &structured.flow.graph);
    let recovered = match catch_unwind(AssertUnwindSafe(|| structured.recover_finally(cx, class))) {
        Ok(Ok(method)) => method,
        Ok(Err(error)) => return format!("{snapshot}\t{}", recovery_error(error)),
        Err(error) => return format!("{snapshot}\trecovery-panic={}", super::panic_text(&*error)),
    };
    coverage.record(&cx.ir, recovered.structured.root);
    coverage.semaphores += recovered.synthetic_semaphores.len();
    write!(
        snapshot,
        "\trecovered={};{}\t{}",
        recovered.synthetic_semaphores.iter().sorted().join(","),
        graph_snapshot(&cx.ir, &recovered.structured.flow.graph),
        super::structure_snapshot(
            &cx.ir,
            recovered.structured.root,
            &recovered.structured.flow.counters
        ),
    )
    .unwrap();
    match catch_unwind(AssertUnwindSafe(|| {
        let method = recovered.into_expressions(cx, class)?;
        let StatementKind::Root { content_flags, .. } = &cx.ir[method.root].kind else {
            unreachable!();
        };
        let structure = super::structure_snapshot(&cx.ir, method.root, &method.flow.counters);
        let expressions =
            super::expression_snapshot::snapshot(cx, method.root, &method.flow.counters);
        Ok::<_, std::io::Error>(format!(
            "{structure};content={},{},{}\t{expressions}",
            content_flags.has_try_catch, content_flags.has_loops, content_flags.has_switch
        ))
    })) {
        Ok(Ok(post)) => format!("{snapshot}\t{post}"),
        Ok(Err(error)) => format!(
            "{snapshot}\tpost-finally-error={}",
            super::one_line(&error.to_string())
        ),
        Err(error) => format!(
            "{snapshot}\tpost-finally-panic={}",
            super::panic_text(&*error)
        ),
    }
}

fn recovery_error(error: std::io::Error) -> String {
    let text = super::one_line(&error.to_string());
    if error.kind() == std::io::ErrorKind::InvalidData {
        if text == "parsing failure!" {
            return "recovery-rejected=reparse:parsing failure!".into();
        }
        if let Some(bounds) = text.strip_prefix("finally instruction offset removal: ") {
            return format!("recovery-rejected=instruction offsets:{bounds}");
        }
    }
    format!("recovery-error={text}")
}

// FinallyProcessor.deleteArea retargets a HashSet of BasicBlocks. Java hashes
// those objects by identity, so only the incoming edge order can vary.
pub fn same_predecessor_membership(java: &str, rust: &str) -> bool {
    java.split(';').zip_longest(rust.split(';')).all(|pair| {
        let itertools::EitherOrBoth::Both(java, rust) = pair else {
            return false;
        };
        if java == rust {
            return true;
        }
        for prefix in ["preds=", "exit-preds="] {
            if let (Some(java), Some(rust)) = (java.strip_prefix(prefix), rust.strip_prefix(prefix))
                && let (Some((java_regular, java_exception)), Some((rust_regular, rust_exception))) =
                    (java.split_once('/'), rust.split_once('/'))
            {
                return java_regular.split(',').sorted().eq(rust_regular.split(',').sorted())
                    && java_exception.split(',').sorted().eq(rust_exception.split(',').sorted());
            }
        }
        false
    })
}

fn graph_snapshot(ir: &Ir, graph: &ControlFlowGraph) -> String {
    let originals: HashMap<_, _> = graph
        .sequence
        .instructions
        .iter()
        .enumerate()
        .map(|(i, inst)| (Arc::as_ptr(inst), i))
        .collect();
    let mut aliases = HashMap::new();
    let mut fields = format!(
        "entry={}/{}/{};comments={}|{}",
        ir[graph.first].id,
        ir[graph.last].id,
        graph.last_id,
        graph.add_error_comment,
        graph.comment_lines.iter().join("|")
    );
    let ids = |blocks: &[BlockId]| blocks.iter().map(|&block| ir[block].id).join(",");
    for &block in &graph.blocks {
        let block = &ir[block];
        write!(
            fields,
            ";block={};edges={}/{};preds={}/{};offsets={}",
            block.id,
            ids(&block.succs),
            ids(&block.succ_exceptions),
            ids(&block.preds),
            ids(&block.pred_exceptions),
            block.instr_old_offsets.iter().join(",")
        )
        .unwrap();
        for instruction in &block.seq {
            let key = Arc::as_ptr(instruction);
            let next = aliases.len();
            let identity = *aliases.entry(key).or_insert(next);
            let original = originals
                .get(&key)
                .map_or_else(|| "-1".into(), usize::to_string);
            let operands = (0..instruction.operands_count())
                .map(|i| instruction.operand(i))
                .join(",");
            let target = match &instruction.kind {
                InstructionKind::Plain => String::new(),
                InstructionKind::Jump(jump) => format!("j{}", jump.destination),
                InstructionKind::Switch(branch) => format!(
                    "s{}/{}/{}",
                    branch.default_destination,
                    branch.destinations.iter().join(","),
                    branch.values.iter().join(",")
                ),
            };
            write!(
                fields,
                ";insn={identity}|{original}|{},{},{},{},{}[{operands}]{target}",
                instruction.opcode,
                instruction.group,
                instruction.wide,
                instruction.start_offset,
                instruction.length
            )
            .unwrap();
        }
    }
    let exit = &ir[graph.last];
    write!(
        fields,
        ";exit-preds={}/{}",
        ids(&exit.preds),
        ids(&exit.pred_exceptions)
    )
    .unwrap();
    for range in &graph.exceptions {
        let types = range
            .exception_types
            .as_ref()
            .map_or_else(|| "*".into(), |types| types.iter().join(","));
        write!(
            fields,
            ";range={}|{types}|{}",
            ir[range.handler].id,
            ids(&range.protected_range)
        )
        .unwrap();
    }
    write!(
        fields,
        ";finally-exits={}",
        graph
            .finally_exits
            .iter()
            .map(|&block| ir[block].id)
            .sorted()
            .join(",")
    )
    .unwrap();
    write!(
        fields,
        ";subroutines={}",
        graph
            .subroutines
            .iter()
            .map(|(&entry, &exit)| format!("{}:{}", ir[entry].id, ir[exit].id))
            .sorted()
            .join(",")
    )
    .unwrap();
    fields
}

#[derive(Default)]
pub struct Coverage {
    catch_all: usize,
    synchronized: usize,
    confirmed: usize,
    semaphores: usize,
    shared_instructions: usize,
    jsr_with_shared_instructions: usize,
}

impl Coverage {
    fn record_input(&mut self, ir: &Ir, graph: &ControlFlowGraph) {
        let mut seen = HashSet::new();
        if graph
            .blocks
            .iter()
            .flat_map(|&block| ir[block].seq.iter())
            .any(|instr| !seen.insert(Arc::as_ptr(instr)))
        {
            self.shared_instructions += 1;
            if graph
                .sequence
                .iter()
                .any(|instr| matches!(instr.opcode, OPC_JSR | OPC_JSR_W))
            {
                self.jsr_with_shared_instructions += 1;
            }
        }
    }

    fn record(&mut self, ir: &Ir, root: StatId) {
        let mut pending = vec![root];
        let mut catch_all = false;
        let mut confirmed = false;
        let mut synchronized = false;
        while let Some(stat) = pending.pop() {
            match ir[stat].kind {
                StatementKind::CatchAll { is_finally, .. } => {
                    catch_all = true;
                    confirmed |= is_finally;
                }
                StatementKind::Synchronized { .. } => synchronized = true,
                _ => {}
            }
            pending.extend(ir[stat].stats.iter().copied());
        }
        self.catch_all += usize::from(catch_all);
        self.confirmed += usize::from(confirmed);
        self.synchronized += usize::from(synchronized);
    }

    pub fn report(&self) {
        eprintln!(
            "Finally coverage: {} method runs with catch-all handlers, {} with synchronized statements, {} with recovered finally handlers, {} semaphores, {} with shared instructions in the transferred CFG ({} with JSR)",
            self.catch_all,
            self.synchronized,
            self.confirmed,
            self.semaphores,
            self.shared_instructions,
            self.jsr_with_shared_instructions,
        );
    }
}
