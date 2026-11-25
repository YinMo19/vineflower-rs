// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Recover finally handlers on the CFG, one candidate per parse of its statement tree.

mod information;
mod rewrite;
mod verify;

use std::{collections::VecDeque, io, sync::Arc};

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;

use crate::code::dead_code_helper as dead;
use crate::decompiler::exps::{Expr, ExprKind, Variable};
use crate::decompiler::ir::{BlockId, Ir, StatId};
use crate::decompiler::sforms::{reassign_ssa, reset_versions, split_ssa, split_ssau};
use crate::decompiler::stats::StatementKind;
use crate::engine::{Cx, counter_container::VAR_COUNTER, method_processor::StructuredMethod};
use crate::structs::StructClass;
use crate::types::VarType;

#[derive(Clone, Copy, PartialEq, Eq)]
enum HandlerKind {
    Stack,
    Pop,
    Store,
    Empty,
}

struct FinallyInfo {
    first_code: HandlerKind,
    exception_offset: i32,
    last: IndexMap<BlockId, bool>,
}

#[derive(Clone, Copy)]
enum Recovery {
    Inconsistent,
    Inlined,
    Semaphore(i32),
}

#[derive(Default)]
pub struct FinallyProcessor {
    handlers: FxHashMap<BlockId, Recovery>,
    pub synthetic_semaphores: IndexSet<i32>,
}

impl FinallyProcessor {
    pub fn iterate_graph(
        &mut self,
        cx: &mut Cx,
        class: &StructClass,
        method: &mut StructuredMethod,
    ) -> io::Result<bool> {
        let root = method.root;
        let mut pending = vec![root];
        while let Some(stat) = pending.pop() {
            if let Some(parent) = cx.ir[stat].parent
                && let StatementKind::CatchAll {
                    handler: Some(body),
                    ..
                } = cx.ir[parent].kind
                && cx.ir[parent].first == Some(stat)
                && !cx.ir[parent].copied
            {
                let handler = basic_head(&cx.ir, body);
                match self.handlers.get(&handler).copied() {
                    Some(Recovery::Inconsistent) => {}
                    Some(recovery) => {
                        let monitor = if let Recovery::Semaphore(index) = recovery {
                            let var = ExprKind::Variable(Variable::in_method(
                                index,
                                VarType::VARTYPE_INT,
                                method.flow.variables,
                            ));
                            Some(Expr::new(&mut cx.ir, &mut method.flow.counters, var, None))
                        } else {
                            None
                        };
                        let StatementKind::CatchAll {
                            is_finally,
                            monitor: slot,
                            ..
                        } = &mut cx.ir[parent].kind
                        else {
                            unreachable!()
                        };
                        *is_finally = true;
                        *slot = monitor;
                    }
                    None => {
                        let state = self.recover(cx, class, method, parent, handler)?;
                        self.handlers.insert(handler, state);
                        return Ok(true);
                    }
                }
            }
            pending.extend(cx.ir[stat].stats.iter().copied());
        }
        Ok(false)
    }

    fn recover(
        &mut self,
        cx: &mut Cx,
        class: &StructClass,
        method: &mut StructuredMethod,
        catch_all: StatId,
        handler: BlockId,
    ) -> io::Result<Recovery> {
        // Each successful iterateGraph returns immediately. The SSAU graph and
        // instruction rewrites therefore live for just this candidate.
        method.process_expressions(cx, class)?;
        let root = method.root;
        let owner = Arc::clone(root.method(&cx.ir));
        let ssa = split_ssa(&mut cx.ir, root, &owner);
        let rewrites = reassign_ssa(&mut cx.ir, root, &ssa.versions, &method.flow.counters);
        reset_versions(&mut cx.ir, root);
        let ssau = split_ssau(&mut cx.ir, root, &owner);
        reset_versions(&mut cx.ir, root);

        let Some(info) = information::inspect(cx, root, catch_all, &owner)? else {
            cx.ir[root].add_comment("$VF: Could not inline inconsistent finally blocks", true);
            return Ok(Recovery::Inconsistent);
        };

        let graph = &mut method.flow.graph;
        let recovered = if cx.options.decompile_finally
            && verify::verify(
                &mut cx.ir,
                graph,
                catch_all,
                &info,
                &rewrites,
                &ssau.versions.graph,
            )? {
            rewrite::inline_return_var(&mut cx.ir, graph, handler, &info);
            Recovery::Inlined
        } else {
            let var = method.flow.counters.get_counter_and_increment(VAR_COUNTER);
            self.synthetic_semaphores.insert(var);
            let body = cx.ir[catch_all].first.unwrap();
            let head = basic_head(&cx.ir, body);
            let protected = basic_blocks(&cx.ir, body);
            rewrite::insert_semaphore(
                &mut cx.ir,
                graph,
                &protected,
                head,
                handler,
                var,
                &info,
                owner.bytecode_version,
            )?;
            if cx.options.decompiler_comments {
                cx.ir[root].add_comment("$VF: Could not verify finally blocks. A semaphore variable has been added to preserve control flow.", true);
            }
            Recovery::Semaphore(var)
        };
        dead::remove_dead_blocks(&mut cx.ir, graph);
        dead::remove_empty_blocks(&mut cx.ir, graph, &cx.options);
        dead::merge_basic_blocks(&mut cx.ir, graph, &cx.options);
        Ok(recovered)
    }
}

fn basic_head(ir: &Ir, stat: StatId) -> BlockId {
    let StatementKind::BasicBlock { block } = ir[stat.get_basic_head(ir)].kind else {
        unreachable!()
    };
    block
}

fn basic_blocks(ir: &Ir, stat: StatId) -> IndexSet<BlockId> {
    let mut blocks = IndexSet::new();
    let mut pending = VecDeque::from([stat]);
    while let Some(stat) = pending.pop_front() {
        if let StatementKind::BasicBlock { block } = ir[stat].kind {
            blocks.insert(block);
        } else {
            pending.extend(ir[stat].stats.iter().copied());
        }
    }
    blocks
}
