// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{HashMap, HashSet, VecDeque};
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::classfile::{ConstantPool, ExceptionHandler};

use super::frame::{Effect, Frame};
use super::{LegacyError, NormalizedCode, Origin, invalid};

// CFG exception coordinates use the classfile's u16 representation.
const MAX_CODE: usize = u16::MAX as usize;

type BlockId = usize;
type ContextId = usize;
type NodeId = usize;

#[derive(Debug)]
enum Flow {
    Next(BlockId),
    Branch { target: BlockId, next: Option<BlockId> },
    Switch(Vec<BlockId>), // default, then cases in original order
    Call { target: BlockId, next: BlockId },
    Ret(u16),
    Stop,
}

struct Block {
    ops: Range<usize>,
    flow: Flow,
    /// Indices into the original table, in selection order.
    handlers: Vec<usize>,
}

struct Handler {
    target: BlockId,
    catch_type: u16,
}

struct Topology {
    blocks: Vec<Block>,
    handlers: Vec<Handler>,
}

impl Topology {
    fn build(ops: &[Instruction], handlers: &[ExceptionHandler]) -> Result<Self, LegacyError> {
        let mut leaders = vec![false; ops.len()];
        leaders[0] = true;
        let index = |offset| ops.binary_search_by_key(&offset, |op| op.offset)
            .map_err(|_| invalid(offset, "not an instruction boundary"));
        let code_end = ops.last().and_then(|op| op.offset.checked_add(op.len));
        for (i, op) in ops.iter().enumerate() {
            match &op.operand {
                Operand::Branch(target) => leaders[index(*target)?] = true,
                Operand::Switch { default, cases } => {
                    leaders[index(*default)?] = true;
                    for &(_, target) in cases {
                        leaders[index(target)?] = true;
                    }
                }
                _ => (),
            }
            if matches!(op.opcode, 0x99..=0xb1 | 0xbf | 0xc6..=0xc9)
                && let Some(next) = leaders.get_mut(i + 1)
            {
                *next = true;
            }
        }
        for handler in handlers {
            let start = u32::from(handler.start_pc);
            let end = u32::from(handler.end_pc);
            if start >= end {
                return Err(invalid(start, "invalid exception range"));
            }
            leaders[index(start)?] = true;
            if Some(end) != code_end {
                leaders[index(end)?] = true;
            }
            leaders[index(u32::from(handler.handler_pc))?] = true;
        }
        let starts: Vec<_> = leaders.into_iter().enumerate()
            .filter_map(|(i, leader)| leader.then_some(i)).collect();
        let block_at = |offset| starts.binary_search_by_key(&offset, |&i| ops[i].offset)
            .map_err(|_| invalid(offset, "not a basic block boundary"));
        let mut blocks = Vec::with_capacity(starts.len());
        for (i, &start) in starts.iter().enumerate() {
            let end = starts.get(i + 1).copied().unwrap_or(ops.len());
            let last = &ops[end - 1];
            let bad = |reason| invalid(last.offset, reason);
            let next = || (i + 1 < starts.len()).then_some(i + 1)
                .ok_or_else(|| bad("instruction falls through the end of the method"));
            let branch = || match last.operand {
                Operand::Branch(target) => block_at(target),
                _ => Err(bad("missing branch target")),
            };
            let flow = match last.opcode {
                0x99..=0xa6 | 0xc6 | 0xc7 => Flow::Branch { target: branch()?, next: Some(next()?) },
                0xa7 | 0xc8 => Flow::Branch { target: branch()?, next: None },
                0xa8 | 0xc9 => Flow::Call { target: branch()?, next: next()? },
                0xa9 => match last.operand {
                    Operand::Local(index) => Flow::Ret(index),
                    _ => return Err(bad("missing ret local index")),
                },
                0xaa | 0xab => {
                    let Operand::Switch { default, cases } = &last.operand else {
                        return Err(bad("missing switch targets"));
                    };
                    let targets = std::iter::once(*default).chain(cases.iter().map(|&(_, target)| target))
                        .map(block_at).collect::<Result<_, _>>()?;
                    Flow::Switch(targets)
                }
                0xac..=0xb1 | 0xbf => Flow::Stop,
                _ => Flow::Next(next()?),
            };
            blocks.push(Block { ops: start..end, flow, handlers: Vec::new() });
        }
        let mut table = Vec::with_capacity(handlers.len());
        for handler in handlers {
            let start = block_at(u32::from(handler.start_pc))?;
            let end = if Some(u32::from(handler.end_pc)) == code_end {
                blocks.len()
            } else {
                block_at(u32::from(handler.end_pc))?
            };
            let target = block_at(u32::from(handler.handler_pc))?;
            for block in &mut blocks[start..end] {
                block.handlers.push(table.len());
            }
            table.push(Handler { target, catch_type: handler.catch_type });
        }
        Ok(Self { blocks, handlers: table })
    }

    /// Approximate one subroutine's lexical extent by following each jsr's
    /// continuation, not its invocation edge. Exception destinations are part
    /// of this extent too. At shared tails the oldest live owner is used below.
    fn members(&self, entry: BlockId) -> HashSet<BlockId> {
        let mut visited = HashSet::from([entry]);
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            let block = &self.blocks[block];
            let mut add = |target| {
                if visited.insert(target) {
                    pending.push(target);
                }
            };
            match &block.flow {
                Flow::Next(next) | Flow::Call { next, .. } => add(*next),
                Flow::Branch { target, next } => {
                    add(*target);
                    if let Some(next) = next {
                        add(*next);
                    }
                }
                Flow::Switch(targets) => targets.iter().copied().for_each(&mut add),
                Flow::Ret(_) | Flow::Stop => (),
            }
            for &handler in &block.handlers {
                add(self.handlers[handler].target);
            }
        }
        visited
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Key {
    context: ContextId,
    block: BlockId,
}

struct Context {
    entry: BlockId,
    continuation: Option<Key>,
}

struct Node {
    key: Key,
    input: Frame,
    queued: bool,
    /// Sparse opcode substitutions after erasing returnAddress values.
    rewrites: Vec<(usize, u8)>,
}

struct Expansion<'a> {
    ops: &'a [Instruction],
    topology: &'a Topology,
    effects: Vec<Option<Effect>>,
    contexts: Vec<Context>,
    calls: HashMap<Key, ContextId>,
    members: HashMap<BlockId, HashSet<BlockId>>,
    ids: HashMap<Key, NodeId>,
    nodes: Vec<Node>,
    pending: VecDeque<NodeId>,
    op_count: usize,
}

pub(super) fn expand(
    ops: &[Instruction],
    handlers: &[ExceptionHandler],
    pool: &ConstantPool<'_>,
) -> Result<NormalizedCode, LegacyError> {
    let topology = Topology::build(ops, handlers)?;
    let mut expansion = Expansion {
        ops,
        topology: &topology,
        effects: vec![None; ops.len()],
        contexts: vec![Context { entry: 0, continuation: None }],
        members: HashMap::from([(0, topology.members(0))]),
        calls: HashMap::new(),
        ids: HashMap::new(),
        nodes: Vec::new(),
        pending: VecDeque::new(),
        op_count: 0,
    };
    expansion.connect(Key { context: 0, block: 0 }, &Frame::default())?;
    while let Some(node) = expansion.pending.pop_front() {
        expansion.process(node, pool)?;
    }
    expansion.emit()
}

impl Expansion<'_> {
    fn connect(&mut self, key: Key, input: &Frame) -> Result<(), LegacyError> {
        let block = &self.topology.blocks[key.block];
        if let Some(&id) = self.ids.get(&key) {
            let node = &mut self.nodes[id];
            if node.input.merge(input, self.ops[block.ops.start].offset)? && !node.queued {
                node.queued = true;
                self.pending.push_back(id);
            }
        } else {
            self.op_count += block.ops.len();
            if self.op_count > MAX_CODE {
                return Err(LegacyError::CodeTooLong);
            }
            let id = self.nodes.len();
            self.ids.insert(key, id);
            self.nodes.push(Node { key, input: input.clone(), queued: true, rewrites: Vec::new() });
            self.pending.push_back(id);
        }
        Ok(())
    }

    /// A branch (including an exception edge) may leave a subroutine directly
    /// for a tail owned by a caller. Without this rule, an outer catch/finally
    /// reached from a callee can be cloned under the wrong calling context.
    fn target(&self, mut context: ContextId, block: BlockId) -> Key {
        let mut owner = context;
        while let Some(continuation) = self.contexts[context].continuation {
            context = continuation.context;
            if self.members[&self.contexts[context].entry].contains(&block) {
                owner = context;
            }
        }
        Key { context: owner, block }
    }

    fn call(
        &mut self,
        caller: Key,
        entry: BlockId,
        next: BlockId,
        offset: u32,
    ) -> Result<Key, LegacyError> {
        if let Some(&context) = self.calls.get(&caller) {
            return Ok(Key { context, block: entry });
        }
        let mut context = caller.context;
        while let Some(continuation) = self.contexts[context].continuation {
            if self.contexts[context].entry == entry {
                return Err(invalid(offset, "recursive jsr invocation"));
            }
            context = continuation.context;
        }
        // Even if a continuation belongs to an ancestor, the active calls are
        // needed to detect recursion and to resolve edge ownership while this
        // invocation runs. Keep the immediate caller until ret executes.
        let context = self.contexts.len();
        self.contexts.push(Context { entry, continuation: Some(Key { context: caller.context, block: next }) });
        self.calls.insert(caller, context);
        self.members.entry(entry).or_insert_with(|| self.topology.members(entry));
        Ok(Key { context, block: entry })
    }

    fn process(&mut self, id: NodeId, pool: &ConstantPool<'_>) -> Result<(), LegacyError> {
        let node = &mut self.nodes[id];
        node.queued = false;
        let key = node.key;
        let mut frame = node.input.clone();
        let block = &self.topology.blocks[key.block];
        let mut exception = (!block.handlers.is_empty()).then(|| frame.exception());
        node.rewrites.clear();
        let last = block.ops.end - 1;
        for i in block.ops.clone() {
            let op = &self.ops[i];
            if matches!(op.opcode, 0xa8 | 0xa9 | 0xc9) {
                break;
            }
            let effect = match self.effects[i] {
                Some(effect) => effect,
                None => {
                    let effect = Effect::of(op, pool)?;
                    self.effects[i] = Some(effect);
                    effect
                }
            };
            let opcode = frame.step(op, effect)?;
            if opcode != op.opcode {
                node.rewrites.push((i, opcode));
            }
            // Exceptional edges see the locals before the potentially failing
            // instruction, and an operand stack containing only the exception.
            if i != last && matches!(effect, Effect::Write { .. })
                && let Some(exception) = &mut exception
            {
                exception.merge_locals(&frame);
            }
        }
        let offset = self.ops[last].offset;
        match &block.flow {
            Flow::Next(next) => self.connect(self.target(key.context, *next), &frame)?,
            Flow::Branch { target, next } => {
                self.connect(self.target(key.context, *target), &frame)?;
                if let Some(next) = next {
                    self.connect(self.target(key.context, *next), &frame)?;
                }
            }
            Flow::Switch(targets) => {
                for &target in targets {
                    self.connect(self.target(key.context, target), &frame)?;
                }
            }
            Flow::Call { target, next } => {
                let destination = self.call(key, *target, *next, offset)?;
                frame.push_address(destination.context);
                self.connect(destination, &frame)?;
            }
            Flow::Ret(local) => {
                let continuation = self.contexts[key.context].continuation
                    .ok_or_else(|| invalid(offset, "ret outside a subroutine"))?;
                frame.check_ret(*local, key.context, offset)?;
                self.connect(self.target(continuation.context, continuation.block), &frame)?;
            }
            Flow::Stop => (),
        }
        if let Some(exception) = exception {
            for &handler in &block.handlers {
                let target = self.topology.handlers[handler].target;
                self.connect(self.target(key.context, target), &exception)?;
            }
        }
        Ok(())
    }

    fn emit(self) -> Result<NormalizedCode, LegacyError> {
        let mut order: Vec<_> = (0..self.nodes.len()).collect();
        order.sort_unstable_by_key(|&node| self.nodes[node].key);
        let mut emitter = Emitter {
            instructions: Vec::with_capacity(self.op_count),
            origins: Vec::with_capacity(self.op_count),
            pending_targets: Vec::new(),
            offset: 0,
        };
        let mut starts = vec![0; order.len()];
        let mut ranges: Vec<Vec<Protected>> = (0..self.topology.handlers.len()).map(|_| Vec::new()).collect();
        for (index, &id) in order.iter().enumerate() {
            let node = &self.nodes[id];
            let Key { context, block } = node.key;
            let block = &self.topology.blocks[block];
            let target = |block| self.ids[&self.target(context, block)];
            let start = emitter.offset;
            starts[id] = start;
            let mut rewrites = node.rewrites.iter().copied().peekable();
            for i in block.ops.clone() {
                let source = &self.ops[i];
                let mut op = source.clone();
                if let Some((_, opcode)) = rewrites.next_if(|(index, _)| *index == i) {
                    op.opcode = opcode;
                    op.operand = Operand::None;
                    op.len = 1;
                }
                if i + 1 == block.ops.end {
                    match &block.flow {
                        Flow::Call { target, .. } => {
                            let block = Key { context: self.calls[&node.key], block: *target };
                            op.opcode = if source.opcode == 0xc9 { 0xc8 } else { 0xa7 };
                            op.operand = Operand::Branch(self.ids[&block] as u32);
                        }
                        Flow::Ret(_) => {
                            let continuation = self.contexts[context].continuation.unwrap();
                            let dest = self.ids[&self.target(continuation.context, continuation.block)];
                            op.opcode = 0xa7;
                            op.operand = Operand::Branch(dest as u32);
                            op.len = 3;
                        }
                        Flow::Branch { target: dest, .. } => {
                            op.operand = Operand::Branch(target(*dest) as u32);
                        }
                        Flow::Switch(targets) => {
                            let Operand::Switch { default, cases } = &mut op.operand else { unreachable!() };
                            *default = target(targets[0]) as u32;
                            for ((_, dest), &block) in cases.iter_mut().zip(&targets[1..]) {
                                *dest = target(block) as u32;
                            }
                            op.len = op.len - switch_padding(source.offset) + switch_padding(emitter.offset);
                        }
                        Flow::Next(_) | Flow::Stop => (),
                    }
                }
                emitter.push(op, Some(source))?;
            }
            if let Flow::Next(next) | Flow::Branch { next: Some(next), .. } = block.flow {
                let dest = target(next);
                if order.get(index + 1) != Some(&dest) {
                    emitter.push(Instruction {
                        offset: 0,
                        opcode: 0xc8,
                        operand: Operand::Branch(dest as u32),
                        len: 5,
                    }, None)?;
                }
            }
            for &index in &block.handlers {
                let handler = &self.topology.handlers[index];
                let target = target(handler.target);
                let protected = &mut ranges[index];
                let end = emitter.offset;
                if let Some(previous) = protected.last_mut().filter(|p| p.end == start && p.target == target) {
                    previous.end = end;
                } else {
                    protected.push(Protected { start, end, target });
                }
            }
        }
        // Preserve first-match priority when an original table entry splits.
        let handlers = ranges.into_iter().zip(&self.topology.handlers)
            .flat_map(|(ranges, handler)| ranges.into_iter().map(|protected| ExceptionHandler {
                start_pc: protected.start as u16,
                end_pc: protected.end as u16,
                handler_pc: starts[protected.target] as u16,
                catch_type: handler.catch_type,
            })).collect();
        for index in emitter.pending_targets {
            match &mut emitter.instructions[index].operand {
                Operand::Branch(target) => *target = starts[*target as usize],
                Operand::Switch { default, cases } => {
                    *default = starts[*default as usize];
                    for (_, target) in cases {
                        *target = starts[*target as usize];
                    }
                }
                _ => unreachable!(),
            }
        }
        Ok(NormalizedCode { instructions: emitter.instructions, handlers, origins: Some(emitter.origins) })
    }
}

struct Protected {
    start: u32,
    end: u32,
    target: NodeId,
}

struct Emitter {
    instructions: Vec<Instruction>,
    origins: Vec<Origin>,
    pending_targets: Vec<usize>,
    offset: u32,
}

impl Emitter {
    fn push(&mut self, mut op: Instruction, source: Option<&Instruction>) -> Result<(), LegacyError> {
        op.offset = self.offset;
        self.offset = self.offset.checked_add(op.len).filter(|&n| n as usize <= MAX_CODE)
            .ok_or(LegacyError::CodeTooLong)?;
        if let Some(source) = source {
            // Realigned switch operands still refer to the same source bytes;
            // only the number of padding bytes between them and the opcode changes.
            if matches!(op.operand, Operand::Switch { .. }) {
                let before = 1 + switch_padding(op.offset);
                let source_before = 1 + switch_padding(source.offset);
                self.origins.push(Origin { start: op.offset, len: before.min(source_before), source: source.offset });
                self.origins.push(Origin {
                    start: op.offset + before,
                    len: op.len - before,
                    source: source.offset + source_before,
                });
            } else {
                self.origins.push(Origin { start: op.offset, len: source.len.min(op.len), source: source.offset });
            }
        }
        if matches!(op.operand, Operand::Branch(_) | Operand::Switch { .. }) {
            self.pending_targets.push(self.instructions.len());
        }
        self.instructions.push(op);
        Ok(())
    }
}

fn switch_padding(offset: u32) -> u32 {
    3 - offset % 4
}
