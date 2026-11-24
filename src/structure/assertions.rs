// Based on Vineflower's AssertProcessor and MethodPropertiesProcessor (Apache-2.0).
// Copyright 2000-2020 JetBrains s.r.o.

use std::{
    collections::{BTreeMap, BTreeSet},
    mem,
};

use crate::{
    ClassGroup,
    bytecode::{Instruction, Operand, decode},
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Constant, ConstantPool, Member, TypeTarget, find_attribute},
    lift::{Effect, Machine},
};

mod interface;
pub(crate) use interface::interface_guards;

#[cfg(test)]
mod tests;

use super::{Emitter, Region, StructureError, logical};

const ERROR: &str = "java/lang/AssertionError";
const STATIC_FINAL: u16 = 0x0008 | 0x0010;
const SYNTHETIC: u16 = 0x1000;

/// The guard is hidden only when its initialization and every bytecode use
/// are accounted for. A plain (possibly user-written) AssertionError throw
/// never establishes that a class has a guard.
#[derive(Debug)]
pub(crate) struct Guard<'c> {
    owner: &'c str,
    field: &'c str,
    initializer: usize,
    declares_field: bool,
    methods: BTreeMap<(u16, u16), usize>,
}

impl<'c> Guard<'c> {
    pub(crate) fn prove(
        group: &ClassGroup<'_>,
        class: &'c ClassFile<'_>,
        status_owner: &str,
    ) -> Option<Self> {
        // Interfaces use a synthetic holder; enum initialization is distinct.
        if class.access_flags & (0x0200 | 0x4000) != 0 {
            return None;
        }
        let pool = &class.pool;
        let owner = pool.class_name(class.this_class).ok()?;
        let mut fields = class
            .fields
            .iter()
            .filter(|field| canonical_guard_field(class, field));
        let field = pool.utf8(fields.next()?.name_index).ok()?;
        if fields.next().is_some() {
            return None;
        }
        let mut guard = Self {
            owner,
            field,
            initializer: 0,
            declares_field: true,
            methods: BTreeMap::new(),
        };
        // No same-package class may refer to this package-private guard. A
        // MethodHandle is a real use even when there is no getstatic in Code.
        if group.classes().any(|(name, other)| {
            name != owner && package(name) == package(owner) && other.pool.iter().any(|constant| {
                guard.symbolic_guard_ref(group, &other.pool, constant).is_some()
            })
        }) || pool.iter().any(|constant| {
            matches!(*constant, Constant::MethodHandle { reference_index, .. }
                if pool.get(reference_index).is_ok_and(|target| guard.symbolic_guard_ref(group, pool, target).is_some()))
                || guard.symbolic_guard_ref(group, pool, constant).is_some_and(|symbol| symbol != owner)
        }) {
            return None;
        }
        for method in &class.methods {
            let name = pool.utf8(method.name_index).ok()?;
            let descriptor = pool.utf8(method.descriptor_index).ok()?;
            let Some(code) = method.code(pool).ok()? else {
                continue;
            };
            let instructions = decode(code.bytes).ok()?;
            let mut graph = None;
            let mut ignored_use = None;
            if name == "<clinit>" && descriptor == "()V" {
                if guard.initializer != 0 || method.access_flags & 0x0008 == 0 {
                    return None;
                }
                let init_graph = ControlFlowGraph::build(&instructions, &code.exceptions).ok()?;
                ignored_use = Some(guard.prove_initializer(
                    pool,
                    status_owner,
                    &instructions,
                    &init_graph,
                )?);
                graph = Some(init_graph);
                guard.initializer = 7;
            }
            let uses = guard.count_uses(pool, &instructions, ignored_use);
            if uses != 0 {
                let graph = match graph {
                    Some(graph) => graph,
                    None => ControlFlowGraph::build(&instructions, &code.exceptions).ok()?,
                };
                guard.record_method(pool, method, &code, &instructions, &graph, uses)?;
            }
        }
        (guard.initializer != 0 && !guard.methods.is_empty()).then_some(guard)
    }

    fn record_method(
        &mut self,
        pool: &ConstantPool<'_>,
        method: &Member<'_>,
        code: &Code<'_>,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        uses: usize,
    ) -> Option<()> {
        // Inlined lambda helper bodies are structured separately.
        if synthetic(pool, method) {
            return None;
        }
        let sites = Sites::scan(pool, self, instructions, graph);
        let reachable = graph.reachable();
        if !sites.covers(uses) || sites.by_head.keys().any(|&head| !reachable[head]) {
            return None;
        }
        for visible in [true, false] {
            if code
                .type_annotations(pool, visible)
                .ok()?
                .iter()
                .any(|annotation| {
                    let (TypeTarget::Offset { offset, .. }
                    | TypeTarget::TypeArgument { offset, .. }) = &annotation.target
                    else {
                        return false;
                    };
                    sites.failure_blocks.iter().any(|&block| {
                        let range = &graph.blocks[block].instructions;
                        u32::from(*offset) == instructions[range.start].offset
                            || u32::from(*offset) == instructions[range.end - 2].offset
                    })
                })
            {
                return None;
            }
        }
        self.methods
            .insert((method.name_index, method.descriptor_index), uses);
        Some(())
    }

    pub(crate) fn hides_field(&self, name: &str, descriptor: &str) -> bool {
        self.declares_field && name == self.field && descriptor == "Z"
    }

    pub(crate) fn initializer_prefix(&self, name: &str, descriptor: &str) -> usize {
        if name == "<clinit>" && descriptor == "()V" {
            self.initializer
        } else {
            0
        }
    }

    fn is_field_ref(&self, pool: &ConstantPool<'_>, index: u16) -> bool {
        matches!(pool.get(index), Ok(Constant::Fieldref { .. }))
            && pool.member_ref(index).ok() == Some((self.owner, self.field, "Z"))
    }

    fn symbolic_guard_ref<'p>(
        &self,
        group: &ClassGroup<'_>,
        pool: &'p ConstantPool<'_>,
        constant: &Constant<'_>,
    ) -> Option<&'p str> {
        let Constant::Fieldref {
            class_index,
            name_and_type_index,
        } = *constant
        else {
            return None;
        };
        if pool.name_and_type(name_and_type_index).ok()? != (self.field, "Z") {
            return None;
        }
        let symbol = pool.class_name(class_index).ok()?;
        let mut owner = symbol;
        // A Fieldref may name a subclass rather than the class that declares
        // the field. Do not remove a field that such a reference can resolve.
        for _ in 0..128 {
            if owner == self.owner {
                return Some(symbol);
            }
            if owner == "java/lang/Object" {
                return None;
            }
            let Some(class) = group.get(owner) else {
                return Some(symbol);
            };
            if class.fields.iter().any(|field| {
                class.pool.utf8(field.name_index).ok() == Some(self.field)
                    && class.pool.utf8(field.descriptor_index).ok() == Some("Z")
            }) || class.super_class == 0
            {
                return None;
            }
            owner = class.pool.class_name(class.super_class).ok()?;
        }
        Some(symbol)
    }

    fn count_uses(
        &self,
        pool: &ConstantPool<'_>,
        instructions: &[Instruction],
        ignore: Option<u32>,
    ) -> usize {
        instructions.iter().filter(|op| {
            matches!(op.opcode, 0xb2..=0xb5)
                && matches!(op.operand, Operand::Constant(index) if self.is_field_ref(pool, index))
                && Some(op.offset) != ignore
        }).count()
    }

    fn prove_initializer(
        &self,
        pool: &ConstantPool<'_>,
        status_owner: &str,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
    ) -> Option<u32> {
        let ([owner, status, test, disabled, jump, enabled, store], rest) =
            instructions.split_first_chunk::<7>()?;
        if rest.is_empty()
            || !matches!(owner.opcode, 0x12 | 0x13)
            || !matches!(owner.operand, Operand::Constant(index) if pool.class_name(index).ok() == Some(status_owner))
            || method_ref(pool, status, 0xb6)?
                != ("java/lang/Class", "desiredAssertionStatus", "()Z")
            || test.opcode != 0x9a
            || test.operand != Operand::Branch(enabled.offset)
            || disabled.opcode != 0x04
            || enabled.opcode != 0x03
            || !matches!(jump.opcode, 0xa7 | 0xc8)
            || jump.operand != Operand::Branch(store.offset)
            || store.opcode != 0xb3
            || !matches!(store.operand, Operand::Constant(index) if self.is_field_ref(pool, index))
        {
            return None;
        }
        let [entry, no, yes, assign, ..] = &graph.blocks[..] else {
            return None;
        };
        if entry.instructions != (0..3)
            || no.instructions != (3..5)
            || yes.instructions != (5..6)
            || assign.instructions.start != 6
            || !entry.predecessors.is_empty()
            || no.predecessors.as_slice() != [0]
            || yes.predecessors.as_slice() != [0]
            || assign.predecessors.as_slice() != [1, 2]
            || graph.blocks[..4].iter().any(|block| {
                !block.exception_predecessors.is_empty() || !block.exception_successors.is_empty()
            })
        {
            return None;
        }
        Some(store.offset)
    }
}

fn canonical_guard_field(class: &ClassFile<'_>, field: &Member<'_>) -> bool {
    is_guard_field(class, field)
        && field.access_flags & STATIC_FINAL == STATIC_FINAL
        && field.access_flags & (0x0001 | 0x0004) == 0
        && field
            .attributes
            .iter()
            .all(|attr| class.pool.utf8(attr.name_index).ok() == Some("Synthetic"))
}

/// Preserve recognizable assertion fields when decompilation is disabled or
/// the class-wide proof fails, even under generic synthetic-field pruning.
pub(crate) fn is_guard_field(class: &ClassFile<'_>, field: &Member<'_>) -> bool {
    let pool = &class.pool;
    pool.utf8(field.descriptor_index).ok() == Some("Z")
        && pool.utf8(field.name_index).is_ok_and(|name| {
            name.strip_prefix("$assertionsDisabled")
                .is_some_and(|suffix| suffix.bytes().all(|byte| byte.is_ascii_digit()))
        })
        && synthetic(pool, field)
}

fn package(name: &str) -> &str {
    name.rsplit_once('/').map_or("", |(package, _)| package)
}

fn synthetic(pool: &ConstantPool<'_>, member: &Member<'_>) -> bool {
    member.access_flags & SYNTHETIC != 0
        || find_attribute(&member.attributes, pool, "Synthetic").is_ok_and(|value| value.is_some())
}

fn method_ref<'p>(
    pool: &'p ConstantPool<'_>,
    op: &Instruction,
    opcode: u8,
) -> Option<(&'p str, &'p str, &'p str)> {
    let Operand::Constant(index) = op.operand else {
        return None;
    };
    if op.opcode != opcode || !matches!(pool.get(index), Ok(Constant::Methodref { .. })) {
        return None;
    }
    pool.member_ref(index).ok()
}

/// Evidence extracted from the original CFG before the structurer can merge
/// compiler-generated tests with neighboring source conditions.
pub(crate) struct Sites {
    by_head: BTreeMap<usize, Site>,
    failure_blocks: BTreeSet<usize>,
}

struct Site {
    guard: usize,
    continuation: usize,
    tests: Vec<Test>,
    failure: usize,
    detail: &'static str,
}

struct Test {
    block: usize,
    taken: bool,
    combine: Option<&'static str>,
}

impl Sites {
    pub(crate) fn for_method(
        class: &ClassFile<'_>,
        method: &Member<'_>,
        guard: &Guard<'_>,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
    ) -> Result<Option<Self>, StructureError> {
        let Some(&count) = guard
            .methods
            .get(&(method.name_index, method.descriptor_index))
        else {
            return Ok(None);
        };
        let sites = Self::scan(&class.pool, guard, instructions, graph);
        if sites.covers(count) {
            Ok(Some(sites))
        } else {
            Err(StructureError::Assertion)
        }
    }

    pub(super) fn starts(&self, head: usize) -> bool {
        self.by_head.contains_key(&head)
    }

    pub(super) fn is_failure_block(&self, block: usize) -> bool {
        self.failure_blocks.contains(&block)
    }

    pub(super) fn all_emitted(&self, emitted: &[bool]) -> bool {
        self.by_head.values().all(|site| emitted[site.failure])
    }

    fn covers(&self, uses: usize) -> bool {
        self.by_head.len() == uses && self.failure_blocks.len() == uses
    }

    fn scan(
        pool: &ConstantPool<'_>,
        guard: &Guard<'_>,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
    ) -> Self {
        let by_head: BTreeMap<_, _> = (0..graph.blocks.len())
            .filter_map(|head| {
                Site::prove(pool, guard, instructions, graph, head).map(|site| (head, site))
            })
            .collect();
        let failure_blocks = by_head.values().map(|site| site.failure).collect();
        Self {
            by_head,
            failure_blocks,
        }
    }
}

impl Site {
    fn prove(
        pool: &ConstantPool<'_>,
        guard: &Guard<'_>,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        head: usize,
    ) -> Option<Self> {
        let head_block = &graph.blocks[head];
        let [.., load, skip] = &instructions[head_block.instructions.clone()] else {
            return None;
        };
        let [continuation, entry] = *head_block.successors.as_slice() else {
            return None;
        };
        if load.opcode != 0xb2
            || !matches!(load.operand, Operand::Constant(index) if guard.is_field_ref(pool, index))
            || skip.opcode != 0x9a
            || continuation <= entry
        {
            return None;
        }
        let failure = continuation - 1;
        let failure_block = &graph.blocks[failure];
        let detail = assertion_error(pool, &instructions[failure_block.instructions.clone()])?;
        if !failure_block.successors.is_empty() {
            return None;
        }

        let mut tests = Vec::new();
        let mut current = entry;
        let mut predecessor = head;
        loop {
            if current == failure {
                break;
            }
            let node = &graph.blocks[current];
            if current <= predecessor
                || current >= failure
                || node.predecessors.as_slice() != [predecessor]
                || !node.exception_predecessors.is_empty()
                || node.exception_successors != head_block.exception_successors
                || tests.len() >= 128
            {
                return None;
            }
            if !matches!(
                instructions[node.instructions.end - 1].opcode,
                0x99..=0xa6 | 0xc6 | 0xc7
            ) {
                return None;
            }
            let [taken, fallthrough] = *node.successors.as_slice() else {
                return None;
            };
            let (polarity, combine, next) = match (taken, fallthrough) {
                (a, b) if a == continuation && b == failure => (true, None, failure),
                (a, b) if a == failure && b == continuation => (false, None, failure),
                (a, b) if a == continuation => (true, Some("||"), b),
                (a, b) if b == continuation => (false, Some("||"), a),
                (a, b) if a == failure => (false, Some("&&"), b),
                (a, b) if b == failure => (true, Some("&&"), a),
                _ => return None,
            };
            tests.push(Test {
                block: current,
                taken: polarity,
                combine,
            });
            predecessor = current;
            current = next;
        }
        if !failure_block.exception_predecessors.is_empty()
            || failure_block.exception_successors != head_block.exception_successors
            || failure_block
                .predecessors
                .iter()
                .any(|&block| block != head && !tests.iter().any(|test| test.block == block))
        {
            return None;
        }
        Some(Self {
            guard: head_block.instructions.end - 2,
            continuation,
            tests,
            failure,
            detail,
        })
    }
}

fn assertion_error(pool: &ConstantPool<'_>, instructions: &[Instruction]) -> Option<&'static str> {
    let [new, dup, message @ .., init, throw] = instructions else {
        return None;
    };
    if new.opcode != 0xbb
        || !matches!(new.operand, Operand::Constant(index) if pool.class_name(index).ok() == Some(ERROR))
        || dup.opcode != 0x59
        || throw.opcode != 0xbf
    {
        return None;
    }
    let (ERROR, "<init>", descriptor) = method_ref(pool, init, 0xb7)? else {
        return None;
    };
    match descriptor {
        "()V" if message.is_empty() => Some("()V"),
        "(Z)V" => Some("(Z)V"),
        "(C)V" => Some("(C)V"),
        "(I)V" => Some("(I)V"),
        "(J)V" => Some("(J)V"),
        "(F)V" => Some("(F)V"),
        "(D)V" => Some("(D)V"),
        "(Ljava/lang/Object;)V" => Some("(Ljava/lang/Object;)V"),
        _ => None,
    }
}

impl Emitter<'_> {
    pub(super) fn assertion_starts(&self, block: usize) -> bool {
        self.assertions.is_some_and(|sites| sites.starts(block))
    }

    pub(super) fn emit_assertion<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let Some(site) = self.assertions.and_then(|sites| sites.by_head.get(&block)) else {
            return Ok(None);
        };
        let owned = |block: usize| {
            !self.emitted[block]
                && self.exceptions.contains(region.exception_arm, block)
                && self
                    .exceptions
                    .at_start(region.exception_arm, block)
                    .is_none()
                && self.graph.blocks[block]
                    .instructions
                    .clone()
                    .all(|index| !self.exceptions.skips_instruction(index))
        };
        if !machine.stack_is_empty()
            || !machine.this_is_initialized()
            || !owned(site.failure)
            || !site.tests.iter().all(|test| owned(test.block))
        {
            return Err(StructureError::Assertion);
        }
        let mut assert_offsets = Vec::new();
        let mut conditions = Vec::with_capacity(site.tests.len());
        let mut along = machine.clone();
        for test in &site.tests {
            let ops = &self.instructions[self.graph.blocks[test.block].instructions.clone()];
            let Some((branch, operands)) = ops.split_last() else {
                return Err(StructureError::Assertion);
            };
            for op in operands {
                if !matches!(along.step(op), Ok(Effect::None)) || !along.take_prelude().is_empty() {
                    return Err(StructureError::Assertion);
                }
            }
            let Ok(Effect::Branch {
                when_true,
                when_false,
                ..
            }) = along.step(branch)
            else {
                return Err(StructureError::Assertion);
            };
            if !along.stack_is_empty()
                || !along.same_locals(machine)
                || !along.take_prelude().is_empty()
            {
                return Err(StructureError::Assertion);
            }
            conditions.push((
                if test.taken { when_true } else { when_false },
                test.combine,
            ));
            assert_offsets.extend(ops.iter().flat_map(offsets_of));
        }
        let condition = conditions
            .into_iter()
            .rev()
            .fold(None::<String>, |suffix, (expr, combine)| {
                Some(match (combine, suffix) {
                    (Some(op), Some(right)) => logical(&expr, op, &right),
                    (None, None) => expr,
                    _ => unreachable!("proven assertion test chain"),
                })
            })
            .unwrap_or_else(|| "false".into());

        let mut failure = along;
        let ops = &self.instructions[self.graph.blocks[site.failure].instructions.clone()];
        let [prefix @ .., constructor, _] = ops else {
            unreachable!("proven assertion throw")
        };
        for op in prefix {
            if !matches!(failure.step(op), Ok(Effect::None)) || !failure.take_prelude().is_empty() {
                return Err(StructureError::Assertion);
            }
        }
        let detail = failure
            .take_assertion_detail(constructor, prefix[0].offset, site.detail)
            .map_err(|_| StructureError::Assertion)?;
        if !failure.same_locals(machine) {
            return Err(StructureError::Assertion);
        }
        assert_offsets.extend(prefix[2..].iter().flat_map(offsets_of));
        // The synthetic guard, allocation and athrow have no source token.
        // The condition's inversion inherits invokespecial's upstream mapping.
        if !site.tests.is_empty() {
            assert_offsets.extend(offsets_of(constructor));
        }
        let guard = self.instructions[site.guard].offset;
        let guard_end =
            self.instructions[site.guard + 1].offset + self.instructions[site.guard + 1].len;
        offsets.retain(|&offset| !(guard..guard_end).contains(&offset));
        offsets.extend(assert_offsets);
        for test in &site.tests {
            self.emitted[test.block] = true;
        }
        self.emitted[site.failure] = true;
        let mut text = format!("assert {condition}");
        if let Some(detail) = detail {
            text.push_str(" : ");
            text.push_str(&detail);
        }
        text.push(';');
        self.push(depth, text, mem::take(offsets));
        Ok(Some(site.continuation))
    }
}

fn offsets_of(op: &Instruction) -> std::ops::Range<u32> {
    op.offset..op.offset + op.len
}
