// Based on Vineflower InitializerProcessor (Apache-2.0).
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
    rc::Rc,
};

use crate::{
    bytecode::{Instruction, Operand, decode},
    classfile::{Code, Member, find_attribute},
    context::NestedKind,
    descriptor::MethodDescriptor,
    lift::{DynamicHelpers, Effect, Machine},
    source_text::Document,
};

use super::{DecompileError, FINAL, INTERFACE, MethodMap, STATIC, SYNTHETIC, Writer, parse};

mod boolean;

#[cfg(test)]
mod tests;

type FieldKey = (u16, u16);
type MethodKey<'c> = (&'c str, &'c str);
type FieldTable<'c> = BTreeMap<(&'c str, &'c str), Field>;

#[derive(Default)]
pub(super) struct FieldInitializers<'c> {
    declarations: BTreeMap<FieldKey, Declaration>,
    methods: BTreeMap<MethodKey<'c>, MovedCode>,
}

struct Declaration {
    expression: Document,
    source_line: Option<usize>,
}

struct MovedCode {
    bytes: Range<u32>,
    mappings: Vec<(FieldKey, Vec<u32>)>,
    original_lines: Vec<(u16, u16)>,
}

#[derive(Clone, Copy)]
struct Field {
    key: FieldKey,
    index: usize,
    flags: u16,
    visible: bool,
    constant: bool,
    declaration_candidate: bool,
}

struct Assignment {
    field: FieldKey,
    instructions: Range<usize>,
    materialization: Option<Range<u32>>,
    expression: Document,
    helpers: BTreeSet<(u16, u16)>,
}

struct Prefix<'c> {
    method: MethodKey<'c>,
    instructions: Vec<Instruction>,
    start: usize,
    assignments: Vec<Assignment>,
    original_lines: Vec<(u16, u16)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Interface,
    Static,
    Instance,
}

enum Scan<'c> {
    Unavailable,
    Delegating,
    Prefix(Prefix<'c>),
}

impl FieldInitializers<'_> {
    pub(super) fn expression(&self, field: &Member<'_>) -> Option<&Document> {
        self.declarations
            .get(&field_key(field))
            .map(|decl| &decl.expression)
    }

    pub(super) fn record_line(&mut self, field: &Member<'_>, source_line: usize) {
        if let Some(decl) = self.declarations.get_mut(&field_key(field)) {
            decl.source_line = Some(source_line);
        }
    }

    pub(super) fn strip(&self, name: &str, descriptor: &str, code: &mut Vec<Instruction>) {
        if let Some(moved) = self.methods.get(&(name, descriptor)) {
            let start = code.partition_point(|op| op.offset < moved.bytes.start);
            let end = code.partition_point(|op| op.offset < moved.bytes.end);
            code.drain(start..end);
        }
    }

    pub(super) fn finish(self, writer: &mut Writer<'_, '_>) -> Result<(), DecompileError> {
        if self.methods.is_empty() {
            return Ok(());
        }
        if self
            .declarations
            .values()
            .any(|decl| decl.source_line.is_none())
        {
            return Err(DecompileError::Unsupported {
                feature: "recovered initializer for a hidden field",
            });
        }
        for ((name, descriptor), moved) in self.methods.into_iter().rev() {
            let offsets = moved.mappings.into_iter().flat_map(|(field, offsets)| {
                let line = self.declarations[&field].source_line.expect("verified field line");
                offsets.into_iter().map(move |offset| (offset, line))
            });
            let order = if name == "<init>" {
                InitializerMapOrder::ClassDeclarations
            } else {
                InitializerMapOrder::Retained
            };
            merge_initializer_mapping(
                writer, name, descriptor, offsets, moved.original_lines, order,
            );
        }
        Ok(())
    }
}

pub(super) enum InitializerMapOrder {
    Retained,
    ClassDeclarations,
}

/// Join bytecode now rendered in a declaration with any remaining code in
/// the original method. Both fragments use the method's original line table.
pub(super) fn merge_initializer_mapping(
    writer: &mut Writer<'_, '_>,
    name: &str,
    descriptor: &str,
    offsets: impl IntoIterator<Item = (u32, usize)>,
    original: Vec<(u16, u16)>,
    order: InitializerMapOrder,
) {
    let Some(mapping) = &mut writer.mapping else { return };
    let mut offsets = offsets.into_iter().peekable();
    if offsets.peek().is_none() {
        return;
    }
    let owner = writer.owner;
    let source_name = writer.names.renames().method_alias(owner, name, descriptor).unwrap_or(name);
    let index = mapping.methods.iter().position(|map| {
        map.class_name == owner && map.name == source_name && map.descriptor == descriptor
    });
    let mut map = index.map_or_else(
        || MethodMap {
            class_name: owner.into(),
            name: source_name.into(),
            descriptor: descriptor.into(),
            offsets: BTreeMap::new(),
        },
        |index| mapping.methods.swap_remove(index),
    );
    map.offsets.extend(offsets);
    mapping.add(map, original);
    let end = mapping.methods.len() - 1;
    let index = if let Some(index) = index {
        mapping.methods.swap(index, end);
        index
    } else {
        end
    };
    if matches!(order, InitializerMapOrder::ClassDeclarations)
        && let Some(first) = mapping.methods[..index].iter().position(|map| map.class_name == owner)
    {
        mapping.methods[first..=index].rotate_right(1);
    }
    mapping.unmapped_lines.retain(|line| !mapping.original_lines.contains_key(line));
}

impl<'c> Writer<'_, 'c> {
    pub(super) fn field_initializers(
        &self,
        emit_fields: bool,
        special_class: bool,
    ) -> Result<FieldInitializers<'c>, DecompileError> {
        let mut recovered = FieldInitializers::default();
        let is_interface = self.flags & INTERFACE != 0;
        if !emit_fields || special_class || (!is_interface && self.class.fields.is_empty()) {
            return Ok(recovered);
        }
        let class = self.class;
        let pool = &class.pool;
        let mut fields = FieldTable::new();
        let mut interface_fields = Vec::new();
        for (index, field) in self.class.fields.iter().enumerate() {
            let key = field_key(field);
            let name = pool.utf8(key.0)?;
            let descriptor = pool.utf8(key.1)?;
            let constant = find_attribute(&field.attributes, pool, "ConstantValue")?.is_some();
            let flags = field.access_flags;
            if is_interface {
                if flags & (STATIC | FINAL) != (STATIC | FINAL) {
                    return Err(unsupported_interface());
                }
                if !constant {
                    interface_fields.push(key);
                }
            }
            let visible = !self.hidden_field(field)?
                && (!self.has_lexical_owner()
                    || self
                        .group
                        .outer_field(self.owner, name, descriptor)
                        .is_none());
            let synthetic = flags & SYNTHETIC != 0
                || find_attribute(&field.attributes, pool, "Synthetic")?.is_some();
            let assertion_scaffold = flags & (STATIC | FINAL) == STATIC | FINAL
                && crate::structure::assertions::has_guard_shape(class, field);
            fields.insert(
                (name, descriptor),
                Field {
                    key,
                    index,
                    flags,
                    visible,
                    constant,
                    declaration_candidate: !assertion_scaffold && (is_interface || !synthetic),
                },
            );
        }

        let mut class_init = None;
        let mut constructors = Vec::new();
        for method in &self.class.methods {
            let name = pool.utf8(method.name_index)?;
            if name == "<clinit>" {
                if class_init.replace(method).is_some() {
                    return if is_interface {
                        Err(unsupported_interface())
                    } else {
                        Ok(recovered)
                    };
                }
            } else if name == "<init>" && !is_interface {
                constructors.push(method);
            }
        }

        if is_interface {
            if let Some(method) = class_init {
                let Scan::Prefix(prefix) =
                    self.scan_initializers(method, &fields, Mode::Interface, usize::MAX)?
                else {
                    return Err(unsupported_interface());
                };
                let end = prefix
                    .assignments
                    .last()
                    .map_or(prefix.start, |value| value.instructions.end);
                if !prefix
                    .assignments
                    .iter()
                    .map(|value| value.field)
                    .eq(interface_fields)
                    || !prefix.instructions[end..]
                        .split_last()
                        .is_some_and(|(last, nops)| {
                            last.opcode == 0xb1 && nops.iter().all(|op| op.opcode == 0)
                        })
                {
                    return Err(unsupported_interface());
                }
                let count = prefix.assignments.len();
                self.keep_initializers(&mut recovered, prefix, count, Mode::Interface, true);
            } else if !interface_fields.is_empty() {
                return Err(unsupported_interface());
            }
            return Ok(recovered);
        }

        if let Some(method) = class_init
            && let Scan::Prefix(prefix) =
                self.scan_initializers(method, &fields, Mode::Static, usize::MAX)?
        {
            let count = prefix.assignments.len();
            self.keep_initializers(&mut recovered, prefix, count, Mode::Static, true);
        }
        if !fields
            .values()
            .any(|field| field.flags & STATIC == 0 && field.visible)
            || (self.has_lexical_owner()
                && self
                    .group
                    .nested_class(self.owner)
                    .is_some_and(|node| !matches!(node.kind, NestedKind::Member(_))))
        {
            return Ok(recovered);
        }

        let mut roots: Vec<Prefix<'c>> = Vec::new();
        let mut common = usize::MAX;
        for method in constructors {
            match self.scan_initializers(method, &fields, Mode::Instance, common)? {
                Scan::Unavailable => return Ok(recovered),
                Scan::Delegating => {}
                Scan::Prefix(prefix) => {
                    common = common.min(prefix.assignments.len());
                    if let Some(first) = roots.first() {
                        common = (0..common)
                            .take_while(|&index| first.same_assignment(&prefix, index))
                            .count();
                    }
                    if common == 0 {
                        return Ok(recovered);
                    }
                    roots.push(prefix);
                }
            }
        }
        for (index, prefix) in roots.into_iter().enumerate() {
            self.keep_initializers(&mut recovered, prefix, common, Mode::Instance, index == 0);
        }
        Ok(recovered)
    }

    fn scan_initializers(
        &self,
        method: &Member<'_>,
        fields: &FieldTable<'c>,
        mode: Mode,
        max_assignments: usize,
    ) -> Result<Scan<'c>, DecompileError> {
        let class = self.class;
        let pool = &class.pool;
        let name = pool.utf8(method.name_index)?;
        let descriptor = pool.utf8(method.descriptor_index)?;
        if mode != Mode::Instance && descriptor != "()V" {
            return Ok(Scan::Unavailable);
        }
        if self.hidden(method)?
            || (self.options.decompile_inner
                && self.group.children(self.owner).any(|(_, node)| {
                    matches!(node.kind, NestedKind::Local(_))
                        && node.method.as_ref().is_some_and(|(enclosing, desc)| {
                            enclosing == name && desc == descriptor
                        })
                }))
        {
            return Ok(Scan::Unavailable);
        }
        let Some(code) = method.code(pool)? else {
            return Ok(Scan::Unavailable);
        };
        if mode == Mode::Interface && !code.exceptions.is_empty() {
            return Ok(Scan::Unavailable);
        }
        let Ok(instructions) = decode(code.bytes) else {
            return Ok(Scan::Unavailable);
        };
        let interface_prefix = if mode == Mode::Interface {
            self.assertion_guard()
                .map_or(0, |guard| guard.initializer_prefix(name, descriptor))
        } else {
            0
        };
        let Some(body) = instructions.get(interface_prefix..) else {
            return Ok(Scan::Unavailable);
        };
        let Some(limit) = first_boundary(body, &code) else {
            return Ok(Scan::Unavailable);
        };
        let end = instructions.partition_point(|op| op.offset < limit);
        let descriptor_type = parse(descriptor, MethodDescriptor::parse)?;
        let render = |name: &str| self.names.render(name);
        let Ok(machine) = Machine::new(
            self.class,
            method,
            &code,
            &descriptor_type,
            self.options,
            &render,
        ) else {
            return Ok(Scan::Unavailable);
        };
        let mut machine = machine.with_group(self.group);
        machine.set_member_renames(self.names.renames());
        let helpers = DynamicHelpers::default();
        machine.set_dynamic_helpers(Rc::clone(&helpers));

        let mut start = interface_prefix;
        if mode == Mode::Instance {
            if machine.this_is_initialized() {
                return Ok(Scan::Unavailable);
            }
            let mut chained = false;
            let mut index = 0;
            while index < end {
                let op = &instructions[index];
                // Pre-super statements (including synthetic captures) are not a
                // source instance-initializer boundary. Only lift the call itself.
                if !expression_opcode(op.opcode) || matches!(op.opcode, 0xb3 | 0xb5) {
                    break;
                }
                if matches!(op.opcode, 0xbc | 0xbd)
                    && let Some(consumed) =
                        machine.try_array_initializer(&instructions[index..end], |_, _| true)
                {
                    index += consumed;
                    continue;
                }
                let Ok(effect) = machine.step(op) else { break };
                if !machine.take_prelude().is_empty() {
                    break;
                }
                if matches!(effect, Effect::None) {
                    index += 1;
                    continue;
                }
                if matches!(effect, Effect::Statement(_))
                    && machine.this_is_initialized()
                    && machine.stack_is_empty()
                    && let (0xb7, Operand::Constant(member)) = (op.opcode, &op.operand)
                {
                    let (owner, target, _) = pool.member_ref(*member)?;
                    if target == "<init>" {
                        if owner == self.owner {
                            return Ok(Scan::Delegating);
                        }
                        // The lifter checks the receiver and direct superclass.
                        start = index + 1;
                        chained = true;
                    }
                }
                break;
            }
            if !chained {
                return Ok(Scan::Unavailable);
            }
            helpers.borrow_mut().clear();
        }

        let expected_store = if mode == Mode::Instance { 0xb5 } else { 0xb3 };
        let mut assignments = Vec::new();
        let mut previous_field = None;
        let can_read_fields = |op: &Instruction| -> Result<bool, DecompileError> {
            if mode != Mode::Interface
                && let (0xb2 | 0xb4, Operand::Constant(member)) = (op.opcode, &op.operand)
            {
                let (owner, name, descriptor) = pool.member_ref(*member)?;
                if owner == self.owner
                    && fields
                        .get(&(name, descriptor))
                        .is_some_and(|field| !field.visible)
                {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        let mut index = start;
        let mut materialization = None;
        while index < end {
            let op = &instructions[index];
            if let Some(tail) = boolean::BooleanTail::read(&instructions[index..end]) {
                let Operand::Constant(member) = tail.store.operand else {
                    break;
                };
                if tail.store.opcode != expected_store || pool.member_ref(member)?.2 != "Z" {
                    break;
                }
                materialization = tail.lift(&mut machine, instructions[start].offset);
                if materialization.is_none() {
                    break;
                }
                index += boolean::BooleanTail::STORE_INDEX;
                continue;
            }
            if !expression_opcode(op.opcode)
                || !initializer_local_access(op, mode)
                || !can_read_fields(op)?
            {
                break;
            }
            if matches!(op.opcode, 0xbc | 0xbd)
                && let Some(consumed) =
                    machine.try_array_initializer(&instructions[index..end], |_, op| {
                        initializer_local_access(op, mode) && can_read_fields(op).unwrap_or(false)
                    })
            {
                index += consumed;
                continue;
            }
            let field = if matches!(op.opcode, 0xb3 | 0xb5) {
                if op.opcode != expected_store
                    || (mode == Mode::Instance && !machine.field_receiver_is_this())
                {
                    break;
                }
                let Operand::Constant(member) = op.operand else {
                    break;
                };
                let (owner, field_name, field_type) = pool.member_ref(member)?;
                let Some(field) = fields.get(&(field_name, field_type)).filter(|field| {
                    owner == self.owner
                        && field.visible
                        && !field.constant
                        && (field.flags & STATIC != 0) == (mode != Mode::Instance)
                        && field.declaration_candidate
                        && previous_field.is_none_or(|previous| field.index > previous)
                }) else {
                    break;
                };
                if mode != Mode::Interface
                    && field.flags & FINAL != 0
                    && could_be_constant_variable(field_type)
                    && !self.definitely_nonconstant(&instructions[start..index], fields)?
                {
                    // Don't turn a runtime assignment into a constant variable:
                    // javac could inline its uses or initialize it before <clinit>.
                    break;
                }
                Some(field)
            } else {
                None
            };
            let Ok(effect) = machine.step(op) else { break };
            if !machine.take_prelude().is_empty() {
                break;
            }
            match (field, effect) {
                (None, Effect::None) => {}
                (Some(field), Effect::FieldAssignment { value, .. })
                    if machine.stack_is_empty() =>
                {
                    assignments.push(Assignment {
                        field: field.key,
                        instructions: start..index + 1,
                        materialization: materialization.take(),
                        expression: value,
                        helpers: std::mem::take(&mut *helpers.borrow_mut()),
                    });
                    start = index + 1;
                    previous_field = Some(field.index);
                    if assignments.len() == max_assignments {
                        break;
                    }
                }
                // A block that remains after the declarations must never move
                // ahead of an extracted assignment, even to a different field.
                _ => break,
            }
            index += 1;
        }
        let original_lines = if self.mapping.is_some() && !assignments.is_empty() {
            code.line_numbers(pool)?
        } else {
            Vec::new()
        };
        Ok(Scan::Prefix(Prefix {
            method: (name, descriptor),
            instructions,
            start: interface_prefix,
            assignments,
            original_lines,
        }))
    }

    fn definitely_nonconstant(
        &self,
        instructions: &[Instruction],
        fields: &FieldTable<'c>,
    ) -> Result<bool, DecompileError> {
        let pool = &self.class.pool;
        for op in instructions {
            match (op.opcode, &op.operand) {
                (0x2e..=0x35 | 0xb4 | 0xbe, _) => return Ok(true),
                (0xb2, Operand::Constant(member)) => {
                    let (owner, name, descriptor) = pool.member_ref(*member)?;
                    if owner == self.owner
                        && fields
                            .get(&(name, descriptor))
                            .is_some_and(|field| field.flags & FINAL == 0 || !field.constant)
                    {
                        return Ok(true);
                    }
                }
                (0xb6..=0xb8, Operand::Constant(member))
                | (0xb9, Operand::InvokeInterface { index: member, .. }) => {
                    let (owner, name, _) = pool.member_ref(*member)?;
                    // The lifter can rewrite these calls as expressions which
                    // could contain only constant variables/literals.
                    if !matches!(owner, "java/lang/StringBuilder" | "java/lang/StringBuffer")
                        && !(owner == "java/lang/String" && name == "valueOf")
                        && !name.starts_with("access$")
                        && name != "<init>"
                    {
                        return Ok(true);
                    }
                }
                _ => {}
            }
        }
        Ok(false)
    }

    fn keep_initializers(
        &self,
        plan: &mut FieldInitializers<'c>,
        prefix: Prefix<'c>,
        count: usize,
        mode: Mode,
        declare: bool,
    ) {
        if count == 0 {
            return;
        }
        let first = prefix.assignments[0].instructions.start;
        let last = prefix.assignments[count - 1].instructions.end - 1;
        let last = &prefix.instructions[last];
        let mut moved = MovedCode {
            bytes: prefix.instructions[first].offset..last.offset + last.len,
            mappings: Vec::new(),
            original_lines: prefix.original_lines,
        };
        for assignment in prefix.assignments.into_iter().take(count) {
            if self.mapping.is_some() {
                let mut body = &prefix.instructions[assignment.instructions];
                if mode != Mode::Static {
                    // A declaration has no explicit putfield/putstatic.
                    body = &body[..body.len() - 1];
                }
                let receiver = (mode == Mode::Instance
                    && !body.iter().any(|op| matches!(op.opcode, 0x59..=0x5e)))
                    .then(|| {
                        let mut loads = body.iter().filter(|op| loads_this(op));
                        let first = loads.next()?;
                        // The assignment proof has exactly `this, rhs` at
                        // the store. With one unaliased receiver load that
                        // load cannot participate in the moved expression.
                        loads.next().is_none().then_some(first.offset)
                    })
                    .flatten();
                moved.mappings.push((
                    assignment.field,
                    body.iter()
                        .filter(|op| {
                            op.opcode != 0
                                && receiver != Some(op.offset)
                                && assignment
                                    .materialization
                                    .as_ref()
                                    .is_none_or(|range| !range.contains(&op.offset))
                        })
                        .flat_map(|op| op.offset..op.offset + op.len)
                        .collect(),
                ));
            }
            if declare {
                self.dynamic_helpers.borrow_mut().extend(assignment.helpers);
                plan.declarations.insert(
                    assignment.field,
                    Declaration {
                        expression: assignment.expression,
                        source_line: None,
                    },
                );
            }
        }
        plan.methods.insert(prefix.method, moved);
    }
}

impl Prefix<'_> {
    fn same_assignment(&self, other: &Self, index: usize) -> bool {
        let left = &self.assignments[index];
        let right = &other.assignments[index];
        let former = &self.instructions[left.instructions.clone()];
        let latter = &other.instructions[right.instructions.clone()];
        left.field == right.field
            && former.len() == latter.len()
            && former.iter().zip(latter).all(|(a, b)| {
                a.opcode == b.opcode
                    && match (&a.operand, &b.operand) {
                        (Operand::Branch(a_target), Operand::Branch(b_target)) => {
                            i64::from(*a_target) - i64::from(a.offset)
                                == i64::from(*b_target) - i64::from(b.offset)
                        }
                        (left, right) => left == right,
                    }
            })
    }
}

fn field_key(field: &Member<'_>) -> FieldKey {
    (field.name_index, field.descriptor_index)
}

fn could_be_constant_variable(descriptor: &str) -> bool {
    descriptor.len() == 1 || descriptor == "Ljava/lang/String;"
}

fn expression_opcode(opcode: u8) -> bool {
    !matches!(opcode, 0x36..=0x4e | 0x84 | 0x99..=0xb1 | 0xbf | 0xc2..=0xc3 | 0xc6..=0xc9)
}

fn loads_this(op: &Instruction) -> bool {
    matches!((op.opcode, &op.operand), (0x19, Operand::Local(0)) | (0x2a, _))
}

fn initializer_local_access(op: &Instruction, mode: Mode) -> bool {
    match op.opcode {
        0x15..=0x2d => mode == Mode::Instance && loads_this(op),
        _ => true,
    }
}

fn first_boundary(instructions: &[Instruction], code: &Code<'_>) -> Option<u32> {
    // Only the two edges of a closed boolean materialization are internal.
    // Any other incoming edge or protected boundary stops prefix removal.
    let mut limit = u32::MAX;
    let mut index = 0;
    while let Some(op) = instructions.get(index) {
        if boolean::BooleanTail::read(&instructions[index..]).is_some() {
            index += boolean::BooleanTail::STORE_INDEX;
            continue;
        }
        index += 1;
        // Legacy subroutines have implicit jump targets in addition to the
        // explicit operands. Don't excise any instructions before normalizing.
        if matches!(op.opcode, 0xa8 | 0xa9 | 0xc9) {
            return None;
        }
        match &op.operand {
            Operand::Branch(target) => limit = limit.min(*target),
            Operand::Switch { default, cases } => {
                limit = limit.min(*default);
                for (_, target) in cases {
                    limit = limit.min(*target);
                }
            }
            _ => {}
        }
    }
    for handler in &code.exceptions {
        limit = limit.min(u32::from(
            handler.start_pc.min(handler.end_pc).min(handler.handler_pc),
        ));
    }
    Some(limit)
}

fn unsupported_interface() -> DecompileError {
    DecompileError::Unsupported {
        feature: "interface initialization not expressible as ordered field initializers",
    }
}
