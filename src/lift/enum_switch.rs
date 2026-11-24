// Based on Vineflower SwitchHelper (Apache-2.0).
// Copyright 2000-2020 JetBrains s.r.o.

//! Recover compiler enum translation tables, not arbitrary arrays indexed by ordinal.
//! A table is removed only if its entire initialization and every use are proved.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    ClassGroup,
    bytecode::{self, Instruction, Operand},
    classfile::{ClassFile, Constant, ConstantPool, ExceptionHandler, Member, find_attribute},
    context::NestedKind,
    descriptor::{MethodDescriptor, Type},
    source_text::Document,
};

use super::{Effect, LiftError, Machine, expr::Category};

const STATIC: u16 = 0x0008;
const FINAL: u16 = 0x0010;
const SYNTHETIC: u16 = 0x1000;
const ENUM: u16 = 0x4000;
const JAVAC_PREFIX: &str = "$SwitchMap$";
const ECLIPSE_PREFIX: &str = "$SWITCH_TABLE$";
const FIELD: &str = "[I";
const ACCESSOR: &str = "()[I";

type MemberRef<'a> = (&'a str, &'a str, &'a str);
type Method = (u16, u16);

#[derive(Default)]
pub(crate) struct Plan {
    classes: BTreeMap<String, ClassPlan>,
    tables: Vec<Table>,
}

#[derive(Default)]
struct ClassPlan {
    auxiliary: Option<bool>,
    fields: BTreeMap<String, bool>,
    accessors: BTreeMap<String, bool>,
    sites: BTreeMap<(Method, u32), Site>,
}

struct Table {
    enum_descriptor: String,
    auxiliary: bool,
    labels: BTreeMap<i32, String>,
}

#[derive(Clone, Copy)]
enum Site {
    Skip(usize),
    Switch(usize),
    Empty(usize),
}

impl Site {
    fn table(self) -> usize {
        match self {
            Self::Skip(table) | Self::Switch(table) | Self::Empty(table) => table,
        }
    }
}

pub(super) enum Action<'a> {
    Skip,
    Switch(&'a str),
    Empty(&'a str),
}

impl Plan {
    pub(crate) fn build(group: &ClassGroup<'_>) -> Self {
        let mut plan = Self::default();
        let mut maps = Vec::new();
        let mut auxiliaries = BTreeMap::new();
        for (owner, class) in group.sources() {
            if let Some(fields) = auxiliary_candidate(group, owner, class) {
                let visibility = plan.classes.entry(owner.into()).or_default();
                visibility.auxiliary = Some(false);
                for &name in &fields {
                    visibility.fields.insert(name.into(), false);
                }
                if let Some(tables) = javac_tables(group, owner, class, &fields) {
                    let start = maps.len();
                    maps.extend(tables);
                    auxiliaries.insert(owner, start..maps.len());
                }
            }
            for field in &class.fields {
                if let Some((name, FIELD)) = member_name(&class.pool, field)
                    && name.starts_with(ECLIPSE_PREFIX)
                {
                    plan.classes
                        .entry(owner.into())
                        .or_default()
                        .fields
                        .insert(name.into(), false);
                }
            }
            for method in &class.methods {
                let Some((name, ACCESSOR)) = member_name(&class.pool, method) else {
                    continue;
                };
                if !name.starts_with(ECLIPSE_PREFIX) {
                    continue;
                }
                plan.classes
                    .entry(owner.into())
                    .or_default()
                    .accessors
                    .insert(name.into(), false);
                if let Some(table) = eclipse_table(group, owner, class, method, name) {
                    maps.push(table);
                }
            }
        }
        if maps.is_empty() {
            return plan;
        }

        let mut references = BTreeMap::new();
        for (id, map) in maps.iter().enumerate() {
            references.insert((map.owner, map.name, FIELD), id);
            if map.initializer != ("<clinit>", "()V") {
                references.insert((map.owner, map.name, ACCESSOR), id);
            }
        }
        let mut claims: Vec<_> = (0..maps.len()).map(|_| Claims::default()).collect();
        let source: BTreeSet<_> = group.sources().map(|(owner, _)| owner).collect();
        for (owner, class) in group.classes() {
            collect_uses(
                owner,
                class,
                source.contains(owner),
                &maps,
                &references,
                &auxiliaries,
                &mut claims,
            );
        }
        for (owner, maps) in &auxiliaries {
            if maps.clone().all(|id| claims[id].consumed()) {
                plan.classes
                    .get_mut(*owner)
                    .expect("registered auxiliary")
                    .auxiliary = Some(true);
            } else {
                // An auxiliary class shares a single initializer across all its tables.
                for id in maps.clone() {
                    claims[id].escaped = true;
                }
            }
        }
        for (map, claims) in maps.into_iter().zip(claims) {
            if !claims.consumed() {
                continue;
            }
            let visibility = plan
                .classes
                .get_mut(map.owner)
                .expect("registered map owner");
            *visibility
                .fields
                .get_mut(map.name)
                .expect("registered backing field") = true;
            if let Some(hidden) = visibility.accessors.get_mut(map.name) {
                *hidden = true;
            }
            let table = plan.tables.len();
            plan.tables.push(Table {
                enum_descriptor: format!("L{};", map.enum_name),
                auxiliary: map.initializer == ("<clinit>", "()V"),
                labels: map
                    .labels
                    .into_iter()
                    .map(|(key, label)| (key, label.into()))
                    .collect(),
            });
            for usage in claims.uses {
                let sites = &mut plan.classes.entry(usage.owner.into()).or_default().sites;
                for offset in usage.skip {
                    sites.insert((usage.method, offset), Site::Skip(table));
                }
                sites.insert(
                    (usage.method, usage.consumer),
                    if usage.empty {
                        Site::Empty(table)
                    } else {
                        Site::Switch(table)
                    },
                );
            }
        }
        plan
    }

    /// `None` leaves ordinary synthetic-member policy unchanged.
    pub(crate) fn auxiliary_visibility(&self, owner: &str) -> Option<bool> {
        self.classes.get(owner)?.auxiliary
    }

    pub(crate) fn member_visibility(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> Option<bool> {
        let class = self.classes.get(owner)?;
        match descriptor {
            FIELD => class.fields.get(name).copied(),
            ACCESSOR => class.accessors.get(name).copied(),
            _ => None,
        }
    }

    fn site(
        &self,
        owner: &str,
        method: Method,
        offset: u32,
        include_auxiliary: bool,
    ) -> Option<Site> {
        let site = *self.classes.get(owner)?.sites.get(&(method, offset))?;
        (include_auxiliary || !self.tables[site.table()].auxiliary).then_some(site)
    }

    fn action(
        &self,
        owner: &str,
        method: Method,
        offset: u32,
        include_auxiliary: bool,
    ) -> Option<Action<'_>> {
        Some(match self.site(owner, method, offset, include_auxiliary)? {
            Site::Skip(_) => Action::Skip,
            Site::Switch(table) => Action::Switch(self.tables[table].enum_name()),
            Site::Empty(table) => Action::Empty(self.tables[table].enum_name()),
        })
    }

    fn label(
        &self,
        owner: &str,
        method: Method,
        offset: u32,
        key: i32,
        include_auxiliary: bool,
    ) -> Option<(&str, &str)> {
        let Site::Switch(table) = self.site(owner, method, offset, include_auxiliary)? else {
            return None;
        };
        let table = &self.tables[table];
        Some((&table.enum_descriptor, table.labels.get(&key)?))
    }
}

impl Table {
    fn enum_name(&self) -> &str {
        &self.enum_descriptor[1..self.enum_descriptor.len() - 1]
    }
}

impl<'a, 'c> Machine<'a, 'c> {
    fn enum_switch_method(&self) -> Method {
        (self.method.name_index, self.method.descriptor_index)
    }

    pub(super) fn enum_switch_action(&self, offset: u32) -> Option<Action<'c>> {
        self.group?.enum_switches().action(
            self.owner,
            self.enum_switch_method(),
            self.debug_offset(offset),
            self.options.decompile_inner,
        )
    }

    pub(crate) fn enum_switch_label(&self, offset: u32, key: i32) -> Option<&str> {
        let (descriptor, label) = self.group?.enum_switches().label(
            self.owner,
            self.enum_switch_method(),
            self.debug_offset(offset),
            key,
            self.options.decompile_inner,
        )?;
        Some(self.source_field_name(object_descriptor(descriptor)?, label, descriptor))
    }

    pub(super) fn enum_switch_selector(&mut self, enum_name: &str) -> Result<Document, LiftError> {
        let selector = self.pop_category(Category::Ref)?;
        Ok(self.coerce_enum_selector(selector, enum_name)?.text)
    }

    pub(super) fn empty_enum_switch(&mut self, enum_name: &str) -> Result<Effect, LiftError> {
        let selector = self.pop_category(Category::Ref)?;
        let selector = self.coerce_enum_selector(selector, enum_name)?;
        self.before_statement(selector.order)?;
        let mut statement = selector.text;
        statement.surround("switch (", ") {}");
        Ok(Effect::Statement(statement))
    }

    fn coerce_enum_selector(
        &self,
        selector: super::expr::Expr,
        enum_name: &str,
    ) -> Result<super::expr::Expr, LiftError> {
        if matches!(&selector.ty, Type::Object(name) if name == enum_name) {
            Ok(selector)
        } else {
            self.member_receiver(selector, enum_name, true)
        }
    }
}

struct Map<'a> {
    owner: &'a str,
    name: &'a str,
    enum_name: &'a str,
    initializer: (&'a str, &'a str),
    labels: BTreeMap<i32, &'a str>,
}

fn member_name<'a>(pool: &'a ConstantPool<'_>, member: &Member<'_>) -> Option<(&'a str, &'a str)> {
    Some((
        pool.utf8(member.name_index).ok()?,
        pool.utf8(member.descriptor_index).ok()?,
    ))
}

fn synthetic(
    flags: u16,
    attributes: &[crate::classfile::Attribute<'_>],
    pool: &ConstantPool<'_>,
) -> bool {
    flags & SYNTHETIC != 0
        || find_attribute(attributes, pool, "Synthetic")
            .ok()
            .flatten()
            .is_some()
}

fn auxiliary_candidate<'a>(
    group: &'a ClassGroup<'_>,
    owner: &str,
    class: &'a ClassFile<'_>,
) -> Option<Vec<&'a str>> {
    if !synthetic(class.access_flags, &class.attributes, &class.pool) {
        return None;
    }
    let node = group.nested_class(owner)?;
    if !matches!(node.kind, NestedKind::Anonymous) || node.method.is_some() {
        return None;
    }
    let suffix = owner.strip_prefix(node.outer.as_str())?.strip_prefix('$')?;
    if suffix.is_empty() || !suffix.bytes().all(|ch| ch.is_ascii_digit()) {
        return None;
    }
    let fields: Vec<_> = class
        .fields
        .iter()
        .filter_map(|field| {
            let (name, descriptor) = member_name(&class.pool, field)?;
            (descriptor == FIELD && name.starts_with(JAVAC_PREFIX)).then_some(name)
        })
        .collect();
    (!fields.is_empty()).then_some(fields)
}

fn javac_tables<'a>(
    group: &'a ClassGroup<'_>,
    owner: &'a str,
    class: &'a ClassFile<'_>,
    fields: &[&'a str],
) -> Option<Vec<Map<'a>>> {
    let pool = &class.pool;
    if !group.is_attached(owner)
        || pool.class_name(class.super_class).ok()? != "java/lang/Object"
        || !class.interfaces.is_empty()
        || group.children(owner).next().is_some()
        || class.fields.len() != fields.len()
        || class.fields.iter().any(|field| {
            field.access_flags & !SYNTHETIC != STATIC | FINAL
                || !synthetic(field.access_flags, &field.attributes, pool)
        })
    {
        return None;
    }
    let [method] = &class.methods[..] else {
        return None;
    };
    let initializer = ("<clinit>", "()V");
    if member_name(pool, method)? != initializer || method.access_flags != STATIC {
        return None;
    }
    let code = method.code(pool).ok()??;
    let ops = bytecode::decode(code.bytes).ok()?;
    let (ret, ops) = ops.split_last()?;
    if ret.opcode != 0xb1 {
        return None;
    }
    let mut parser = Initializer {
        pool,
        ops,
        handlers: &code.exceptions,
        end: ret.offset,
    };
    let mut maps = Vec::with_capacity(fields.len());
    while !parser.ops.is_empty() {
        let enum_name = parser.allocate(group)?;
        let (field_owner, name, FIELD) = reference(pool, parser.take()?, 0xb3)? else {
            return None;
        };
        if field_owner != owner
            || !fields.contains(&name)
            || !encoded_name(name, JAVAC_PREFIX, enum_name)
            || maps.iter().any(|map: &Map<'_>| map.name == name)
        {
            return None;
        }
        let labels = parser.entries(group, enum_name, Array::Field((owner, name, FIELD)))?;
        maps.push(Map {
            owner,
            name,
            enum_name,
            initializer,
            labels,
        });
    }
    (maps.len() == fields.len() && parser.handlers.is_empty()).then_some(maps)
}

fn eclipse_table<'a>(
    group: &'a ClassGroup<'_>,
    owner: &'a str,
    class: &'a ClassFile<'_>,
    method: &Member<'_>,
    name: &'a str,
) -> Option<Map<'a>> {
    let pool = &class.pool;
    if !synthetic(method.access_flags, &method.attributes, pool)
        || method.access_flags & !(SYNTHETIC | STATIC | 0x0007) != 0
        || method.access_flags & STATIC == 0
    {
        return None;
    }
    let field = class
        .fields
        .iter()
        .find(|field| member_name(pool, field) == Some((name, FIELD)))?;
    if !synthetic(field.access_flags, &field.attributes, pool)
        || field.access_flags & !SYNTHETIC != STATIC | 0x0002
    {
        return None;
    }
    let code = method.code(pool).ok()??;
    let ops = bytecode::decode(code.bytes).ok()?;
    let (ret, ops) = ops.split_last()?;
    let [read, dup, check, early_return, pop, rest @ ..] = ops else {
        return None;
    };
    let field = (owner, name, FIELD);
    if reference(pool, read, 0xb2)? != field
        || dup.opcode != 0x59
        || check.opcode != 0xc6
        || check.operand != Operand::Branch(pop.offset)
        || early_return.opcode != 0xb0
        || pop.opcode != 0x57
        || ret.opcode != 0xb0
    {
        return None;
    }
    let mut parser = Initializer {
        pool,
        ops: rest,
        handlers: &code.exceptions,
        end: ret.offset,
    };
    let enum_name = parser.allocate(group)?;
    if !encoded_name(name, ECLIPSE_PREFIX, enum_name) {
        return None;
    }
    let slot = reference_slot(parser.take()?, 0x3a, 0x4b)?;
    let labels = parser.entries(group, enum_name, Array::Local(slot))?;
    let [load, next, last] = parser.ops else {
        return None;
    };
    if reference_slot(load, 0x19, 0x2a)? != slot
        || !parser.handlers.is_empty()
        || !(next.opcode == 0x59 && reference(pool, last, 0xb3) == Some(field)
            || reference(pool, next, 0xb3) == Some(field)
                && reference_slot(last, 0x19, 0x2a) == Some(slot))
    {
        return None;
    }
    Some(Map {
        owner,
        name,
        enum_name,
        initializer: (name, ACCESSOR),
        labels,
    })
}

fn encoded_name(name: &str, prefix: &str, enum_name: &str) -> bool {
    name.strip_prefix(prefix).is_some_and(|suffix| {
        suffix.len() == enum_name.len()
            && suffix.bytes().eq(enum_name
                .bytes()
                .map(|byte| if byte == b'/' { b'$' } else { byte }))
    })
}

fn is_enum(group: &ClassGroup<'_>, name: &str) -> bool {
    // The compiler's exact synthetic initializer also supplies type evidence for
    // dependencies not in the input; present class metadata must agree with it.
    group.get(name).is_none_or(|class| {
        class.access_flags & ENUM != 0
            && class.pool.class_name(class.super_class).ok() == Some("java/lang/Enum")
    })
}

fn enum_constant(group: &ClassGroup<'_>, owner: &str, name: &str, descriptor: &str) -> bool {
    object_descriptor(descriptor) == Some(owner)
        && group.get(owner).is_none_or(|class| {
            class.fields.iter().any(|field| {
                field.access_flags & (STATIC | FINAL | ENUM) == STATIC | FINAL | ENUM
                    && member_name(&class.pool, field) == Some((name, descriptor))
            })
        })
}

fn object_descriptor(descriptor: &str) -> Option<&str> {
    descriptor.strip_prefix('L')?.strip_suffix(';')
}

fn reference<'a>(
    pool: &'a ConstantPool<'_>,
    op: &Instruction,
    opcode: u8,
) -> Option<MemberRef<'a>> {
    let Operand::Constant(index) = op.operand else {
        return None;
    };
    if op.opcode != opcode
        || !matches!(
            (opcode, pool.get(index).ok()?),
            (0xb2 | 0xb3, Constant::Fieldref { .. }) | (0xb6 | 0xb8, Constant::Methodref { .. })
        )
    {
        return None;
    }
    pool.member_ref(index).ok()
}

fn ordinal(pool: &ConstantPool<'_>, op: &Instruction, enum_name: &str) -> bool {
    matches!(reference(pool, op, 0xb6), Some((owner, "ordinal", "()I"))
        if owner == enum_name || owner == "java/lang/Enum")
}

fn reference_slot(op: &Instruction, opcode: u8, compact: u8) -> Option<u16> {
    match op.operand {
        Operand::Local(slot) if op.opcode == opcode => Some(slot),
        Operand::None if (compact..compact + 4).contains(&op.opcode) => {
            Some(u16::from(op.opcode - compact))
        }
        _ => None,
    }
}

fn integer(pool: &ConstantPool<'_>, op: &Instruction) -> Option<i32> {
    match (op.opcode, &op.operand) {
        (0x02..=0x08, Operand::None) => Some(i32::from(op.opcode) - 3),
        (0x10 | 0x11, Operand::Immediate(value)) => Some(*value),
        (0x12 | 0x13, Operand::Constant(index)) => {
            let Constant::Integer(value) = *pool.get(*index).ok()? else {
                return None;
            };
            Some(value)
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum Array<'a> {
    Field(MemberRef<'a>),
    Local(u16),
}

struct Initializer<'a, 'b> {
    pool: &'a ConstantPool<'a>,
    ops: &'b [Instruction],
    handlers: &'b [ExceptionHandler],
    end: u32,
}

impl<'a, 'b> Initializer<'a, 'b> {
    fn take(&mut self) -> Option<&'b Instruction> {
        let (op, rest) = self.ops.split_first()?;
        self.ops = rest;
        Some(op)
    }

    fn allocate(&mut self, group: &ClassGroup<'_>) -> Option<&'a str> {
        let (enum_name, "values", descriptor) = reference(self.pool, self.take()?, 0xb8)? else {
            return None;
        };
        if object_descriptor(descriptor.strip_prefix("()[")?) != Some(enum_name)
            || self.take()?.opcode != 0xbe
            || self.take()?.operand != Operand::NewArray(10)
            || !is_enum(group, enum_name)
        {
            return None;
        }
        Some(enum_name)
    }

    fn entries(
        &mut self,
        group: &ClassGroup<'_>,
        enum_name: &str,
        target: Array<'_>,
    ) -> Option<BTreeMap<i32, &'a str>> {
        let mut labels = BTreeMap::new();
        let mut constants = BTreeSet::new();
        while let (Some(first), Some((handler, handlers))) =
            (self.ops.first(), self.handlers.split_first())
        {
            if u32::from(handler.start_pc) != first.offset {
                break;
            }
            let [array, get, call, value, store, jump, caught, rest @ ..] = self.ops else {
                return None;
            };
            let right_array = match target {
                Array::Field(field) => reference(self.pool, array, 0xb2) == Some(field),
                Array::Local(slot) => reference_slot(array, 0x19, 0x2a) == Some(slot),
            };
            let safe_catch = caught.opcode == 0x57
                || reference_slot(caught, 0x3a, 0x4b).is_some_and(
                    |slot| !matches!(target, Array::Local(array_slot) if slot == array_slot),
                );
            let (owner, label, descriptor) = reference(self.pool, get, 0xb2)?;
            let key = integer(self.pool, value)?;
            if !right_array
                || owner != enum_name
                || !enum_constant(group, owner, label, descriptor)
                || !ordinal(self.pool, call, enum_name)
                || store.opcode != 0x4f
                || !matches!(jump.opcode, 0xa7 | 0xc8)
                || jump.operand != Operand::Branch(rest.first().map_or(self.end, |op| op.offset))
                || u32::from(handler.end_pc) != jump.offset
                || u32::from(handler.handler_pc) != caught.offset
                || self.pool.class_name(handler.catch_type).ok()
                    != Some("java/lang/NoSuchFieldError")
                || !safe_catch
                || key <= 0
                || !constants.insert(label)
                || labels.insert(key, label).is_some()
            {
                return None;
            }
            self.ops = rest;
            self.handlers = handlers;
        }
        Some(labels)
    }
}

#[derive(Default)]
struct Claims<'a> {
    escaped: bool,
    uses: Vec<Use<'a>>,
}

impl Claims<'_> {
    fn consumed(&self) -> bool {
        !self.escaped && !self.uses.is_empty()
    }
}

struct Use<'a> {
    owner: &'a str,
    method: Method,
    skip: [u32; 3],
    consumer: u32,
    empty: bool,
}

fn symbolic_member<'a>(
    pool: &'a ConstantPool<'_>,
    constant: &Constant<'_>,
) -> Option<MemberRef<'a>> {
    let (class, name_and_type) = match *constant {
        Constant::Fieldref {
            class_index,
            name_and_type_index,
        }
        | Constant::Methodref {
            class_index,
            name_and_type_index,
        }
        | Constant::InterfaceMethodref {
            class_index,
            name_and_type_index,
        } => (class_index, name_and_type_index),
        _ => return None,
    };
    let (name, descriptor) = pool.name_and_type(name_and_type).ok()?;
    Some((pool.class_name(class).ok()?, name, descriptor))
}

fn instruction_index(op: &Instruction) -> Option<u16> {
    match op.operand {
        Operand::Constant(index)
        | Operand::InvokeInterface { index, .. }
        | Operand::MultiANewArray { index, .. } => Some(index),
        _ => None,
    }
}

fn collect_uses<'a>(
    owner: &'a str,
    class: &'a ClassFile<'_>,
    source: bool,
    maps: &[Map<'a>],
    references: &BTreeMap<MemberRef<'a>, usize>,
    auxiliaries: &BTreeMap<&str, std::ops::Range<usize>>,
    claims: &mut [Claims<'a>],
) {
    let pool = &class.pool;
    let mut candidates = BTreeSet::new();
    let auxiliary_for = |name: &str| {
        let name = if name.starts_with('[') {
            object_descriptor(name.trim_start_matches('[')).unwrap_or(name)
        } else {
            name
        };
        auxiliaries.get(name).into_iter().flat_map(Clone::clone)
    };
    let table_for = |member: MemberRef<'_>| references.get(&member).copied();
    let mut referenced_aux = BTreeSet::new();
    if !auxiliaries.is_empty() {
        for &index in std::iter::once(&class.super_class).chain(&class.interfaces) {
            if let Ok(name) = pool.class_name(index) {
                escape(claims, auxiliary_for(name));
            }
        }
        for member in class.fields.iter().chain(&class.methods) {
            if let Some((_, descriptor)) = member_name(pool, member) {
                escape(
                    claims,
                    descriptor_classes(descriptor).flat_map(auxiliary_for),
                );
            }
        }
    }
    for constant in pool.iter() {
        match *constant {
            Constant::Class(index) if !auxiliaries.is_empty() => {
                if let Ok(name) = pool.utf8(index) {
                    referenced_aux.extend(auxiliary_for(name));
                }
            }
            Constant::NameAndType {
                descriptor_index, ..
            }
            | Constant::MethodType(descriptor_index)
                if !auxiliaries.is_empty() =>
            {
                if let Ok(descriptor) = pool.utf8(descriptor_index) {
                    escape(
                        claims,
                        descriptor_classes(descriptor).flat_map(auxiliary_for),
                    );
                }
            }
            Constant::MethodHandle {
                reference_index, ..
            } => {
                if let Ok(target) = pool.get(reference_index)
                    && let Some(member) = symbolic_member(pool, target)
                {
                    escape(claims, table_for(member));
                    escape(claims, auxiliary_for(member.0));
                }
            }
            _ => {
                if let Some(id) = symbolic_member(pool, constant).and_then(table_for) {
                    candidates.insert(id);
                }
            }
        }
    }
    if candidates.is_empty() && referenced_aux.is_empty() {
        return;
    }
    if !referenced_aux.is_empty() {
        match class.bootstrap_methods() {
            Ok(bootstraps) => {
                for bootstrap in bootstraps {
                    for index in bootstrap.arguments {
                        if let Ok(Constant::Class(index)) = pool.get(index)
                            && let Ok(name) = pool.utf8(*index)
                        {
                            escape(claims, auxiliary_for(name));
                        }
                    }
                }
            }
            Err(_) => escape(claims, referenced_aux.iter().copied()),
        }
    }
    let mut stack = Vec::new();
    for method in &class.methods {
        let Some(method_name) = member_name(pool, method) else {
            continue;
        };
        let decoded = match method.code(pool) {
            Ok(None) => continue,
            Ok(Some(code)) => bytecode::decode(code.bytes).ok().map(|ops| (code, ops)),
            Err(_) => None,
        };
        let Some((code, ops)) = decoded else {
            // A malformed method is not evidence that a referenced table is unused.
            escape(claims, candidates.into_iter().chain(referenced_aux));
            return;
        };
        let source = source && !ops.iter().any(|op| matches!(op.opcode, 0xa8 | 0xa9 | 0xc9));
        let mut entries = None;
        for (index, op) in ops.iter().enumerate() {
            let Some(constant_index) = instruction_index(op) else {
                continue;
            };
            let Ok(constant) = pool.get(constant_index) else {
                continue;
            };
            if let Constant::Class(name) = *constant
                && let Ok(name) = pool.utf8(name)
            {
                escape(claims, auxiliary_for(name));
            }
            let Some(member) = symbolic_member(pool, constant) else {
                continue;
            };
            let Some(id) = table_for(member) else {
                escape(claims, auxiliary_for(member.0));
                continue;
            };
            let table = &maps[id];
            if owner == table.owner && method_name == table.initializer {
                // The whole initializer is already accounted for by the recognizer.
                continue;
            }
            if claims[id].escaped {
                continue;
            }
            let acquisition = if table.initializer == ("<clinit>", "()V") {
                0xb2
            } else {
                0xb8
            };
            let expected = (
                table.owner,
                table.name,
                if acquisition == 0xb2 { FIELD } else { ACCESSOR },
            );
            if !source || reference(pool, op, acquisition) != Some(expected) {
                claims[id].escaped = true;
                continue;
            }
            let entries = entries.get_or_insert_with(|| control_entries(&ops, &code.exceptions));
            let method = (method.name_index, method.descriptor_index);
            if let Some(usage) = consume_lookup(
                pool,
                &ops[index..],
                entries,
                table,
                (owner, method),
                &mut stack,
            ) {
                claims[id].uses.push(usage);
            } else {
                claims[id].escaped = true;
            }
        }
    }
}

fn escape(claims: &mut [Claims<'_>], ids: impl IntoIterator<Item = usize>) {
    for id in ids {
        claims[id].escaped = true;
    }
}

fn descriptor_classes(mut descriptor: &str) -> impl Iterator<Item = &str> {
    std::iter::from_fn(move || {
        let (class, tail) = descriptor.split_once('L')?.1.split_once(';')?;
        descriptor = tail;
        Some(class)
    })
}

fn control_entries(ops: &[Instruction], handlers: &[ExceptionHandler]) -> BTreeSet<u32> {
    let mut entries = BTreeSet::new();
    for op in ops {
        match &op.operand {
            Operand::Branch(target) => {
                entries.insert(*target);
            }
            Operand::Switch { default, cases } => {
                entries.insert(*default);
                entries.extend(cases.iter().map(|&(_, target)| target));
            }
            _ => {}
        }
    }
    for handler in handlers {
        entries.extend([handler.start_pc, handler.end_pc, handler.handler_pc].map(u32::from));
    }
    entries
}

fn consume_lookup<'a, 'p>(
    pool: &'p ConstantPool<'_>,
    ops: &[Instruction],
    entries: &BTreeSet<u32>,
    table: &Map<'_>,
    (owner, method): (&'a str, Method),
    stack: &mut Vec<Value<'p>>,
) -> Option<Use<'a>> {
    let (acquire, mut ops) = ops.split_first()?;
    let next_entry = entries
        .range((
            std::ops::Bound::Excluded(acquire.offset),
            std::ops::Bound::Unbounded,
        ))
        .next()
        .copied()
        .unwrap_or(u32::MAX);
    stack.clear();
    while let [op, rest @ ..] = ops {
        if op.offset >= next_entry {
            return None;
        }
        if let [Value::Reference(receiver)] = stack.as_slice()
            && let [lookup, consumer, ..] = rest
            && lookup.opcode == 0x2e
            && consumer.offset < next_entry
            && let Some((call_owner, "ordinal", "()I")) = reference(pool, op, 0xb6)
            && (call_owner == table.enum_name
                || call_owner == "java/lang/Enum" && *receiver == Some(table.enum_name))
        {
            let empty = match &consumer.operand {
                Operand::None if consumer.opcode == 0x57 => true,
                Operand::Switch { default, cases }
                    if cases.iter().all(|(key, target)| {
                        target == default || table.labels.contains_key(key)
                    }) =>
                {
                    false
                }
                _ => return None,
            };
            return Some(Use {
                owner,
                method,
                skip: [acquire.offset, op.offset, lookup.offset],
                consumer: consumer.offset,
                empty,
            });
        }
        evaluate_producer(pool, op, stack)?;
        ops = rest;
    }
    None
}

#[derive(Clone, Copy)]
enum Value<'a> {
    Scalar(u16),
    /// A known class name, an array descriptor, or an unrefined reference.
    Reference(Option<&'a str>),
    Uninitialized {
        name: &'a str,
        allocation: u32,
    },
}

impl Value<'_> {
    fn width(self) -> u16 {
        match self {
            Self::Scalar(width) => width,
            Self::Reference(_) | Self::Uninitialized { .. } => 1,
        }
    }
}

fn descriptor_value(descriptor: &str) -> Option<Value<'_>> {
    Some(match descriptor.as_bytes().first()? {
        b'[' => Value::Reference(Some(descriptor)),
        b'L' => Value::Reference(Some(object_descriptor(descriptor)?)),
        b'J' | b'D' => Value::Scalar(2),
        b'B' | b'C' | b'F' | b'I' | b'S' | b'Z' => Value::Scalar(1),
        _ => return None,
    })
}

fn consume_slots(stack: &mut Vec<Value<'_>>, mut slots: u16) -> Option<()> {
    while slots != 0 {
        slots = slots.checked_sub(stack.pop()?.width())?;
    }
    Some(())
}

fn take_ref<'a>(stack: &mut Vec<Value<'a>>) -> Option<Option<&'a str>> {
    let Value::Reference(name) = stack.pop()? else {
        return None;
    };
    Some(name)
}

/// Prove that the straight-line receiver expression cannot access the map or the
/// previous operand stack. Unrecognised producers leave the original map intact.
fn evaluate_producer<'a>(
    pool: &'a ConstantPool<'_>,
    op: &Instruction,
    stack: &mut Vec<Value<'a>>,
) -> Option<()> {
    let scalar = Value::Scalar;
    let reference = Value::Reference;
    let value = match op.opcode {
        0x00 => return Some(()),
        0x01 | 0x19 | 0x2a..=0x2d => reference(None),
        0x02..=0x08 | 0x0b..=0x0d | 0x10..=0x11 | 0x15 | 0x17 | 0x1a..=0x1d | 0x22..=0x25 => {
            scalar(1)
        }
        0x09..=0x0a | 0x0e..=0x0f | 0x16 | 0x18 | 0x1e..=0x21 | 0x26..=0x29 => scalar(2),
        0x12..=0x14 => match pool.get(instruction_index(op)?).ok()? {
            Constant::Integer(_) | Constant::Float(_) => scalar(1),
            Constant::Long(_) | Constant::Double(_) => scalar(2),
            Constant::String(_) => reference(Some("java/lang/String")),
            Constant::Class(_) => reference(Some("java/lang/Class")),
            Constant::MethodHandle { .. } | Constant::MethodType(_) => reference(None),
            Constant::Dynamic {
                name_and_type_index,
                ..
            } => descriptor_value(pool.name_and_type(*name_and_type_index).ok()?.1)?,
            _ => return None,
        },
        0x2e..=0x35 => {
            consume_slots(stack, 1)?;
            let array = take_ref(stack)?;
            match op.opcode {
                0x2f | 0x31 => scalar(2),
                0x32 => match array
                    .and_then(|name| name.strip_prefix('['))
                    .and_then(descriptor_value)
                {
                    Some(reference @ Value::Reference(_)) => reference,
                    _ => reference(None),
                },
                _ => scalar(1),
            }
        }
        0x59 => {
            let value = *stack.last()?;
            if !matches!(value, Value::Uninitialized { .. }) {
                return None;
            }
            value
        }
        0x60..=0x77 => {
            let width = 1 + u16::from(op.opcode % 2);
            consume_slots(stack, width * if op.opcode < 0x74 { 2 } else { 1 })?;
            scalar(width)
        }
        0x78..=0x83 => {
            let width = 1 + u16::from(op.opcode % 2);
            consume_slots(stack, width + if op.opcode < 0x7e { 1 } else { width })?;
            scalar(width)
        }
        0x85..=0x93 => {
            consume_slots(
                stack,
                if matches!(op.opcode, 0x88..=0x8a | 0x8e..=0x90) {
                    2
                } else {
                    1
                },
            )?;
            scalar(
                if matches!(op.opcode, 0x85 | 0x87 | 0x8a | 0x8c | 0x8d | 0x8f) {
                    2
                } else {
                    1
                },
            )
        }
        0xb2 | 0xb4 => {
            let (_, _, descriptor) = symbolic_member(pool, pool.get(instruction_index(op)?).ok()?)?;
            if op.opcode == 0xb4 {
                take_ref(stack)?;
            }
            descriptor_value(descriptor)?
        }
        0xb6..=0xba => {
            let constant = pool.get(instruction_index(op)?).ok()?;
            let (owner, name, descriptor) = match constant {
                Constant::InvokeDynamic {
                    name_and_type_index,
                    ..
                } if op.opcode == 0xba => {
                    let (name, descriptor) = pool.name_and_type(*name_and_type_index).ok()?;
                    ("", name, descriptor)
                }
                _ => symbolic_member(pool, constant)?,
            };
            let method = MethodDescriptor::parse(descriptor).ok()?;
            for parameter in method.parameters.iter().rev() {
                match parameter {
                    Type::Object(_) | Type::Array(_) => {
                        take_ref(stack)?;
                    }
                    _ => {
                        consume_slots(stack, parameter.slots())?;
                    }
                }
            }
            if op.opcode == 0xb7 && name == "<init>" && method.return_type == Type::Void {
                let Value::Uninitialized { name, allocation } = stack.pop()? else {
                    return None;
                };
                if name != owner {
                    return None;
                }
                let value = stack.last_mut()?;
                if !matches!(value, Value::Uninitialized { allocation: site, .. } if *site == allocation)
                {
                    return None;
                }
                *value = reference(Some(name));
                return Some(());
            }
            if !matches!(op.opcode, 0xb8 | 0xba) {
                take_ref(stack)?;
            }
            descriptor_value(descriptor.split_once(')')?.1)?
        }
        0xbb => Value::Uninitialized {
            name: pool.class_name(instruction_index(op)?).ok()?,
            allocation: op.offset,
        },
        0xbe => {
            take_ref(stack)?;
            scalar(1)
        }
        0xc0 => {
            take_ref(stack)?;
            reference(Some(pool.class_name(instruction_index(op)?).ok()?))
        }
        _ => return None,
    };
    stack.push(value);
    Some(())
}

#[cfg(test)]
#[path = "enum_switch_tests.rs"]
mod tests;
