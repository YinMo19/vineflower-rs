// Based on Vineflower enum handling in ClassWriter and InitializerProcessor (Apache-2.0).
use std::{collections::{BTreeMap, BTreeSet}, fmt::Write, rc::Rc};

use super::{DecompileError, ENUM, FINAL, PRIVATE, PUBLIC, STATIC, SYNTHETIC, Writer, parse};
use super::initializers::{InitializerMapOrder, merge_initializer_mapping};
use crate::{
    bytecode::{Instruction, Operand, decode},
    classfile::{ClassFile, Constant, Member},
    descriptor::{MethodDescriptor, Type},
    lift::{AnonymousSites, Machine},
    source_text::Document,
};

#[path = "enumeration_subclasses.rs"]
mod subclasses;

struct ConstantInit<'a> {
    name: &'a str,
    arguments: Document,
    subclass: Option<usize>,
}

const CONSTRUCTOR_PREFIX: &str = "(Ljava/lang/String;I";
const ENTRIES_TYPE: &str = "Lkotlin/enums/EnumEntries;";
pub(super) const ENTRIES_FACTORY: &str = "kotlin/enums/EnumEntriesKt";

pub(super) struct Enumeration<'a> {
    constants: Vec<ConstantInit<'a>>,
    sites: Option<AnonymousSites>,
    constructor_bridges: BTreeSet<&'a str>,
    values_field: Option<&'a str>,
    helper: Option<&'a str>,
    entries_initializer: Option<std::ops::Range<u32>>,
    skip_initializer: usize,
    initializer_lines: Vec<(u16, u16)>,
}

impl<'a> Enumeration<'a> {
    pub(super) fn recover(writer: &Writer<'_, 'a>) -> Result<Self, DecompileError> {
        let class = writer.class;
        let pool = &class.pool;
        if class.super_class == 0 || pool.class_name(class.super_class)? != "java/lang/Enum" {
            return Err(unsupported("enum with nonstandard superclass"));
        }
        let owner = pool.class_name(class.this_class)?;
        let values_type = format!("[L{owner};");
        let field_type = &values_type[1..];
        let mut names = Vec::new();
        let mut values_field = None;
        for field in &class.fields {
            let name = pool.utf8(field.name_index)?;
            if field.access_flags & ENUM != 0 {
                names.push(name);
            } else if field.access_flags & (PRIVATE | STATIC | FINAL | SYNTHETIC)
                == PRIVATE | STATIC | FINAL | SYNTHETIC
                && pool.utf8(field.descriptor_index)? == values_type
                && values_field.replace(name).is_some()
            {
                return Err(unsupported("ambiguous enum values arrays"));
            }
        }
        let initializer = class
            .methods
            .iter()
            .find(|method| matches!(pool.utf8(method.name_index), Ok("<clinit>")));
        let map_offsets = writer.mapping.is_some() && writer.options.method_to_decompile.is_empty();
        let mut has_visible_arguments = false;
        let mut result = Self {
            constants: Vec::with_capacity(names.len()),
            sites: writer.anonymous_sites(),
            constructor_bridges: BTreeSet::new(),
            values_field,
            helper: None,
            entries_initializer: None,
            skip_initializer: 0,
            initializer_lines: Vec::new(),
        };
        let Some(initializer) = initializer else {
            // Some assemblers provide enum-flagged fields without a generated initializer.
            result
                .constants
                .extend(names.iter().map(|&name| ConstantInit {
                    name,
                    arguments: Document::new(),
                    subclass: None,
                }));
            verify_generated_lookup_methods(class, owner, None, &values_type)?;
            return Ok(result);
        };
        let values =
            values_field.ok_or_else(|| unsupported("enum without synthetic values array"))?;
        let code = initializer
            .code(pool)?
            .ok_or(DecompileError::InvalidAttribute(
                "enum class initializer Code",
            ))?;
        let instructions = decode(code.bytes).map_err(|source| DecompileError::Method {
            name: "<clinit>".into(),
            descriptor: "()V".into(),
            source: Box::new(source),
        })?;
        let initializer_type = parse("()V", MethodDescriptor::parse)?;
        let render_class = |name: &str| writer.names.render(name);
        let mut allocated_subclasses = BTreeSet::new();
        let mut cursor = instructions.as_slice();
        for (ordinal, &name) in names.iter().enumerate() {
            let Some(([new, duplicate, name_load, order], tail)) = cursor.split_first_chunk::<4>()
            else {
                return Err(pattern());
            };
            let Operand::Constant(index) = new.operand else {
                return Err(pattern());
            };
            if new.opcode != 0xbb
                || duplicate.opcode != 0x59
                || string_value(class, name_load)? != Some(name)
                || integer(class, order)? != Some(ordinal as i32)
            {
                return Err(pattern());
            }
            let allocated = pool.class_name(index)?;
            let mut constructor = None;
            for (at, pair) in tail.windows(2).enumerate() {
                let (call, store) = (&pair[0], &pair[1]);
                if let Some((call_owner, "<init>", raw)) = member(class, call, 0xb7)?
                    && call_owner == allocated
                    && member(class, store, 0xb3)? == Some((owner, name, field_type))
                {
                    constructor = Some((at, raw));
                    break;
                }
            }
            let (constructor_at, raw) = constructor.ok_or_else(pattern)?;
            let mut descriptor = parse(raw, MethodDescriptor::parse)?;
            if !raw.starts_with(CONSTRUCTOR_PREFIX) || descriptor.return_type != Type::Void {
                return Err(pattern());
            }
            let subclass = if allocated != owner {
                if !allocated_subclasses.insert(allocated) {
                    return Err(unsupported(
                        "enum subclass reused by more than one constant",
                    ));
                }
                let sites = result
                    .sites
                    .as_ref()
                    .ok_or_else(|| unsupported("detached enum constant subclass"))?;
                let recovered =
                    subclasses::recover(writer.group, class, owner, allocated, raw, &descriptor)?;
                result.constructor_bridges.extend(recovered.bridge);
                let mut sites = sites.borrow_mut();
                let id = sites.len();
                sites.push(recovered.site);
                Some(id)
            } else {
                let target = subclasses::find_constructor(class, raw)?.ok_or_else(pattern)?;
                if target.access_flags & SYNTHETIC != 0 {
                    return Err(pattern());
                }
                None
            };
            descriptor.parameters.drain(..2);
            let arg_ops = &tail[..constructor_at];
            if arg_ops.iter().any(|op| {
                member(class, op, 0xb2)
                    .is_ok_and(|reference| reference == Some((owner, values, values_type.as_str())))
            }) {
                return Err(unsupported(
                    "enum constant references the hidden values array",
                ));
            }
            let arguments = if arg_ops.is_empty() && descriptor.parameters.is_empty() {
                Document::new()
            } else {
                let wrap = |source| DecompileError::Method {
                    name: "<clinit>".into(),
                    descriptor: "()V".into(),
                    source: Box::new(source),
                };
                let mut machine = Machine::new(
                    class,
                    initializer,
                    &code,
                    &initializer_type,
                    writer.options,
                    &render_class,
                )
                .map_err(wrap)?
                .with_group(writer.group);
                machine.set_member_renames(writer.names.renames());
                machine.set_dynamic_helpers(Rc::clone(&writer.dynamic_helpers));
                if let Some(sites) = &result.sites {
                    machine.set_anonymous_sites(Rc::clone(sites));
                }
                machine
                    .enum_constant_arguments(
                        arg_ops,
                        tail[constructor_at].offset,
                        &descriptor,
                        map_offsets,
                    )
                    .map_err(wrap)?
            };
            has_visible_arguments |= !arguments.is_empty();
            result.constants.push(ConstantInit {
                name,
                arguments,
                subclass,
            });
            cursor = &tail[constructor_at + 2..];
        }
        let values_method = format!("(){values_type}");
        if let Some((helper_owner, helper, desc)) =
            member(class, cursor.first().ok_or_else(pattern)?, 0xb8)?
        {
            if helper_owner != owner || desc != values_method {
                return Err(pattern());
            }
            let mut found = false;
            for method in &class.methods {
                if method.access_flags & (PRIVATE | STATIC | SYNTHETIC)
                    == PRIVATE | STATIC | SYNTHETIC
                    && pool.utf8(method.name_index)? == helper
                    && pool.utf8(method.descriptor_index)? == values_method
                {
                    let code = method.code(pool)?.ok_or_else(pattern)?;
                    let instructions = decode(code.bytes).map_err(|_| pattern())?;
                    let tail = values_array(class, &names, field_type, &instructions)?;
                    found =
                        matches!(tail, [ret] if ret.opcode == 0xb0) && code.exceptions.is_empty();
                    break;
                }
            }
            if !found {
                return Err(pattern());
            }
            result.helper = Some(helper);
            cursor = &cursor[1..];
        } else {
            cursor = values_array(class, &names, field_type, cursor)?;
        }
        let Some((store, tail)) = cursor.split_first() else {
            return Err(pattern());
        };
        if member(class, store, 0xb3)? != Some((owner, values, values_type.as_str()))
            || tail.is_empty()
        {
            return Err(pattern());
        }
        let mut tail = tail;
        if let Some(([load, cast, call, store], rest)) = tail.split_first_chunk::<4>()
            && !rest.is_empty()
            && member(class, load, 0xb2)? == Some((owner, values, values_type.as_str()))
            && class_is(class, cast, 0xc0, "[Ljava/lang/Enum;")?
            && member(class, call, 0xb8)? == Some((
                ENTRIES_FACTORY, "enumEntries", "([Ljava/lang/Enum;)Lkotlin/enums/EnumEntries;",
            ))
            && member(class, store, 0xb3)? == Some((owner, "$ENTRIES", ENTRIES_TYPE))
            && class.fields.iter().any(|field| {
                field.access_flags == PRIVATE | STATIC | FINAL | SYNTHETIC
                    && pool.utf8(field.name_index).ok() == Some("$ENTRIES")
                    && pool.utf8(field.descriptor_index).ok() == Some(ENTRIES_TYPE)
            })
        {
            // Java hides the generated backing array. Its public values()
            // already proves an ordered snapshot of exactly those constants.
            result.entries_initializer = Some(load.offset..store.offset + store.len);
            tail = rest;
        }
        result.skip_initializer = instructions.len() - tail.len();
        let start = tail[0].offset;
        if subclasses::enters_prefix(&code, tail, start) {
            return Err(unsupported("control flow enters enum construction"));
        }
        verify_generated_lookup_methods(class, owner, Some(values), &values_type)?;
        if map_offsets && (has_visible_arguments || result.entries_initializer.is_some()) {
            result.initializer_lines = code.line_numbers(pool)?;
        }
        Ok(result)
    }

    pub(super) fn hides_field(&self, field: &Member<'_>, name: &str) -> bool {
        field.access_flags & ENUM != 0 || self.values_field == Some(name)
    }

    pub(super) fn entries_initializer(&self, name: &str) -> Option<std::ops::Range<u32>> {
        (name == "$ENTRIES").then(|| self.entries_initializer.clone()).flatten()
    }

    pub(super) fn hides_method(
        &self,
        owner: &str,
        name: &str,
        desc: &str,
        method: &Member<'_>,
    ) -> bool {
        name == "<init>" && self.constructor_bridges.contains(desc)
            || self.helper == Some(name)
                && method.access_flags & (PRIVATE | STATIC | SYNTHETIC)
                    == PRIVATE | STATIC | SYNTHETIC
            || method.access_flags & (PUBLIC | STATIC) == PUBLIC | STATIC
                && match name {
                    "values" => {
                        desc.strip_prefix("()[L")
                            .and_then(|desc| desc.strip_suffix(';'))
                            == Some(owner)
                    }
                    "valueOf" => {
                        desc.strip_prefix("(Ljava/lang/String;)L")
                            .and_then(|desc| desc.strip_suffix(';'))
                            == Some(owner)
                    }
                    _ => false,
                }
    }

    pub(super) fn method_prefix(
        &self,
        class: &ClassFile<'_>,
        name: &str,
        desc: &str,
        instructions: &[Instruction],
    ) -> Result<usize, DecompileError> {
        match name {
            "<clinit>" => Ok(self.skip_initializer),
            "<init>" if desc.starts_with(CONSTRUCTOR_PREFIX) => {
                // The only legal direct Enum invocation is javac's implicit
                // prefix. An alternate constructor may have a Java 25
                // prologue before the hidden label and ordinal are loaded.
                let mut hidden = instructions.iter().enumerate()
                    .filter(|(_, op)| matches!(subclasses::local_slot(op), Some(1 | 2)));
                let Some((label_at, label)) = hidden.next() else { return Err(pattern()) };
                let Some((ordinal_at, ordinal)) = hidden.next() else { return Err(pattern()) };
                if ordinal_at != label_at + 1
                    || !local(label, 0x19, 1)
                    || !local(ordinal, 0x15, 2)
                    || hidden.next().is_some()
                {
                    return Err(unsupported("explicit use of JVM enum constructor parameters"));
                }
                if let [receiver, _, _, call, _rest @ ..] = instructions
                    && label_at == 1
                    && local(receiver, 0x19, 0)
                    && matches!(member(class, call, 0xb7)?, Some(("java/lang/Enum", "<init>", "(Ljava/lang/String;I)V")))
                {
                    return if instructions.len() > 4 { Ok(4) } else { Err(pattern()) };
                }
                Ok(0)
            }
            "<init>" => Err(pattern()),
            _ => Ok(0),
        }
    }
}

impl Writer<'_, '_> {
    pub(super) fn emit_enum_constants(
        &mut self,
        enumeration: &mut Enumeration<'_>,
    ) -> Result<BTreeMap<u32, usize>, DecompileError> {
        let count = enumeration.constants.len();
        let map_offsets = self.mapping.is_some();
        let mut offsets = BTreeMap::new();
        if count == 0 {
            self.line(1, ";");
        }
        let descriptor = self
            .options
            .dump_text_tokens
            .then(|| format!("L{};", self.owner));
        for (index, constant) in enumeration.constants.drain(..).enumerate() {
            let mut head = Document::new();
            if let Some(descriptor) = &descriptor {
                self.field_symbol(&mut head, constant.name, constant.name, descriptor);
            } else {
                head.push_str(constant.name);
            }
            head.append(constant.arguments);
            if let Some(id) = constant.subclass {
                let _ = write!(head, "\0{id}\0");
            }
            head.push(if index + 1 == count { ';' } else { ',' });
            if map_offsets {
                self.line_with_anonymous_anchors(
                    1, &head, enumeration.sites.as_ref(),
                    Some(&mut |bytes: std::ops::Range<u32>, line| {
                        offsets.extend(bytes.map(|offset| (offset, line)));
                    }),
                )?;
                for offset in head.omitted_bytecode().flatten() {
                    offsets.remove(&offset);
                }
            } else {
                self.line_with_anonymous(1, &head, enumeration.sites.as_ref())?;
            }
        }
        Ok(offsets)
    }

    pub(super) fn finish_enum_initializer_map(
        &mut self,
        enumeration: Enumeration<'_>,
        offsets: BTreeMap<u32, usize>,
    ) {
        merge_initializer_mapping(
            self, "<clinit>", "()V", offsets, enumeration.initializer_lines,
            InitializerMapOrder::ClassDeclarations,
        );
    }
}

fn values_array<'i>(
    class: &ClassFile<'_>,
    names: &[&str],
    field_type: &str,
    instructions: &'i [Instruction],
) -> Result<&'i [Instruction], DecompileError> {
    let owner = class.pool.class_name(class.this_class)?;
    let Some(([length, new], mut tail)) = instructions.split_first_chunk::<2>() else {
        return Err(pattern());
    };
    if integer(class, length)? != Some(names.len() as i32) || !class_is(class, new, 0xbd, owner)? {
        return Err(pattern());
    }
    let via_local = tail.first().is_some_and(|op| store_local(op, 0x3a, 0));
    if via_local {
        tail = &tail[1..];
    }
    for (index, &name) in names.iter().enumerate() {
        let Some(([reference, slot, load, store], rest)) = tail.split_first_chunk::<4>() else {
            return Err(pattern());
        };
        let array = if via_local { local(reference, 0x19, 0) } else { reference.opcode == 0x59 };
        if !array
            || integer(class, slot)? != Some(index as i32)
            || member(class, load, 0xb2)? != Some((owner, name, field_type))
            || store.opcode != 0x53
        {
            return Err(pattern());
        }
        tail = rest;
    }
    if via_local {
        let (reload, rest) = tail.split_first().ok_or_else(pattern)?;
        if !local(reload, 0x19, 0) || !matches!(rest, [ret] if ret.opcode == 0xb0) {
            return Err(pattern());
        }
        tail = rest;
    }
    Ok(tail)
}

/// Only the language-defined lookup methods may disappear with the backing
/// array. javac clones it; Eclipse allocates and copies the same array.
fn verify_generated_lookup_methods(
    class: &ClassFile<'_>,
    owner: &str,
    values: Option<&str>,
    array_type: &str,
) -> Result<(), DecompileError> {
    let pool = &class.pool;
    for method in &class.methods {
        let name = pool.utf8(method.name_index)?;
        let desc = pool.utf8(method.descriptor_index)?;
        let copy = name == "values" && desc.strip_prefix("()") == Some(array_type);
        let lookup = name == "valueOf"
            && desc
                .strip_prefix("(Ljava/lang/String;)L")
                .and_then(|ty| ty.strip_suffix(';'))
                == Some(owner);
        if !copy && !lookup {
            continue;
        }
        let fail = || unsupported("nonstandard enum lookup method");
        if method.access_flags & !SYNTHETIC != PUBLIC | STATIC {
            return Err(fail());
        }
        let code = method.code(pool)?.ok_or_else(fail)?;
        let ops = decode(code.bytes).map_err(|_| fail())?;
        if !code.exceptions.is_empty() {
            return Err(fail());
        }
        let verified = if copy {
            match values {
                Some(values) => verify_values_copy(class, &ops, owner, values, array_type)?,
                None => false,
            }
        } else if let [load, name, call, cast, ret] = ops.as_slice() {
            load_constant(load).is_some()
                && class_is(class, load, load.opcode, owner)?
                && local(name, 0x19, 0)
                && member(class, call, 0xb8)?
                    == Some((
                        "java/lang/Enum",
                        "valueOf",
                        "(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;",
                    ))
                && class_is(class, cast, 0xc0, owner)?
                && ret.opcode == 0xb0
        } else {
            false
        };
        if !verified {
            return Err(fail());
        }
    }
    Ok(())
}

fn verify_values_copy(
    class: &ClassFile<'_>,
    instructions: &[Instruction],
    owner: &str,
    values: &str,
    array_type: &str,
) -> Result<bool, DecompileError> {
    let Some((load, tail)) = instructions.split_first() else {
        return Ok(false);
    };
    if member(class, load, 0xb2)? != Some((owner, values, array_type)) {
        return Ok(false);
    }
    Ok(match tail {
        [clone, cast, ret] => {
            matches!(member(class, clone, 0xb6)?,
                Some((name, "clone", "()Ljava/lang/Object;")) if name == array_type || name == "java/lang/Object")
                && class_is(class, cast, 0xc0, array_type)?
                && ret.opcode == 0xb0
        }
        [
            dup,
            save_array,
            from_start,
            load_array,
            length,
            dup_len,
            save_len,
            allocate,
            dup_target,
            save_target,
            to_start,
            load_len,
            copy,
            result,
            ret,
        ] => {
            dup.opcode == 0x59
                && store_local(save_array, 0x3a, 0)
                && integer(class, from_start)? == Some(0)
                && local(load_array, 0x19, 0)
                && length.opcode == 0xbe
                && dup_len.opcode == 0x59
                && store_local(save_len, 0x36, 1)
                && class_is(class, allocate, 0xbd, owner)?
                && dup_target.opcode == 0x59
                && store_local(save_target, 0x3a, 2)
                && integer(class, to_start)? == Some(0)
                && local(load_len, 0x15, 1)
                && member(class, copy, 0xb8)?
                    == Some((
                        "java/lang/System",
                        "arraycopy",
                        "(Ljava/lang/Object;ILjava/lang/Object;II)V",
                    ))
                && local(result, 0x19, 2)
                && ret.opcode == 0xb0
        }
        _ => false,
    })
}

fn store_local(op: &Instruction, opcode: u8, slot: u16) -> bool {
    (op.opcode == opcode && op.operand == Operand::Local(slot))
        || (slot < 4 && op.opcode == 0x3b + (opcode - 0x36) * 4 + slot as u8)
}

fn load_constant(op: &Instruction) -> Option<u16> {
    match (op.opcode, &op.operand) {
        (0x12..=0x14, Operand::Constant(index)) => Some(*index),
        _ => None,
    }
}

fn string_value<'a>(
    class: &'a ClassFile<'_>,
    op: &Instruction,
) -> Result<Option<&'a str>, DecompileError> {
    Ok(
        match load_constant(op)
            .map(|index| class.pool.get(index))
            .transpose()?
        {
            Some(Constant::String(index)) => Some(class.pool.utf8(*index)?),
            _ => None,
        },
    )
}

fn integer(class: &ClassFile<'_>, op: &Instruction) -> Result<Option<i32>, DecompileError> {
    Ok(match (op.opcode, &op.operand) {
        (0x02..=0x08, _) => Some(i32::from(op.opcode) - 3),
        (0x10..=0x11, Operand::Immediate(value)) => Some(*value),
        (0x12..=0x13, Operand::Constant(index)) => match class.pool.get(*index)? {
            Constant::Integer(value) => Some(*value),
            _ => None,
        },
        _ => None,
    })
}

fn class_is(
    class: &ClassFile<'_>,
    op: &Instruction,
    opcode: u8,
    expected: &str,
) -> Result<bool, DecompileError> {
    match (op.opcode, &op.operand) {
        (code, Operand::Constant(index)) if code == opcode => {
            Ok(class.pool.class_name(*index)? == expected)
        }
        _ => Ok(false),
    }
}

fn member<'a>(
    class: &'a ClassFile<'_>,
    op: &Instruction,
    opcode: u8,
) -> Result<Option<(&'a str, &'a str, &'a str)>, DecompileError> {
    match (op.opcode, &op.operand) {
        (code, Operand::Constant(index)) if code == opcode => {
            let constant = class.pool.get(*index)?;
            if !matches!(
                (code, constant),
                (0xb2 | 0xb3, Constant::Fieldref { .. })
                    | (0xb6..=0xb8, Constant::Methodref { .. })
            ) {
                return Err(pattern());
            }
            Ok(Some(class.pool.member_ref(*index)?))
        }
        _ => Ok(None),
    }
}

fn local(op: &Instruction, opcode: u8, slot: u16) -> bool {
    (op.opcode == opcode && op.operand == Operand::Local(slot))
        || (slot < 4 && op.opcode == 0x1a + (opcode - 0x15) * 4 + slot as u8)
}

fn pattern() -> DecompileError {
    unsupported("nonstandard enum initialization")
}
fn unsupported(feature: &'static str) -> DecompileError {
    DecompileError::Unsupported { feature }
}
