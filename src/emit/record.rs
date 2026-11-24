// Based on Vineflower RecordHelper and ClassWriter (Apache-2.0).
use super::{
    DecompileError, Document, FINAL, PRIVATE, PUBLIC, STATIC, VARARGS, VISIBILITY, Writer, parse,
};
use crate::{
    bytecode::{Instruction, Operand},
    classfile::{
        Annotation, ClassError, ClassFile, Code, Constant, Member, RecordComponent, TypeTarget,
    },
    descriptor::{FieldSignature, MethodDescriptor, Primitive, Type},
};

impl<'a> Writer<'a, '_> {
    pub(super) fn is_component_field(
        &self,
        field: &Member<'a>,
        components: Option<&[RecordComponent<'a>]>,
    ) -> Result<bool, ClassError> {
        let Some(components) = components else {
            return Ok(false);
        };
        if field.access_flags & (VISIBILITY | STATIC | FINAL) != PRIVATE | FINAL {
            return Ok(false);
        }
        let pool = &self.class.pool;
        let name = pool.utf8(field.name_index)?;
        let descriptor = pool.utf8(field.descriptor_index)?;
        for component in components {
            if name == pool.utf8(component.name_index)?
                && descriptor == pool.utf8(component.descriptor_index)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn record_components_source(
        &self,
        components: &[RecordComponent<'a>],
    ) -> Result<Vec<Document>, DecompileError> {
        let pool = &self.class.pool;
        let mut canonical = None;
        for method in &self.class.methods {
            if pool.utf8(method.name_index)? == "<init>"
                && is_canonical(self.class, components, pool.utf8(method.descriptor_index)?)?
            {
                canonical = Some(method);
                break;
            }
        }
        let varargs = canonical.is_some_and(|method| method.access_flags & VARARGS != 0);
        let mut params = [Vec::new(), Vec::new()];
        if let Some(canonical) = canonical {
            for (index, visible) in [true, false].into_iter().enumerate() {
                params[index] = canonical.parameter_annotations(pool, visible)?;
            }
        }
        let mut rendered = Vec::with_capacity(components.len());
        for (index, component) in components.iter().enumerate() {
            let mut out = Document::new();
            let mut declarations = Vec::new();
            let name = pool.utf8(component.name_index)?;
            let descriptor = pool.utf8(component.descriptor_index)?;
            for visible in [true, false] {
                extend_unique(&mut declarations, component.annotations(pool, visible)?);
            }
            for method in &self.class.methods {
                if pool.utf8(method.name_index)? == name
                    && pool.utf8(method.descriptor_index)?.strip_prefix("()") == Some(descriptor)
                {
                    for visible in [true, false] {
                        extend_unique(&mut declarations, method.annotations(pool, visible)?);
                    }
                    break;
                }
            }
            for group in &params {
                if let Some(annotations) = group.get(index) {
                    extend_unique(&mut declarations, annotations.iter().cloned());
                }
            }
            for annotation in &declarations {
                out.append(self.annotation_document(annotation, None)?);
                out.push(' ');
            }
            let mut annotations = component.type_annotations(pool, true)?;
            annotations.extend(component.type_annotations(pool, false)?);
            let sig = if self.options.decompile_generics {
                component.signature(pool)?
            } else {
                None
            };
            let varargs = varargs && index + 1 == components.len();
            let ty = if let Some(sig) = sig {
                let ty = parse(sig, FieldSignature::parse)?;
                self.render_type_target(
                    &ty.field_type,
                    &annotations,
                    TypeTarget::Field,
                    &declarations,
                    varargs,
                )?
            } else {
                let ty = parse(descriptor, Type::parse)?;
                self.render_type_target(
                    &ty,
                    &annotations,
                    TypeTarget::Field,
                    &declarations,
                    varargs,
                )?
            };
            out.append(ty);
            out.push(' ');
            self.field_symbol(&mut out, name, name, descriptor);
            rendered.push(out);
        }
        Ok(rendered)
    }
}

fn extend_unique(queue: &mut Vec<Annotation>, additions: impl IntoIterator<Item = Annotation>) {
    for annotation in additions {
        if !queue.contains(&annotation) {
            queue.push(annotation);
        }
    }
}

pub(super) fn is_generated(
    class: &ClassFile<'_>,
    components: &[RecordComponent<'_>],
    name: &str,
    desc: &str,
    method: &Member<'_>,
    insns: &[Instruction],
) -> Result<bool, DecompileError> {
    let pool = &class.pool;
    let owner = pool.class_name(class.this_class)?;
    let annotated =
        !method.annotations(pool, true)?.is_empty() || !method.annotations(pool, false)?.is_empty();
    if !method.exceptions(pool)?.is_empty() {
        return Ok(false);
    }
    if name == "<init>"
        && !annotated
        && method.access_flags & VISIBILITY == class.access_flags & VISIBILITY
        && is_canonical(class, components, desc)?
    {
        return Ok(insns.len() == 3 + 3 * components.len()
            && record_super(class, &insns[..2])?
            && insns.last().is_some_and(|insn| insn.opcode == 0xb1)
            && component_assignments(class, components, &insns[2..insns.len() - 1])?);
    }
    if method.access_flags & (VISIBILITY | STATIC) == PUBLIC
        && let [object, access, ret] = insns
        && local_load(object, 0, 0x19)
        && let Some(returns) = desc.strip_prefix("()")
    {
        for component in components {
            if pool.utf8(component.name_index)? == name
                && pool.utf8(component.descriptor_index)? == returns
                && method_ref(class, access, 0xb4, (owner, name, returns))?
            {
                return Ok(ret.opcode == load_opcode(&parse(returns, Type::parse)?) - 0x15 + 0xac);
            }
        }
    }
    if annotated {
        return Ok(false);
    }
    let (call, returns) = match (name, desc, insns) {
        ("toString", "()Ljava/lang/String;", [a, call, ret])
            if local_load(a, 0, 0x19) && ret.opcode == 0xb0 =>
        {
            (call, "Ljava/lang/String;")
        }
        ("hashCode", "()I", [a, call, ret]) if local_load(a, 0, 0x19) && ret.opcode == 0xac => {
            (call, "I")
        }
        ("equals", "(Ljava/lang/Object;)Z", [a, b, call, ret])
            if local_load(a, 0, 0x19) && local_load(b, 1, 0x19) && ret.opcode == 0xac =>
        {
            (call, "Z")
        }
        _ => return Ok(false),
    };
    if method.access_flags & (VISIBILITY | FINAL | STATIC) != PUBLIC | FINAL || call.opcode != 0xba
    {
        return Ok(false);
    }
    let Operand::Constant(index) = call.operand else {
        return Ok(false);
    };
    let Constant::InvokeDynamic {
        bootstrap_index,
        name_and_type_index,
    } = pool.get(index)?
    else {
        return Ok(false);
    };
    let (call_name, call_desc) = pool.name_and_type(*name_and_type_index)?;
    let tail = if name == "equals" {
        "Ljava/lang/Object;"
    } else {
        ""
    };
    if call_name != name || call_desc != format!("(L{owner};{tail}){returns}") {
        return Ok(false);
    }
    let methods = class.bootstrap_methods()?;
    let Some(bootstrap) = methods.get(usize::from(*bootstrap_index)) else {
        return Ok(false);
    };
    let Constant::MethodHandle {
        reference_kind: 6,
        reference_index,
    } = pool.get(bootstrap.method_ref)?
    else {
        return Ok(false);
    };
    let (class_name, method_name, _) = pool.member_ref(*reference_index)?;
    if class_name != "java/lang/runtime/ObjectMethods"
        || method_name != "bootstrap"
        || bootstrap.arguments.len() != components.len() + 2
        || pool.class_name(bootstrap.arguments[0])? != owner
    {
        return Ok(false);
    }
    let Constant::String(names_index) = pool.get(bootstrap.arguments[1])? else {
        return Ok(false);
    };
    let names = pool.utf8(*names_index)?;
    if components.is_empty() {
        return Ok(names.is_empty());
    }
    let mut names = names.split(';');
    for (component, &handle) in components.iter().zip(&bootstrap.arguments[2..]) {
        let name = pool.utf8(component.name_index)?;
        let desc = pool.utf8(component.descriptor_index)?;
        let Constant::MethodHandle {
            reference_kind: 1,
            reference_index,
        } = pool.get(handle)?
        else {
            return Ok(false);
        };
        if names.next() != Some(name) || pool.member_ref(*reference_index)? != (owner, name, desc) {
            return Ok(false);
        }
    }
    Ok(names.next().is_none())
}

/// A compact constructor executes all component assignments implicitly, after
/// its body. Only the exact terminal writes can be erased.
pub(super) fn compact_tail(
    class: &ClassFile<'_>,
    components: &[RecordComponent<'_>],
    descriptor: &MethodDescriptor,
    method: &Member<'_>,
    code: &Code<'_>,
    insns: &[Instruction],
    parameter_names: &[String],
) -> Result<Option<std::ops::Range<usize>>, DecompileError> {
    let pool = &class.pool;
    if !is_canonical(class, components, pool.utf8(method.descriptor_index)?)?
        || method.access_flags & !(VISIBILITY | VARARGS) != 0
        || !method.exceptions(pool)?.is_empty()
        || !code.exceptions.is_empty()
        || !method.method_type_annotations(pool, true)?.is_empty()
        || !method.method_type_annotations(pool, false)?.is_empty()
        || method
            .method_parameters(pool)?
            .iter()
            .any(|parameter| parameter.access_flags & FINAL != 0)
        || !insns.last().is_some_and(|op| op.opcode == 0xb1)
    {
        return Ok(None);
    }
    let end = insns.len() - 1;
    let Some(start) = end.checked_sub(3 * components.len()).filter(|&at| at >= 2) else {
        return Ok(None);
    };
    if !record_super(class, &insns[..2])?
        || !component_assignments(class, components, &insns[start..end])?
    {
        return Ok(None);
    }
    // Compact syntax binds the component names, not the chosen debug aliases.
    // An empty body cannot refer to them.
    if start > 2 {
        for (parameter, component) in parameter_names.iter().zip(components) {
            if parameter != pool.utf8(component.name_index)? {
                return Ok(None);
            }
        }
    }
    let body_targets = insns[2].offset..=insns[start].offset;
    let first_temp = 1 + descriptor.parameters.iter().map(|ty| u32::from(ty.slots())).sum::<u32>();
    let mut debug = None;
    let owner = pool.class_name(class.this_class)?;
    for op in &insns[2..start] {
        if matches!(op.opcode, 0xac..=0xb1 | 0xa8 | 0xa9 | 0xc9)
            || match &op.operand {
                Operand::Branch(target) => !body_targets.contains(target),
                Operand::Switch { default, cases } => !body_targets.contains(default)
                    || cases.iter().any(|(_, target)| !body_targets.contains(target)),
                _ => false,
            }
        {
            return Ok(None);
        }
        if let Some((slots, read)) = op.local_access()
            && (!read || op.opcode == 0x84)
            && slots.start < first_temp
        {
            let mut index = 1;
            let binding = descriptor.parameters.iter().zip(components).find(|(ty, _)| {
                let start = index;
                index += u32::from(ty.slots());
                slots == (start..index)
            });
            let Some((ty, component)) = binding else {
                // A partial category-two write or write to `this` changes
                // the meaning of the otherwise identical terminal loads.
                return Ok(None);
            };
            let load = match op.opcode {
                0x36..=0x3a => op.opcode - 0x36 + 0x15,
                0x3b..=0x4e => (op.opcode - 0x3b) / 4 + 0x15,
                0x84 => 0x15,
                _ => unreachable!("proved a local write"),
            };
            if load != load_opcode(ty)
                || matches!(ty, Type::Primitive(Primitive::Boolean | Primitive::Byte
                    | Primitive::Short | Primitive::Char))
            {
                return Ok(None);
            }
            if debug.is_none() {
                debug = Some(code.local_variables(pool)?);
            }
            let mut candidates = debug.as_deref().unwrap_or_default()
                .iter()
                .filter(|local| u32::from(local.index) == slots.start);
            let expected_name = pool.utf8(component.name_index)?;
            let expected_type = pool.utf8(component.descriptor_index)?;
            if !candidates.next().is_some_and(|local| {
                local.start_pc == 0
                    && u32::from(local.length) > op.offset + op.len
                    && u32::from(local.length) > insns[end].offset
                    && local.name == expected_name
                    && local.descriptor == expected_type
            }) || candidates.next().is_some()
            {
                return Ok(None);
            }
        }
        if matches!(op.opcode, 0xb4 | 0xb5) && let Operand::Constant(index) = op.operand {
            let (field_owner, name, descriptor) = pool.member_ref(index)?;
            if field_owner == owner {
                for component in components {
                    if pool.utf8(component.name_index)? == name
                        && pool.utf8(component.descriptor_index)? == descriptor
                    {
                        return Ok(None);
                    }
                }
            }
        }
    }
    Ok(Some(start..end))
}

fn record_super(class: &ClassFile<'_>, prefix: &[Instruction]) -> Result<bool, ClassError> {
    let [receiver, call] = prefix else { return Ok(false) };
    Ok(local_load(receiver, 0, 0x19)
        && method_ref(class, call, 0xb7, ("java/lang/Record", "<init>", "()V"))?)
}

fn component_assignments(
    class: &ClassFile<'_>,
    components: &[RecordComponent<'_>],
    insns: &[Instruction],
) -> Result<bool, DecompileError> {
    if insns.len() != 3 * components.len() {
        return Ok(false);
    }
    let pool = &class.pool;
    let owner = pool.class_name(class.this_class)?;
    let mut slot = 1;
    for (assignment, component) in insns.chunks_exact(3).zip(components) {
        let name = pool.utf8(component.name_index)?;
        let desc = pool.utf8(component.descriptor_index)?;
        let ty = parse(desc, Type::parse)?;
        if !local_load(&assignment[0], 0, 0x19)
            || !local_load(&assignment[1], slot, load_opcode(&ty))
            || !method_ref(class, &assignment[2], 0xb5, (owner, name, desc))?
        {
            return Ok(false);
        }
        slot += ty.slots();
    }
    Ok(true)
}

fn is_canonical(
    class: &ClassFile<'_>,
    components: &[RecordComponent<'_>],
    desc: &str,
) -> Result<bool, ClassError> {
    let Some(mut rest) = desc.strip_prefix('(') else {
        return Ok(false);
    };
    for component in components {
        let Some(tail) = rest.strip_prefix(class.pool.utf8(component.descriptor_index)?) else {
            return Ok(false);
        };
        rest = tail;
    }
    Ok(rest == ")V")
}

fn local_load(insn: &Instruction, slot: u16, opcode: u8) -> bool {
    (insn.opcode == opcode && insn.operand == Operand::Local(slot))
        || (slot < 4 && insn.opcode == 0x1a + (opcode - 0x15) * 4 + slot as u8)
}

fn load_opcode(ty: &Type) -> u8 {
    match ty {
        Type::Primitive(Primitive::Long) => 0x16,
        Type::Primitive(Primitive::Float) => 0x17,
        Type::Primitive(Primitive::Double) => 0x18,
        Type::Array(_) | Type::Object(_) => 0x19,
        _ => 0x15,
    }
}

fn method_ref(
    class: &ClassFile<'_>,
    insn: &Instruction,
    opcode: u8,
    expected: (&str, &str, &str),
) -> Result<bool, ClassError> {
    if insn.opcode != opcode {
        return Ok(false);
    }
    let Operand::Constant(index) = insn.operand else {
        return Ok(false);
    };
    Ok(class.pool.member_ref(index)? == expected)
}
