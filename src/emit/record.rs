// Based on Vineflower RecordHelper and ClassWriter (Apache-2.0).
use super::{DecompileError, FINAL, PRIVATE, PUBLIC, STATIC, VARARGS, VISIBILITY, Writer, parse};
use crate::{
    bytecode::{Instruction, Operand},
    classfile::{ClassError, ClassFile, Constant, Member, RecordComponent},
    descriptor::{FieldSignature, Primitive, Type},
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

    pub(super) fn record_header(
        &self,
        out: &mut String,
        components: &[RecordComponent<'a>],
    ) -> Result<(), DecompileError> {
        let pool = &self.class.pool;
        let mut varargs = false;
        if !components.is_empty() {
            for m in &self.class.methods {
                if m.access_flags & VARARGS != 0
                    && pool.utf8(m.name_index)? == "<init>"
                    && is_canonical(self.class, components, pool.utf8(m.descriptor_index)?)?
                {
                    varargs = true;
                    break;
                }
            }
        }
        out.push('(');
        for (index, component) in components.iter().enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            for visible in [true, false] {
                for annotation in component.annotations(pool, visible)? {
                    out.push_str(&self.annotation(&annotation)?);
                    out.push(' ');
                }
            }
            let descriptor = pool.utf8(component.descriptor_index)?;
            let map_name = |name: &str| self.names.render(name);
            let sig = if self.options.decompile_generics {
                component.signature(pool)?
            } else {
                None
            };
            let ty = if let Some(sig) = sig {
                parse(sig, FieldSignature::parse)?
                    .field_type
                    .render(map_name)
            } else {
                parse(descriptor, Type::parse)?.render(map_name)
            };
            if varargs
                && index + 1 == components.len()
                && let Some(element) = ty.strip_suffix("[]")
            {
                out.push_str(element);
                out.push_str("...");
            } else {
                out.push_str(&ty);
            }
            out.push(' ');
            out.push_str(pool.utf8(component.name_index)?);
        }
        out.push(')');
        Ok(())
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
    if !method.annotations(pool, true)?.is_empty()
        || !method.annotations(pool, false)?.is_empty()
        || !method.exceptions(pool)?.is_empty()
    {
        return Ok(false);
    }
    if name == "<init>"
        && method.access_flags & VISIBILITY == class.access_flags & VISIBILITY
        && is_canonical(class, components, desc)?
    {
        if insns.len() != 3 + 3 * components.len()
            || !local_load(&insns[0], 0, 0x19)
            || !method_ref(
                class,
                &insns[1],
                0xb7,
                ("java/lang/Record", "<init>", "()V"),
            )?
            || insns.last().is_none_or(|i| i.opcode != 0xb1)
        {
            return Ok(false);
        }
        let mut slot = 1;
        for (i, component) in components.iter().enumerate() {
            let name = pool.utf8(component.name_index)?;
            let desc = pool.utf8(component.descriptor_index)?;
            let ty = parse(desc, Type::parse)?;
            let start = 2 + 3 * i;
            if !local_load(&insns[start], 0, 0x19)
                || !local_load(&insns[start + 1], slot, load_opcode(&ty))
                || !method_ref(class, &insns[start + 2], 0xb5, (owner, name, desc))?
            {
                return Ok(false);
            }
            slot += ty.slots();
        }
        return Ok(true);
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
