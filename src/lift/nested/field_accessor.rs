use crate::{
    bytecode::{Instruction, Operand},
    classfile::{ClassError, ClassFile, Constant, ConstantPool, find_attribute},
    context::NestedKind,
    descriptor::{MethodDescriptor, Type},
};

use super::{Effect, Expr, LiftError, Machine, PRIMARY, Source, parameter_load_slot};
use crate::lift::assignment_expr::{Binary, Form, one_instruction, store_dup_opcode};

#[cfg(test)]
mod tests;

enum Action {
    Read,
    WriteVoid,
    WriteValue(Form),
}

pub(super) struct FieldAccessor<'a> {
    name: &'a str,
    descriptor: &'a str,
    ty: Type,
    is_static: bool,
    action: Action,
}

impl<'a> FieldAccessor<'a> {
    /// Match the whole body except for the already checked return. In
    /// particular, the position of the duplication proves which value returns.
    pub(super) fn recognize(
        class: &'a ClassFile<'_>,
        owner: &str,
        signature: &MethodDescriptor,
        ops: &[Instruction],
        max_stack: u16,
    ) -> Result<Option<Self>, LiftError> {
        let Some((member, mut ops)) = ops.split_last() else {
            return Ok(None);
        };
        let (is_static, write) = match member.opcode {
            0xb2 => (true, false),
            0xb3 => (true, true),
            0xb4 => (false, false),
            0xb5 => (false, true),
            _ => return Ok(None),
        };
        let pool = &class.pool;
        let Some(field @ (target_owner, name, descriptor)) = field_ref(pool, member)? else {
            return Ok(None);
        };
        if target_owner != owner {
            return Ok(None);
        }
        let mut declared = false;
        for member in &class.fields {
            if pool.utf8(member.name_index)? == name
                && pool.utf8(member.descriptor_index)? == descriptor
            {
                if (member.access_flags & 0x0008 != 0) != is_static
                    || write && member.access_flags & 0x0010 != 0
                    || member.access_flags & 0x1000 != 0
                    || find_attribute(&member.attributes, pool, "Synthetic")?.is_some()
                {
                    return Ok(None);
                }
                declared = true;
                break;
            }
        }
        if !declared {
            return Ok(None);
        }
        let ty = Type::parse(descriptor)?;
        let mut parameters = signature.parameters.as_slice();
        if !is_static {
            let ([receiver @ Type::Object(receiver_owner), rest @ ..], [load, body @ ..]) =
                (parameters, ops)
            else {
                return Ok(None);
            };
            if receiver_owner != owner || parameter_load_slot(load, receiver) != Some(0) {
                return Ok(None);
            }
            parameters = rest;
            ops = body;
        }
        let address = u8::from(!is_static);
        let address_slots = u16::from(address);
        let returns_value = signature.return_type == ty;
        let action = if !write {
            if !parameters.is_empty()
                || !ops.is_empty()
                || !returns_value
                || max_stack < address_slots.max(ty.slots())
            {
                return Ok(None);
            }
            Action::Read
        } else if parameters == std::slice::from_ref(&ty) {
            let (load, retained) = match ops {
                [load] if signature.return_type == Type::Void => (load, false),
                [load, dup] if returns_value && dup.opcode == store_dup_opcode(&ty, address) => {
                    (load, true)
                }
                _ => return Ok(None),
            };
            if parameter_load_slot(load, &ty) != Some(address_slots)
                || max_stack < address_slots + ty.slots() * (1 + u16::from(retained))
            {
                return Ok(None);
            }
            if retained {
                Action::WriteValue(Form::Assign)
            } else {
                Action::WriteVoid
            }
        } else if parameters.is_empty() && returns_value {
            let read_opcode = if is_static { 0xb2 } else { 0xb4 };
            let (read, update) = match ops {
                [read, update @ ..] if is_static => (read, update),
                [dup, read, update @ ..] if !is_static && dup.opcode == 0x59 => (read, update),
                _ => return Ok(None),
            };
            if read.opcode != read_opcode || field_ref(pool, read)? != Some(field) {
                return Ok(None);
            }
            let Some(form) = increment(pool, &ty, address, update, max_stack) else {
                return Ok(None);
            };
            Action::WriteValue(form)
        } else {
            return Ok(None);
        };
        Ok(Some(Self {
            name,
            descriptor,
            ty,
            is_static,
            action,
        }))
    }
}

fn field_ref<'a>(
    pool: &'a ConstantPool<'_>,
    op: &Instruction,
) -> Result<Option<(&'a str, &'a str, &'a str)>, ClassError> {
    let Operand::Constant(index) = op.operand else {
        return Ok(None);
    };
    if !matches!(pool.get(index)?, Constant::Fieldref { .. }) {
        return Ok(None);
    }
    pool.member_ref(index).map(Some)
}

fn increment(
    pool: &ConstantPool<'_>,
    ty: &Type,
    address: u8,
    ops: &[Instruction],
    max_stack: u16,
) -> Option<Form> {
    let dup_opcode = store_dup_opcode(ty, address);
    let (postfix, one, operation, tail) = match ops {
        [dup, one, operation, tail @ ..] if dup.opcode == dup_opcode => {
            (true, one, operation, tail)
        }
        [one, operation, tail @ .., dup] if dup.opcode == dup_opcode => {
            (false, one, operation, tail)
        }
        _ => return None,
    };
    let narrow = match tail {
        [] => None,
        [op] if matches!(op.opcode, 0x91..=0x93) => Some(op.opcode),
        _ => return None,
    };
    let binary = Binary::of(operation.opcode)?;
    let text = binary.increment()?;
    let one = one_instruction(pool, one, binary.right)?;
    if !binary.assignment_conversion(ty, &one, narrow)
        || max_stack < u16::from(address) + ty.slots() * (2 + u16::from(postfix))
    {
        return None;
    }
    Some(Form::Increment { text, postfix })
}

impl Machine<'_, '_> {
    pub(super) fn emit_field_accessor(
        &mut self,
        owner: &str,
        signature: &MethodDescriptor,
        args: &[Expr],
        field: FieldAccessor<'_>,
    ) -> Result<Effect, LiftError> {
        let fail = || self.unsupported("synthetic nest field is not nameable here");
        let (mut target, passed) = if field.is_static {
            if self.group.is_some_and(|group| {
                group
                    .nested_class(owner)
                    .is_some_and(|class| matches!(class.kind, NestedKind::Anonymous))
            }) {
                return Err(fail());
            }
            (self.class_reference(owner), args)
        } else {
            let (receiver, passed) = args.split_first().ok_or_else(fail)?;
            if self.unnamed_enclosing_receiver(receiver) {
                return Err(fail());
            }
            let target = if receiver.ty == signature.parameters[0]
                && !matches!(receiver.source, Source::Null)
            {
                receiver.at(PRIMARY).into_owned()
            } else {
                self.member_receiver(receiver.clone(), owner, false)?
                    .into_at(PRIMARY)
            };
            (target, passed)
        };
        target.push('.');
        let source = self.source_field_name(owner, field.name, field.descriptor);
        self.append_field_reference(&mut target, source, owner, field.name, field.descriptor);
        match field.action {
            Action::Read => {
                self.push(self.expression(field.ty, target, PRIMARY, args, true)?)?;
            }
            Action::WriteVoid => {
                let [value] = passed else { return Err(fail()) };
                let order = self.order_of(args, true)?;
                self.before_statement(order)?;
                return Ok(Effect::FieldAssignment {
                    target,
                    value: value.text.clone(),
                });
            }
            Action::WriteValue(form) => {
                // If the caller computes an operator through a separate getter
                // before calling a setter, that computation stays in the RHS.
                // Folding it into a compound store would need an independent
                // proof that the receiver and evaluation order are unchanged.
                let right = if matches!(form, Form::Assign) {
                    let [value] = passed else { return Err(fail()) };
                    Some(value.text.clone())
                } else {
                    None
                };
                let (text, precedence) = form.render(target, right);
                let mut expression = self.expression(field.ty, text, precedence, args, true)?;
                expression.statement = true;
                self.push(expression)?;
            }
        }
        Ok(Effect::None)
    }
}
