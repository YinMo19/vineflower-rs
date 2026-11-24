// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{cell::RefCell, rc::Rc};

use crate::{
    bytecode::{self, Instruction, Operand},
    context::NestedKind,
    descriptor::{ClassSignature, MethodDescriptor, Type},
};

use super::{
    LiftError, Machine,
    expr::{Expr, Source},
    members::render_arguments,
    nested::parameter_load_slot,
};

pub(crate) type AnonymousSites = Rc<RefCell<Vec<AnonymousSite>>>;

pub(crate) struct AnonymousSite {
    pub class: String,
    pub descriptor: String,
    pub instructions: Vec<Instruction>,
    pub initializer_start: usize,
}

impl Machine<'_, '_> {
    pub(crate) fn set_anonymous_sites(&mut self, sites: AnonymousSites) {
        self.anonymous_sites = Some(sites);
    }

    pub(crate) fn mark_initialized_this(&mut self) {
        self.initialized_this = true;
    }

    /// Decode the synthetic constructor before rendering an anonymous class.
    /// Its enclosing instance is implicit, and its explicit arguments are
    /// forwarded exactly once and in order to the selected super constructor.
    pub(super) fn anonymous_construction(
        &self,
        owner: &str,
        descriptor: &str,
        args: &[Expr],
    ) -> Result<Option<String>, LiftError> {
        let Some(group) = self.group.filter(|_| self.options.decompile_inner) else {
            return Ok(None);
        };
        if !group.is_attached(owner)
            || !group.nested_class(owner).is_some_and(|class| matches!(class.kind, NestedKind::Anonymous))
        {
            return Ok(None);
        }
        let class = group.get(owner).expect("attached class is registered");
        let pool = &class.pool;
        let fail = || self.unsupported("unrecognized anonymous constructor forwarding layout");
        let sites = self.anonymous_sites.as_ref().ok_or_else(fail)?;
        let mut constructor = None;
        for method in &class.methods {
            if pool.utf8(method.name_index)? == "<init>" && pool.utf8(method.descriptor_index)? == descriptor {
                constructor = method.code(pool)?;
                break;
            }
        }
        let code = constructor.ok_or_else(fail)?;
        let constructor_type = MethodDescriptor::parse(descriptor)?;
        let instructions = bytecode::decode(code.bytes).map_err(|_| fail())?;
        let enclosing = group.constructor_outer(owner, descriptor);
        let implicit = usize::from(enclosing.is_some());
        if let Some(enclosing) = enclosing
            && !args.first().is_some_and(|argument| {
                matches!(argument.source, Source::This | Source::OuterThis)
                    && matches!(&argument.ty, Type::Object(ty) if group.is_assignable(ty, enclosing))
            })
        {
            return Err(fail());
        }
        let mut prefix = 0;
        if let Some([receiver, parameter, field, ..]) = instructions.get(prefix..)
            && receiver.opcode == 0x2a && field.opcode == 0xb5
            && let Operand::Constant(index) = field.operand
        {
            let (field_owner, name, field_descriptor) = pool.member_ref(index)?;
            if field_owner != owner || enclosing.is_none()
                || group.outer_field(owner, name, field_descriptor) != enclosing
                || constructor_type.parameters.first().and_then(|ty| parameter_load_slot(parameter, ty)) != Some(1)
            {
                return Err(self.unsupported("captured local variables in an anonymous class"));
            }
            prefix += 3;
        }
        let remaining = instructions.get(prefix..).ok_or_else(fail)?;
        let Some((receiver, remaining)) = remaining.split_first() else { return Err(fail()) };
        if receiver.opcode != 0x2a {
            return Err(fail());
        }
        let super_call = remaining.iter().position(|op| op.opcode == 0xb7).ok_or_else(fail)?;
        let super_op = &remaining[super_call];
        let Operand::Constant(super_index) = super_op.operand else { return Err(fail()) };
        let (super_owner, super_name, super_descriptor) = pool.member_ref(super_index)?;
        if super_name != "<init>" || class.super_class == 0 || pool.class_name(class.super_class)? != super_owner {
            return Err(fail());
        }
        let super_type = MethodDescriptor::parse(super_descriptor)?;
        let loads = &remaining[..super_call];
        let first = constructor_type.parameters.len().checked_sub(loads.len()).ok_or_else(fail)?;
        let prepared = &constructor_type.parameters[first..];
        if first > implicit || prepared != super_type.parameters.as_slice() {
            return Err(fail());
        }
        let mut slot = 1 + constructor_type.parameters[..first].iter().map(Type::slots).sum::<u16>();
        for (load, ty) in loads.iter().zip(prepared) {
            if parameter_load_slot(load, ty) != Some(slot) {
                return Err(fail());
            }
            slot += ty.slots();
        }
        let initializer_start = prefix + super_call + 2;
        let tail = &instructions[initializer_start..];
        let first_offset = tail.first().ok_or_else(fail)?.offset;
        if code.exceptions.iter().any(|handler| u32::from(handler.start_pc) < first_offset)
            || constructor_parameters_are_used(tail, &constructor_type.parameters, implicit)
        {
            return Err(fail());
        }
        let signature = if self.options.decompile_generics {
            class.signature()?.map(ClassSignature::parse).transpose()?
        } else {
            None
        };
        let (head, visible_args) = match &class.interfaces[..] {
            [] => {
                let (mut head, visible_args) = self.constructor_target(super_owner, super_descriptor, &args[first..], None)?;
                if let Some(signature) = &signature && head.starts_with("new ") {
                    head.truncate("new ".len());
                    head.push_str(&signature.superclass.render(self.class_name));
                }
                (head, visible_args)
            }
            [interface] if super_owner == "java/lang/Object" && loads.is_empty() => {
                let name = signature.as_ref().and_then(|signature| signature.interfaces.first())
                    .map_or_else(
                        || pool.class_name(*interface).map(self.class_name),
                        |interface| Ok(interface.render(self.class_name)),
                    )?;
                (format!("new {name}"), &args[first..])
            }
            _ => return Err(fail()),
        };
        let mut sites = sites.borrow_mut();
        let id = sites.len();
        sites.push(AnonymousSite {
            class: owner.into(), descriptor: descriptor.into(), instructions, initializer_start,
        });
        Ok(Some(format!("{head}({})\0{id}\0", render_arguments(visible_args))))
    }
}

fn constructor_parameters_are_used(instructions: &[Instruction], parameters: &[Type], implicit: usize) -> bool {
    let mut slot = 1;
    for (index, ty) in parameters.iter().enumerate() {
        if index >= implicit && instructions.iter().any(|op| {
            parameter_load_slot(op, ty) == Some(slot)
                || matches!(op.operand, Operand::Increment { index, .. } if index == slot)
        }) {
            return true;
        }
        slot += ty.slots();
    }
    false
}
