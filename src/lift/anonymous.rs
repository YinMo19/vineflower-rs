// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{cell::RefCell, rc::Rc};

use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::ClassFile,
    context::NestedKind,
    descriptor::{ClassSignature, MethodDescriptor, Type},
};

use super::{
    LiftError, Machine,
    expr::{Expr, Source},
    members::render_arguments,
    nested::parameter_load_slot,
};

#[path = "anonymous_capture.rs"]
mod capture;
pub(crate) use capture::AnonymousBindings;
use capture::{Capture, CaptureFrame, loaded_parameter, writes_local};

pub(crate) type AnonymousSites = Rc<RefCell<Vec<AnonymousSite>>>;

pub(crate) struct AnonymousSite {
    pub class: Rc<str>,
    pub descriptor: String,
    pub instructions: Vec<Instruction>,
    pub initializer_start: usize,
    captures: Option<Rc<[Capture]>>,
}

impl AnonymousSite {
    pub(crate) fn uncaptured(
        class: &str,
        descriptor: &str,
        instructions: Vec<Instruction>,
        initializer_start: usize,
    ) -> Self {
        Self {
            class: class.into(),
            descriptor: descriptor.into(),
            instructions,
            initializer_start,
            captures: None,
        }
    }

    pub(crate) fn capture_bindings(
        &self,
        parent: Option<AnonymousBindings>,
    ) -> Option<AnonymousBindings> {
        if let Some(captures) = &self.captures {
            return CaptureFrame::bind(&self.class, captures, parent);
        }
        parent
    }

    pub(crate) fn captures_field(&self, name: &str, descriptor: &str) -> bool {
        self.captures.as_ref().is_some_and(|captures| {
            captures
                .iter()
                .any(|capture| capture.is_field(name, descriptor))
        })
    }
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
        let Some(node) = group
            .nested_class(owner)
            .filter(|node| matches!(node.kind, NestedKind::Anonymous))
        else {
            return Ok(None);
        };
        if !group.is_attached(owner) {
            return Ok(None);
        }
        if node.outer != self.owner {
            return Err(self.unsupported("anonymous construction outside its lexical class"));
        }
        let class = group.get(owner).expect("attached class is registered");
        let pool = &class.pool;
        let fail = || self.unsupported("unrecognized anonymous constructor forwarding layout");
        let sites = self.anonymous_sites.as_ref().ok_or_else(fail)?;
        let mut constructor = None;
        for method in &class.methods {
            if pool.utf8(method.name_index)? == "<init>"
                && pool.utf8(method.descriptor_index)? == descriptor
            {
                constructor = method.code(pool)?;
                break;
            }
        }
        let code = constructor.ok_or_else(fail)?;
        let constructor_type = MethodDescriptor::parse(descriptor)?;
        let instructions = bytecode::decode(code.bytes).map_err(|_| fail())?;
        let enclosing = group.constructor_outer(owner, descriptor);
        let implicit = usize::from(enclosing.is_some());
        if let Some(enclosing) = enclosing && !args.first().is_some_and(|argument| {
            matches!(argument.source, Source::This | Source::OuterThis)
                && matches!(&argument.ty, Type::Object(ty) if group.is_assignable(ty, enclosing))
        }) {
            return Err(fail());
        }
        let mut captures = ConstructorCaptures {
            owner,
            class,
            parameters: &constructor_type.parameters,
            args,
            enclosing,
            fields: Vec::new(),
            enclosing_assigned: false,
        };
        let prefix = captures.skip_stores(self, &instructions)?;
        let remaining = instructions.get(prefix..).ok_or_else(fail)?;
        let Some((receiver, remaining)) = remaining.split_first() else {
            return Err(fail());
        };
        if receiver.opcode != 0x2a {
            return Err(fail());
        }
        let super_call = remaining
            .iter()
            .position(|op| op.opcode == 0xb7)
            .ok_or_else(fail)?;
        let super_op = &remaining[super_call];
        let Operand::Constant(super_index) = super_op.operand else {
            return Err(fail());
        };
        let (super_owner, super_name, super_descriptor) = pool.member_ref(super_index)?;
        if super_name != "<init>"
            || class.super_class == 0
            || pool.class_name(class.super_class)? != super_owner
        {
            return Err(fail());
        }
        let mut loads = &remaining[..super_call];
        let super_descriptor = if let Some((last, prefix)) = loads.split_last()
            && last.opcode == 0x01
            && let Some(target) =
                self.legacy_constructor_descriptor(super_owner, super_descriptor)?
        {
            loads = prefix;
            target
        } else {
            super_descriptor
        };
        let super_type = MethodDescriptor::parse(super_descriptor)?;
        let first = match loads.first() {
            Some(load) => {
                loaded_parameter(load, captures.parameters)
                    .ok_or_else(fail)?
                    .0
            }
            None => 0,
        };
        let last = first + loads.len();
        let prepared = captures.parameters.get(first..last).ok_or_else(fail)?;
        if prepared != super_type.parameters.as_slice()
            || loads.iter().enumerate().any(|(index, load)| {
                loaded_parameter(load, captures.parameters)
                    .is_none_or(|(ordinal, _)| ordinal != first + index)
            })
        {
            return Err(fail());
        }
        let super_end = prefix + super_call + 2;
        let initializer_start =
            super_end + captures.skip_stores(self, &instructions[super_end..])?;
        if (0..captures.parameters.len()).any(|index| {
            index >= implicit
                && !(first..last).contains(&index)
                && !captures
                    .fields
                    .iter()
                    .any(|capture| capture.parameter == index)
        }) {
            return Err(fail());
        }
        let tail = &instructions[initializer_start..];
        let first_offset = tail.first().ok_or_else(fail)?.offset;
        if code
            .exceptions
            .iter()
            .any(|handler| u32::from(handler.start_pc) < first_offset)
            || constructor_parameters_are_used(
                tail,
                captures.parameters,
                implicit,
                &captures.fields,
            )
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
                let (mut head, visible_args) = self.constructor_target(
                    super_owner,
                    super_descriptor,
                    &args[first..last],
                    None,
                )?;
                if let Some(signature) = &signature
                    && head.starts_with("new ")
                {
                    head.truncate("new ".len());
                    head.push_str(&signature.superclass.render(self.class_name));
                }
                (head, visible_args)
            }
            [interface] if super_owner == "java/lang/Object" && loads.is_empty() => {
                let name = signature
                    .as_ref()
                    .and_then(|signature| signature.interfaces.first())
                    .map_or_else(
                        || pool.class_name(*interface).map(self.class_name),
                        |interface| Ok(interface.render(self.class_name)),
                    )?;
                (format!("new {name}"), &args[first..last])
            }
            _ => return Err(fail()),
        };
        let mut sites = sites.borrow_mut();
        let id = sites.len();
        sites.push(AnonymousSite {
            class: owner.into(),
            descriptor: descriptor.into(),
            instructions,
            initializer_start,
            captures: (!captures.fields.is_empty()).then(|| captures.fields.into()),
        });
        Ok(Some(format!(
            "{head}({})\0{id}\0",
            render_arguments(visible_args)
        )))
    }
}

struct ConstructorCaptures<'a, 'c> {
    owner: &'c str,
    class: &'c ClassFile<'a>,
    parameters: &'c [Type],
    args: &'c [Expr],
    enclosing: Option<&'c str>,
    fields: Vec<Capture>,
    enclosing_assigned: bool,
}

impl ConstructorCaptures<'_, '_> {
    fn skip_stores(
        &mut self,
        machine: &Machine<'_, '_>,
        instructions: &[Instruction],
    ) -> Result<usize, LiftError> {
        let mut offset = 0;
        while let Some(capture) = machine.anonymous_capture_store(
            self.owner,
            self.class,
            self.parameters,
            self.args,
            &instructions[offset..],
            self.enclosing,
        )? {
            if let Some(capture) = capture {
                if self.fields.iter().any(|field| field.same_field(&capture)) {
                    return Err(machine.unsupported("duplicate anonymous capture store"));
                }
                self.fields.push(capture);
            } else if std::mem::replace(&mut self.enclosing_assigned, true) {
                return Err(machine.unsupported("duplicate anonymous enclosing-instance store"));
            }
            offset += 3;
        }
        Ok(offset)
    }
}

fn constructor_parameters_are_used(
    instructions: &[Instruction],
    parameters: &[Type],
    implicit: usize,
    captures: &[Capture],
) -> bool {
    let mut slot = 1u16;
    for (index, ty) in parameters.iter().enumerate() {
        let recoverable =
            index < implicit || captures.iter().any(|capture| capture.parameter == index);
        if instructions.iter().any(|op| {
            writes_local(op, slot) || (!recoverable && parameter_load_slot(op, ty) == Some(slot))
        }) {
            return true;
        }
        let Some(next) = slot.checked_add(ty.slots()) else {
            return true;
        };
        slot = next;
    }
    false
}
