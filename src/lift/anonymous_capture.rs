// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::rc::Rc;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{ClassFile, find_attribute},
    descriptor::Type,
};

use super::super::{
    Effect, LiftError, Machine,
    expr::{Expr, Source},
    nested::parameter_load_slot,
};

pub(crate) type AnonymousBindings = Rc<CaptureFrame>;

pub(crate) struct CaptureFrame {
    owner: Rc<str>,
    captures: Rc<[Capture]>,
    parent: Option<AnonymousBindings>,
}

pub(super) struct Capture {
    pub(super) parameter: usize,
    pub(super) slot: u16,
    field: String,
    descriptor: String,
    name: String,
    ty: Type,
}

impl Capture {
    fn expression(&self) -> Expr {
        Expr {
            source: Source::CapturedLocal,
            ..Expr::atom(self.ty.clone(), self.name.clone())
        }
    }

    pub(super) fn is_field(&self, field: &str, descriptor: &str) -> bool {
        self.field == field && self.descriptor == descriptor
    }

    pub(super) fn same_field(&self, other: &Self) -> bool {
        self.is_field(&other.field, &other.descriptor)
    }
}

impl CaptureFrame {
    pub(super) fn bind(
        owner: &Rc<str>,
        captures: &Rc<[Capture]>,
        parent: Option<AnonymousBindings>,
    ) -> Option<AnonymousBindings> {
        if captures.is_empty() {
            parent
        } else {
            Some(Rc::new(Self {
                owner: Rc::clone(owner),
                captures: Rc::clone(captures),
                parent,
            }))
        }
    }

    fn frame(&self, owner: &str) -> Option<&Self> {
        let mut frame = Some(self);
        while let Some(candidate) = frame {
            if &*candidate.owner == owner {
                return frame;
            }
            frame = candidate.parent.as_deref();
        }
        None
    }

    fn binds_name(&self, name: &str) -> bool {
        let mut frame = Some(self);
        while let Some(candidate) = frame {
            if candidate
                .captures
                .iter()
                .any(|capture| capture.name == name)
            {
                return true;
            }
            frame = candidate.parent.as_deref();
        }
        false
    }
}

impl<'a, 'c> Machine<'a, 'c> {
    pub(crate) fn set_anonymous_source(&mut self, instructions: &'c [Instruction]) {
        self.anonymous_source = Some(instructions);
    }
}

impl Machine<'_, '_> {
    pub(crate) fn set_anonymous_bindings(&mut self, bindings: Option<AnonymousBindings>) {
        self.anonymous_bindings = bindings;
    }

    pub(in crate::lift) fn captured_parameter(&self, index: u16) -> Option<Expr> {
        if self.method_name != "<init>" {
            return None;
        }
        self.anonymous_bindings
            .as_deref()?
            .frame(self.owner)?
            .captures
            .iter()
            .find(|capture| capture.slot == index)
            .map(Capture::expression)
    }

    pub(in crate::lift) fn synthetic_anonymous_capture(
        &mut self,
        owner: &str,
        field: &str,
        descriptor: &str,
        receiver: &Expr,
        value: Option<&Expr>,
    ) -> Result<Option<Effect>, LiftError> {
        let Some(capture) = self
            .anonymous_bindings
            .as_deref()
            .and_then(|bindings| bindings.frame(owner))
            .and_then(|bindings| {
                bindings
                    .captures
                    .iter()
                    .find(|capture| capture.is_field(field, descriptor))
            })
        else {
            return Ok(None);
        };
        if value.is_some()
            || !matches!(receiver.source, Source::This | Source::OuterThis)
            || !matches!(&receiver.ty, Type::Object(ty) if ty == owner)
        {
            return Err(self.unsupported("nonlexical access to a captured local variable"));
        }
        if (0..self.code.max_locals).any(|slot| {
            !(self.method_name == "<init>" && owner == self.owner && slot == capture.slot)
                && self.local_capture_binding(slot, &capture.name).is_some()
        }) {
            return Err(self.unsupported("captured local variable is shadowed"));
        }
        let expression = capture.expression();
        self.push(expression)?;
        Ok(Some(Effect::None))
    }

    /// A javac capture store reads an actual constructor parameter and writes
    /// to a final synthetic instance field on this object. Never replace an
    /// arbitrary argument expression with a source variable in a later call.
    pub(super) fn anonymous_capture_store(
        &self,
        owner: &str,
        class: &ClassFile<'_>,
        parameters: &[Type],
        args: &[Expr],
        instructions: &[Instruction],
        enclosing: Option<&str>,
    ) -> Result<Option<Option<Capture>>, LiftError> {
        const FIELD_STORAGE: u16 = 0x0008 | 0x0010;
        let [receiver, parameter, put, ..] = instructions else {
            return Ok(None);
        };
        if receiver.opcode != 0x2a || put.opcode != 0xb5 {
            return Ok(None);
        }
        let Operand::Constant(index) = put.operand else {
            return Ok(None);
        };
        let pool = &class.pool;
        let (field_owner, field, descriptor) = pool.member_ref(index)?;
        if field_owner != owner {
            return Ok(None);
        }
        let mut synthetic = false;
        for member in &class.fields {
            if pool.utf8(member.name_index)? == field
                && pool.utf8(member.descriptor_index)? == descriptor
            {
                synthetic = member.access_flags & FIELD_STORAGE == 0x0010
                    && (member.access_flags & 0x1000 != 0
                        || find_attribute(&member.attributes, pool, "Synthetic")?.is_some());
                break;
            }
        }
        if !synthetic {
            return Ok(None);
        }
        let fail = || self.unsupported("unrecognized anonymous capture assignment");
        let (ordinal, slot) = loaded_parameter(parameter, parameters).ok_or_else(fail)?;
        if self
            .group
            .and_then(|group| group.outer_field(owner, field, descriptor))
            .is_some()
        {
            if enclosing.is_none() || ordinal != 0 {
                return Err(fail());
            }
            return Ok(Some(None));
        }
        let ty = Type::parse(descriptor)?;
        let arg = args.get(ordinal).ok_or_else(fail)?;
        if parameters[ordinal] != ty || arg.observable {
            return Err(fail());
        }
        let is_local = match arg.source {
            Source::Local(index) => self.is_effectively_final_capture(index, &arg.text),
            Source::CapturedLocal => self
                .anonymous_bindings
                .as_deref()
                .is_some_and(|bindings| bindings.binds_name(&arg.text)),
            _ => false,
        };
        if !is_local {
            return Err(
                self.unsupported("anonymous capture is not an effectively final lexical variable")
            );
        }
        Ok(Some(Some(Capture {
            parameter: ordinal,
            slot,
            field: field.into(),
            descriptor: descriptor.into(),
            name: arg.text.clone(),
            ty,
        })))
    }

    fn is_effectively_final_capture(&self, slot: u16, name: &str) -> bool {
        let Some((range, parameter)) = self.local_capture_binding(slot, name) else {
            return false;
        };
        let Some(instructions) = self.anonymous_source else {
            return false;
        };
        let mut first_store = None;
        for op in instructions.iter().filter(|op| writes_local(op, slot)) {
            let Some(offset) = self
                .normalized
                .map_or(Some(op.offset), |mapping| mapping.source_offset(op.offset))
            else {
                continue;
            };
            if let Some((start, len)) = range {
                let start = u32::from(start);
                if offset < start || offset >= start + u32::from(len) {
                    continue;
                }
                if !parameter && offset == start && op.opcode != 0x84 {
                    continue;
                }
                return false;
            }
            if parameter || op.opcode == 0x84 || first_store.is_some_and(|first| first != offset) {
                return false;
            }
            first_store = Some(offset);
        }
        true
    }
}

pub(super) fn loaded_parameter(
    instruction: &Instruction,
    parameters: &[Type],
) -> Option<(usize, u16)> {
    let mut slot = 1u16;
    for (ordinal, ty) in parameters.iter().enumerate() {
        if parameter_load_slot(instruction, ty) == Some(slot) {
            return Some((ordinal, slot));
        }
        slot = slot.checked_add(ty.slots())?;
    }
    None
}

pub(super) fn writes_local(instruction: &Instruction, slot: u16) -> bool {
    match (instruction.opcode, &instruction.operand) {
        (0x36..=0x3a, Operand::Local(index)) | (0x84, Operand::Increment { index, .. }) => {
            *index == slot
        }
        (opcode @ 0x3b..=0x4e, _) => u16::from((opcode - 0x3b) % 4) == slot,
        _ => false,
    }
}
