// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::rc::Rc;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{ClassFile, find_attribute},
    descriptor::Type,
    source_text::Document,
};

use super::super::{
    Effect, LiftError, Machine,
    expr::{Expr, Source},
    nested::parameter_load_slot,
};
use super::local::LocalPlan;
use crate::lift::locals::LexicalNames;

pub(crate) type AnonymousBindings = Rc<CaptureFrame>;

pub(crate) struct CaptureFrame {
    owner: Rc<str>,
    captures: Rc<[Capture]>,
    parent: Option<AnonymousBindings>,
    plan: Option<Rc<LocalPlan>>,
    enclosing_names: Option<LexicalNames>,
}

pub(super) struct Capture {
    pub(super) parameter: usize,
    pub(super) slot: u16,
    field: String,
    descriptor: String,
    name: Document,
    ty: Type,
    origin: CaptureOrigin,
}

#[derive(PartialEq, Eq)]
pub(super) enum CaptureOrigin {
    Local {
        slot: u16,
        range: Option<(u16, u16)>,
        declaration: Option<u32>,
        parameter: bool,
    },
    EnclosingCapture,
}
impl Capture {
    pub(super) fn new(
        parameter: usize,
        slot: u16,
        field: &str,
        descriptor: &str,
        name: &Document,
        ty: Type,
        origin: CaptureOrigin,
    ) -> Self {
        Self {
            parameter,
            slot,
            field: field.into(),
            descriptor: descriptor.into(),
            name: name.clone(),
            ty,
            origin,
        }
    }

    pub(super) fn same_lexical_binding(&self, other: &Self) -> bool {
        self.name == other.name && self.origin == other.origin
    }

    pub(super) fn declaration(&self) -> Option<u32> {
        match self.origin {
            CaptureOrigin::Local { declaration, .. } => declaration,
            CaptureOrigin::EnclosingCapture => None,
        }
    }

    pub(super) fn matches_capture_argument(&self, argument: &Expr) -> bool {
        matches!(argument.source, Source::CapturedLocal)
            && self.ty == argument.ty
            && self.name == argument.text.as_str()
    }

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
        owner: Rc<str>,
        captures: Rc<[Capture]>,
        parent: Option<AnonymousBindings>,
        enclosing_names: Option<LexicalNames>,
    ) -> AnonymousBindings {
        Rc::new(Self {
            owner,
            captures,
            parent,
            plan: None,
            enclosing_names,
        })
    }

    pub(super) fn named(
        owner: Rc<str>,
        captures: Rc<[Capture]>,
        plan: Rc<LocalPlan>,
        parent: Option<AnonymousBindings>,
        enclosing_names: LexicalNames,
    ) -> AnonymousBindings {
        Rc::new(Self {
            owner,
            captures,
            plan: Some(plan),
            parent,
            enclosing_names: Some(enclosing_names),
        })
    }

    pub(super) fn named_frame(&self, owner: &str) -> Option<(&Rc<LocalPlan>, &[Capture])> {
        let frame = self.frame(owner)?;
        Some((frame.plan.as_ref()?, &frame.captures))
    }

    pub(crate) fn local_constructor_capture_count(&self, owner: &str, descriptor: &str) -> usize {
        self.named_frame(owner)
            .and_then(|(plan, _)| plan.constructor(descriptor))
            .map_or(0, <[_]>::len)
    }

    pub(crate) fn captures_field(&self, owner: &str, name: &str, descriptor: &str) -> bool {
        self.frame(owner).is_some_and(|frame| {
            frame
                .captures
                .iter()
                .any(|capture| capture.is_field(name, descriptor))
        })
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

    pub(in crate::lift) fn enclosing_names(&self, owner: &str) -> Option<&LexicalNames> {
        self.frame(owner)?.enclosing_names.as_ref()
    }

    fn reserve_names(&self, locals: &crate::lift::locals::Locals<'_>) {
        let mut frame = Some(self);
        while let Some(candidate) = frame {
            for capture in &*candidate.captures {
                locals.reserve_capture_name(capture.name.as_str());
            }
            frame = candidate.parent.as_deref();
        }
    }

    pub(in crate::lift) fn binds_name(&self, name: &str) -> bool {
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
        if let Some(bindings) = &bindings {
            bindings.reserve_names(&self.locals);
        }
        self.anonymous_bindings = bindings;
    }

    pub(in crate::lift) fn captured_parameter(&self, index: u16) -> Option<Expr> {
        if self.method_name != "<init>" {
            return None;
        }
        let frame = self.anonymous_bindings.as_deref()?.frame(self.owner)?;
        if let Some(plan) = &frame.plan {
            let descriptor = self.class.pool.utf8(self.method.descriptor_index).ok()?;
            let argument = plan
                .constructor(descriptor)?
                .iter()
                .find(|argument| argument.slot == index)?;
            return frame.captures.get(argument.field).map(Capture::expression);
        }
        frame
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
        let Some((frame, index, capture)) = self
            .anonymous_bindings
            .as_deref()
            .and_then(|bindings| bindings.frame(owner))
            .and_then(|frame| {
                frame
                    .captures
                    .iter()
                    .enumerate()
                    .find(|(_, capture)| capture.is_field(field, descriptor))
                    .map(|(index, capture)| (frame, index, capture))
            })
        else {
            return Ok(None);
        };
        if !matches!(receiver.source, Source::This | Source::OuterThis)
            || value.is_some() && !matches!(receiver.source, Source::This)
            || !matches!(&receiver.ty, Type::Object(ty) if ty == owner)
        {
            return Err(self.unsupported("nonlexical access to a captured local variable"));
        }
        let constructor = if self.method_name == "<init>" && owner == self.owner {
            if let Some(plan) = &frame.plan {
                let descriptor = self.class.pool.utf8(self.method.descriptor_index)?;
                plan.constructor(descriptor)
                    .and_then(|arguments| arguments.get(index))
                    .map(|argument| (argument.slot, argument.store))
            } else {
                Some((capture.slot, None))
            }
        } else {
            None
        };
        if let Some(value) = value {
            if constructor.and_then(|(_, store)| store) == Some(self.debug_offset(self.offset))
                && capture.matches_capture_argument(value)
            {
                return Ok(Some(Effect::None));
            }
            return Err(self.unsupported("noninitial write to a captured local variable"));
        }
        if (0..self.code.max_locals).any(|slot| {
            !constructor.is_some_and(|(implicit, _)| slot == implicit)
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
        let Some(CaptureStore {
            field,
            descriptor,
            ordinal,
            slot,
            ..
        }) = capture_store(class, owner, parameters, instructions)?
        else {
            return Ok(None);
        };
        let fail = || self.unsupported("unrecognized anonymous capture assignment");
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
        let origin = self.capture_argument(arg).ok_or_else(|| {
            self.unsupported("anonymous capture is not an effectively final lexical variable")
        })?;
        Ok(Some(Some(Capture::new(
            ordinal, slot, field, descriptor, &arg.text, ty, origin,
        ))))
    }

    pub(super) fn capture_argument(&self, arg: &Expr) -> Option<CaptureOrigin> {
        if arg.observable {
            return None;
        }
        match arg.source {
            Source::Local(slot) => self.effectively_final_capture(slot, arg.text.as_str()),
            Source::CapturedLocal
                if self
                    .anonymous_bindings
                    .as_deref()
                    .is_some_and(|bindings| bindings.binds_name(arg.text.as_str())) =>
            {
                Some(CaptureOrigin::EnclosingCapture)
            }
            _ => None,
        }
    }

    fn effectively_final_capture(&self, slot: u16, name: &str) -> Option<CaptureOrigin> {
        let (range, parameter) = self.local_capture_binding(slot, name)?;
        let mut declaration = None;
        for op in self
            .anonymous_source?
            .iter()
            .filter(|op| writes_local(op, slot))
        {
            let offset = self.debug_offset(op.offset);
            if let Some((start, len)) = range {
                let start = u32::from(start);
                if !parameter
                    && op.opcode != 0x84
                    && (offset == start || self.debug_offset(op.offset + op.len) == start)
                {
                    if declaration
                        .replace(offset)
                        .is_some_and(|prev| prev != offset)
                    {
                        return None;
                    }
                } else if start <= offset && offset < start + u32::from(len) {
                    return None;
                }
            } else {
                if parameter
                    || op.opcode == 0x84
                    || declaration
                        .replace(offset)
                        .is_some_and(|prev| prev != offset)
                {
                    return None;
                }
            }
        }
        Some(CaptureOrigin::Local {
            slot,
            range,
            declaration,
            parameter,
        })
    }
}

pub(super) struct CaptureStore<'a> {
    pub(super) field: &'a str,
    pub(super) descriptor: &'a str,
    pub(super) ordinal: usize,
    pub(super) slot: u16,
    pub(super) offset: u32,
}

/// Recognize a separately verified `aload_0; load parameter; putfield` capture.
pub(super) fn capture_store<'a>(
    class: &'a ClassFile<'_>,
    owner: &str,
    parameters: &[Type],
    instructions: &[Instruction],
) -> Result<Option<CaptureStore<'a>>, LiftError> {
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
    for member in &class.fields {
        if pool.utf8(member.name_index)? != field
            || pool.utf8(member.descriptor_index)? != descriptor
        {
            continue;
        }
        if member.access_flags & (0x0008 | 0x0010) != 0x0010
            || (member.access_flags & 0x1000 == 0
                && find_attribute(&member.attributes, pool, "Synthetic")?.is_none())
        {
            return Ok(None);
        }
        let fail = || LiftError::Unsupported {
            offset: put.offset,
            opcode: put.opcode,
            reason: "unrecognized lexical capture assignment",
        };
        let (ordinal, slot) = loaded_parameter(parameter, parameters).ok_or_else(fail)?;
        if parameters[ordinal] != Type::parse(descriptor)? {
            return Err(fail());
        }
        return Ok(Some(CaptureStore {
            field,
            descriptor,
            ordinal,
            slot,
            offset: put.offset,
        }));
    }
    Ok(None)
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
