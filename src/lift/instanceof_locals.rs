use crate::classfile::{TypeArgumentTarget, TypeTarget};
use crate::descriptor::Primitive;

use super::{Category, Effect, Instruction, LiftError, Local, Machine, Source, Type};
use crate::source_text::Document;

/// A local introduced by the successful flow of an `instanceof` expression.
/// It is prepared at the test but never installed in the failing arm.
pub(crate) struct IfPatternLocal {
    slot: u16,
    local: Local,
}

impl IfPatternLocal {
    pub(crate) fn slot(&self) -> u16 {
        self.slot
    }
}

impl Machine<'_, '_> {
    pub(crate) fn supports_instanceof_patterns(&self) -> bool {
        self.class.major_version >= 60
            || self.class.major_version >= 58 && self.class.minor_version == u16::MAX
    }

    pub(crate) fn supports_unnamed_record_components(&self) -> bool {
        self.class.major_version >= 66
            || self.class.major_version == 65 && self.class.minor_version == u16::MAX
    }

    pub(crate) fn unnamed_record_component(&self, ty: Option<&Type>) -> Document {
        let Some(ty) = ty else { return Document::from("_"); };
        let mut text = self.local_type_document(ty);
        text.push_str(" _");
        text
    }

    pub(crate) fn record_component_covers(&self, declared: &Type, tested: &Type) -> bool {
        self.pattern_covers(declared, tested)
            // Bootstrap numeric wrappers have a known superclass even
            // when no runtime class path was supplied.
            || matches!((declared, tested), (Type::Object(a), Type::Object(b))
                if a == "java/lang/Number" && matches!(crate::lift::boxing::unboxed(b),
                    Some(Primitive::Byte | Primitive::Short | Primitive::Int
                        | Primitive::Long | Primitive::Float | Primitive::Double)))
    }

    pub(crate) fn if_pattern_alias_unnamed(&self, store: &Instruction, slot: u16) -> bool {
        let start = self.debug_offset(store.offset);
        let end = self.debug_offset(store.offset + store.len - 1) + 1;
        self.locals.debug_at(slot, start).is_none() && self.locals.debug_at(slot, end).is_none()
    }

    pub(crate) fn if_pattern_selector(&self, pattern: &Type) -> bool {
        self.stack.last().is_some_and(|value| {
            Category::of(&value.ty) == Some(Category::Ref)
                && !matches!(value.source, Source::New(_) | Source::Null)
                // Before Java 21 source rejects an unconditional type pattern.
                // Leave it alone on later class files as well: no need to
                // manufacture a pattern from a redundant type check.
                && !self.known_assignable(&value.ty, pattern)
        })
    }

    pub(crate) fn prepare_if_pattern_local(
        &self,
        ty: &Type,
        cast: &Instruction,
        store: &Instruction,
        slot: u16,
    ) -> Result<Option<IfPatternLocal>, LiftError> {
        self.prepare_if_binding(ty, Some(cast), store, slot)
    }

    fn prepare_if_binding(
        &self,
        ty: &Type,
        cast: Option<&Instruction>,
        store: &Instruction,
        slot: u16,
    ) -> Result<Option<IfPatternLocal>, LiftError> {
        let index = usize::from(slot);
        let width = usize::from(ty.slots());
        let Some(previous) = self.locals.slots.get(index..index + width) else {
            return Ok(None);
        };
        if index > 0
            && self.locals.slots[index - 1]
                .as_ref()
                .is_some_and(|local| local.ty.slots() == 2)
        {
            return Ok(None);
        }
        if let Some(cast) = cast
            && let Ok(offset) = u16::try_from(self.debug_offset(cast.offset))
            && self
                .render_code_type(
                    ty,
                    TypeTarget::TypeArgument {
                        kind: TypeArgumentTarget::Cast,
                        offset,
                        argument: 0,
                    },
                )?
                .is_some()
        {
            // The cast annotation does not annotate the instanceof target.
            return Ok(None);
        }
        let start = self.debug_offset(store.offset);
        let end = self.debug_offset(store.offset + store.len - 1) + 1;
        let debug = self
            .locals
            .debug_at(slot, end)
            .or_else(|| self.locals.debug_at(slot, start));
        if debug.is_some_and(|entry| Type::parse(entry.descriptor).ok().as_ref() != Some(ty)) {
            return Ok(None);
        }
        if previous.iter().flatten().any(|local| {
            local.receiver
                || local
                    .debug_range
                    .is_none_or(|(first, size)| u32::from(first) + u32::from(size) > start)
        }) {
            // A new pattern declaration would shadow a live variable instead
            // of assigning to it. An expired, debug-proven range may be reused.
            return Ok(None);
        }
        let name = self.locals.local_name(slot, ty, debug);
        let debug_range = debug.map(|entry| (entry.start_pc, entry.length));
        Ok(Some(IfPatternLocal {
            slot,
            local: Local {
                name,
                ty: ty.clone(),
                generic: None,
                anonymous_site: None,
                debug_range,
                receiver: false,
                token_index: self.locals.new_local_token_index(slot),
            },
        }))
    }

    pub(crate) fn prepare_record_if_component(
        &self,
        ty: &Type,
        cast: Option<&Instruction>,
        store: &Instruction,
        slot: u16,
    ) -> Result<(Document, IfPatternLocal), LiftError> {
        if self.locals.declaration_signature(ty, self.store_debug(store, slot).as_ref()).is_some() {
            return Err(self.unsupported("record pattern component requires a generic source type"));
        }
        let local = self.prepare_if_binding(ty, cast, store, slot)?
            .ok_or_else(|| self.unsupported("record pattern cannot declare a fresh component local"))?;
        let mut text = self.local_type_document(ty);
        text.push(' ');
        text.append(self.local_binding_document(slot, &local.local, true));
        Ok((text, local))
    }

    pub(crate) fn record_if_selector(
        &self, slot: u16, pattern: &Type, has_cast: bool,
    ) -> Result<Document, LiftError> {
        let local = self.locals.slots.get(usize::from(slot)).and_then(Option::as_ref)
            .ok_or_else(|| self.invalid_local(slot, "unbound record-pattern selector"))?;
        if local.generic.is_some()
            || !self.known_assignable(&local.ty, pattern)
                && (!has_cast || !self.known_assignable(pattern, &local.ty))
        {
            return Err(self.unsupported("record-pattern selector cannot supply the deconstruction receiver"));
        }
        Ok(self.local_binding_document(slot, local, false))
    }

    pub(crate) fn lift_if_pattern_test(
        &mut self,
        instruction: &Instruction,
        binding: &IfPatternLocal,
    ) -> Result<(), LiftError> {
        if !matches!(self.step(instruction)?, Effect::None) {
            return Err(self.invalid_operand("pattern condition must be an instanceof instruction"));
        }
        let declaration = self.local_binding_document(binding.slot, &binding.local, true);
        let Some(condition) = self.stack.last_mut() else {
            return Err(self.invalid_stack("missing instanceof result"));
        };
        condition.text.push(' ');
        condition.text.append(declaration);
        Ok(())
    }

    pub(crate) fn install_if_pattern_local(&mut self, binding: &IfPatternLocal) {
        let slot = usize::from(binding.slot);
        self.locals.slots[slot] = Some(binding.local.clone());
        if binding.local.ty.slots() == 2 {
            self.locals.slots[slot + 1] = None;
        }
    }

    pub(crate) fn restore_if_pattern_slot(&mut self, baseline: &Self, binding: &IfPatternLocal) {
        let slot = usize::from(binding.slot);
        let slots = slot..slot + usize::from(binding.local.ty.slots());
        self.locals.slots[slots.clone()].clone_from_slice(&baseline.locals.slots[slots]);
    }
}
