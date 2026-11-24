// Based on Vineflower VarExprent and VarVersionsProcessor (Apache-2.0).

use std::{collections::HashMap, rc::Rc};

use crate::{
    descriptor::Type,
    emit::symbols::append_class,
    source_text::{
        Document,
        tokens::{Token, TokenKind},
    },
};

use super::{Local, Locals, Machine};

type CaptureTokens = HashMap<u16, Option<Rc<Token>>>;

#[derive(Clone)]
pub(super) struct LocalTokens<'a> {
    descriptor: &'a str,
    parameter_slots: u16,
    captures: Option<Rc<CaptureTokens>>,
}

impl<'a> LocalTokens<'a> {
    pub(super) fn new(descriptor: &'a str, parameter_slots: u16) -> Self {
        Self {
            descriptor,
            parameter_slots,
            captures: None,
        }
    }
}

#[derive(Clone)]
pub(super) struct LocalTokenIndices {
    bound_slots: Vec<bool>,
    next: u32,
}

impl LocalTokenIndices {
    pub(super) fn new(slots: &[Option<Local>]) -> Self {
        // A receiver or parameter owns version one of its exact JVM slot;
        // the second slot of a long/double is not itself a variable binding.
        Self {
            bound_slots: slots.iter().map(Option::is_some).collect(),
            next: slots.len() as u32,
        }
    }
}

impl Locals<'_> {
    pub(super) fn new_local_token_index(&self, slot: u16) -> Option<u32> {
        let mut names = self.names.borrow_mut();
        let indices = names.token_indices.as_mut()?;
        let bound = &mut indices.bound_slots[usize::from(slot)];
        if !std::mem::replace(bound, true) {
            return None;
        }
        // Vineflower reserves JVM slots for the first SSA version and assigns
        // later source bindings indices beyond max_locals. The Rust lifter
        // assigns these in declaration order, not full JVM SSA analysis order.
        let index = indices.next;
        indices.next += 1;
        Some(index)
    }
}

impl Machine<'_, '_> {
    /// A variable name built from a bound slot, not from its source spelling.
    pub(crate) fn local_document(&self, slot: u16, declaration: bool) -> Option<Document> {
        let local = self.locals.slots.get(usize::from(slot))?.as_ref()?;
        Some(self.local_binding_document(slot, local, declaration))
    }

    pub(super) fn local_binding_document(
        &self,
        slot: u16,
        local: &Local,
        declaration: bool,
    ) -> Document {
        let mut text = Document::new();
        self.append_local_binding(&mut text, slot, local, declaration);
        text
    }

    pub(super) fn append_local_binding(
        &self,
        text: &mut Document,
        slot: u16,
        local: &Local,
        declaration: bool,
    ) {
        if let Some(token) = self.local_binding_token(slot, local, declaration) {
            text.token(&local.name, token);
        } else {
            text.push_str(&local.name);
        }
    }

    pub(super) fn local_binding_token(
        &self,
        slot: u16,
        local: &Local,
        declaration: bool,
    ) -> Option<Rc<Token>> {
        let tokens = self.locals.tokens.as_ref()?;
        if local.receiver {
            return None;
        }
        if !declaration
            && local.token_index.is_none()
            && let Some(capture) = tokens
                .captures
                .as_ref()
                .and_then(|captures| captures.get(&slot))
        {
            return capture.clone();
        }
        let kind = TokenKind::Variable {
            owner: self.owner.into(),
            method: self.method_name.into(),
            descriptor: tokens.descriptor.into(),
            index: local.token_index.unwrap_or(u32::from(slot)),
            name: local.name.clone(),
            parameter: slot < tokens.parameter_slots,
        };
        Some(Rc::new(Token { declaration, kind }))
    }

    /// Captured implementation arguments refer to the original lexical
    /// variable, including when the enclosing method is itself a lambda.
    pub(in crate::lift) fn inherit_lambda_capture_token(
        &mut self,
        child_slot: u16,
        outer: &Machine<'_, '_>,
        outer_slot: u16,
    ) {
        if self.locals.tokens.is_none() {
            return;
        }
        let token = outer
            .locals
            .slots
            .get(usize::from(outer_slot))
            .and_then(Option::as_ref)
            .and_then(|local| outer.local_binding_token(outer_slot, local, false));
        self.set_lambda_capture_token(child_slot, token);
    }

    /// A spill is not an original implementation-method parameter.
    pub(in crate::lift) fn omit_lambda_capture_token(&mut self, child_slot: u16) {
        self.set_lambda_capture_token(child_slot, None);
    }

    fn set_lambda_capture_token(&mut self, child_slot: u16, token: Option<Rc<Token>>) {
        if let Some(tokens) = self.locals.tokens.as_mut() {
            let captures = tokens.captures.get_or_insert_with(Rc::default);
            Rc::make_mut(captures).insert(child_slot, token);
        }
    }

    pub(super) fn local_type_document(&self, ty: &Type) -> Document {
        if self.locals.tokens.is_none() {
            return self.render_type(ty).into();
        }
        let mut leaf = ty;
        let mut dimensions = 0;
        while let Type::Array(element) = leaf {
            leaf = element;
            dimensions += 1;
        }
        let Type::Object(binary) = leaf else {
            return self.render_type(ty).into();
        };
        let mut doc = Document::new();
        append_class(&mut doc, &(self.class_name)(binary), binary, true);
        for _ in 0..dimensions {
            doc.push_str("[]");
        }
        doc
    }
}
