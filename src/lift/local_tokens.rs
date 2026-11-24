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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Options,
        bytecode::decode,
        classfile::{ClassFile, Code, Member},
        descriptor::MethodDescriptor,
        lift::Effect,
    };

    const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x34\0\x08\
        \x01\0\x06Tokens\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
        \x01\0\x04test\x01\0\x05(JI)I\x01\0\x05inner\
        \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";
    const BYTES: &[u8] = &[0x1c, 0x3e, 0x84, 0x03, 0x01, 0x01, 0x4d, 0x1d, 0xac];

    fn method(name_index: u16) -> Member<'static> {
        Member {
            access_flags: 0x0008,
            name_index,
            descriptor_index: 6,
            attributes: vec![],
        }
    }

    fn code() -> Code<'static> {
        Code {
            max_stack: 2,
            max_locals: 4,
            bytes: BYTES,
            exceptions: vec![],
            attributes: vec![],
        }
    }

    fn assert_symbols(document: &Document, text: &str, expected: &[(&str, &str, bool, bool, u32)]) {
        let mut actual = String::new();
        let mut seen = Vec::new();
        document.render_with_tokens_at(
            &mut actual,
            120,
            "   ",
            false,
            0,
            |_, _| {},
            |token, range| {
                if let TokenKind::Variable {
                    name,
                    owner,
                    method,
                    descriptor,
                    parameter,
                    index,
                } = &token.kind
                {
                    assert_eq!(owner, "Tokens");
                    assert_eq!(descriptor, "(JI)I");
                    assert_eq!(range.start.line, 0);
                    assert_eq!(range.end.line, 0);
                    seen.push((
                        name.clone(),
                        method.clone(),
                        token.declaration,
                        *parameter,
                        *index,
                        range.start.column..range.end.column,
                    ));
                }
            },
        );
        assert_eq!(actual, text);
        assert_eq!(seen.len(), expected.len());
        for ((name, method, declaration, parameter, index, span), expected) in
            seen.into_iter().zip(expected)
        {
            assert_eq!(
                (&name[..], &method[..], declaration, parameter, index),
                *expected
            );
            assert_eq!(&actual[span], name);
        }
    }

    #[test]
    fn tracks_wide_parameter_slots_and_rebound_locals() {
        let class = ClassFile::parse(CLASS).unwrap();
        let method = method(5);
        let code = code();
        let descriptor = MethodDescriptor::parse("(JI)I").unwrap();
        let map = |name: &str| name.rsplit('/').next().unwrap().into();
        let options = Options {
            dump_text_tokens: true,
            ..Options::default()
        };
        let mut machine =
            Machine::new(&class, &method, &code, &descriptor, &options, &map).unwrap();
        assert!(machine.local_document(1, true).is_none());
        assert_symbols(
            &machine.local_document(0, true).unwrap(),
            "var0",
            &[("var0", "test", true, true, 0)],
        );
        let instructions = decode(BYTES).unwrap();
        machine.step(&instructions[0]).unwrap();
        let Effect::Statement(declaration) = machine.step(&instructions[1]).unwrap() else {
            panic!("expected local declaration")
        };
        assert_symbols(
            &declaration,
            "int var3 = var2;",
            &[
                ("var3", "test", true, false, 3),
                ("var2", "test", false, true, 2),
            ],
        );
        let Effect::Statement(increment) = machine.step(&instructions[2]).unwrap() else {
            panic!("expected increment")
        };
        assert_symbols(&increment, "var3++;", &[("var3", "test", false, false, 3)]);
        machine.step(&instructions[3]).unwrap();
        let Effect::Statement(rebound) = machine.step(&instructions[4]).unwrap() else {
            panic!("expected rebound local declaration")
        };
        assert_symbols(
            &rebound,
            "Object var2_1 = null;",
            &[("var2_1", "test", true, true, 4)],
        );
        machine.step(&instructions[5]).unwrap();
        let Effect::Return(Some(value)) = machine.step(&instructions[6]).unwrap() else {
            panic!("expected value return")
        };
        assert_symbols(&value, "var3", &[("var3", "test", false, false, 3)]);
    }

    #[test]
    fn captures_refer_to_lexical_symbols_not_implementation_parameters() {
        let class = ClassFile::parse(CLASS).unwrap();
        let (outer_method, inner_method) = (method(5), method(7));
        let code = code();
        let descriptor = MethodDescriptor::parse("(JI)I").unwrap();
        let options = Options {
            dump_text_tokens: true,
            ..Options::default()
        };
        let outer = Machine::new(
            &class,
            &outer_method,
            &code,
            &descriptor,
            &options,
            &str::to_owned,
        )
        .unwrap();
        let mut inner = Machine::new(
            &class,
            &inner_method,
            &code,
            &descriptor,
            &options,
            &str::to_owned,
        )
        .unwrap();
        inner.inherit_lambda_capture_token(2, &outer, 2);
        inner.omit_lambda_capture_token(0);
        assert_symbols(
            &inner.local_document(2, false).unwrap(),
            "var2",
            &[("var2", "test", false, true, 2)],
        );
        assert_symbols(&inner.local_document(0, false).unwrap(), "var0", &[]);
    }
}
