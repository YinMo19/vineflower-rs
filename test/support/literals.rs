// SPDX-License-Identifier: Apache-2.0

use super::*;
use vineflower_rs::{decompiler::exps::literal, util::token::TokenKind};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn constant_pool_literals_match_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let expected =
        upstream_reference::Corpus::discover().run("LiteralReference", &[], scratch.path());
    let mut rows = Vec::new();
    for as_is in [false, true] {
        for ascii in [false, true] {
            let mut options = Options::default();
            options.keep_literals = as_is;
            options.ascii_strings = ascii;
            let options = Arc::new(options);
            let mut context = StructContext::new(options.clone(), None);
            context
                .add_file(&scratch.path().join("Literals.class"), true)
                .unwrap();
            let class = context.get_class("Literals").unwrap();
            let mut cx = Cx::new(Arc::new(context));
            cx.imports = ImportCollector::for_class(&cx.struct_context, &class);
            cx.current_class_node = Some(class.qualified_name.clone());
            for field in &class.fields {
                let Some(attr) = &field.attributes.constant_value else {
                    continue;
                };
                let ty = VarType::from_signature(&field.descriptor);
                let value = class.pool.get_primitive_constant(attr.index).unwrap().value;
                let precedence = literal::precedence(&mut cx, &ty, &value, None);
                let text = literal::render(&mut cx, &ty, &value, None, false).unwrap();
                let tokens = text
                    .get_tokens()
                    .into_iter()
                    .map(|t| {
                        let kind = match t.kind {
                            TokenKind::Class { .. } => "ClassTextToken",
                            TokenKind::Field { .. } => "FieldTextToken",
                            _ => panic!("Unexpected literal token"),
                        };
                        format!("{}+{}/{kind}", t.start, t.length)
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                rows.push(format!(
                    "{}{} {} {precedence} {} {tokens}",
                    u8::from(as_is),
                    u8::from(ascii),
                    field.name,
                    text.convert_to_string_and_allow_data_discard()
                ));
            }
        }
    }
    for (a, b) in rows.iter().zip(expected.lines()) {
        assert_eq!(a, b);
    }
    assert_eq!(rows.len(), expected.lines().count());
}
