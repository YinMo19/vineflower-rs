// Based on Vineflower's corresponding-synthetic naming fixtures (Apache-2.0).

use crate::ClassGroup;

use super::*;

#[test]
fn disabled_lambda_marks_do_not_modify_source_or_symbols() {
    let mut text = Document::from("(Runnable)");
    let options = Options { dump_text_tokens: true, ..Options::default() };
    append_lambda_mark(&mut text, &options, "pkg/Example", "lambda$run$0", "()V");
    assert_eq!(text.as_str(), "(Runnable)");
    assert_eq!(text.flat_tokens().count(), 0);
}

#[test]
fn lambda_mark_declares_the_exact_implementation_method_before_expression() {
    let mut text = Document::from("(Runnable)");
    let options = Options {
        mark_corresponding_synthetics: true,
        dump_text_tokens: true,
        ..Options::default()
    };
    append_lambda_mark(&mut text, &options, "pkg/Example", "lambda$run$0", "(J)V");
    text.push_str("() -> run()");
    assert_eq!(text.as_str(), "(Runnable)/* lambda$run$0 */ () -> run()");
    let tokens: Vec<_> = text.flat_tokens().collect();
    assert_eq!(tokens.len(), 1);
    let (span, token) = &tokens[0];
    assert_eq!(&text.as_str()[span.clone()], "lambda$run$0");
    assert!(token.declaration);
    assert!(matches!(
        &token.kind,
        TokenKind::Method { owner, name, descriptor }
        if owner == "pkg/Example" && name == "lambda$run$0" && descriptor == "(J)V"
    ));
}

#[test]
fn anonymous_enum_class_marks_bind_the_implementation_not_the_enum_type() {
    let enum_class = include_bytes!("../../../tests/smoke/java17/TestImplicitlySealedEnum.class");
    let subclass = include_bytes!("../../../tests/smoke/java17/TestImplicitlySealedEnum$1.class");
    let group = ClassGroup::new([enum_class.as_slice(), subclass.as_slice()]).unwrap();
    let options = Options {
        mark_corresponding_synthetics: true,
        dump_text_tokens: true,
        ..Options::default()
    };
    let source = group.decompile("pkg/TestImplicitlySealedEnum", &options).unwrap().text;
    assert!(source.contains("B /* TestImplicitlySealedEnum$1 */ {"), "{source}");
    assert!(source.contains("class [declaration] pkg/TestImplicitlySealedEnum$1\n"), "{source}");
    assert!(!source.contains("A /* ") && !source.contains("enum TestImplicitlySealedEnum /* "));
}
