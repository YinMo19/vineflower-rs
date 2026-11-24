use vineflower_rs::{Options, decompile_group};

const GENERIC_OUTER: &[u8] = include_bytes!("smoke/java11/TestNestedGenerics2.class");
const GENERIC_ANONYMOUS: &[u8] = include_bytes!("smoke/java11/TestNestedGenerics2$1.class");

#[test]
fn java11_anonymous_local_preserves_its_type_and_enclosing_type_variables() {
    let source = decompile_group(GENERIC_OUTER, [GENERIC_ANONYMOUS], &Options::default())
        .unwrap()
        .text;
    assert!(source.contains("public static <T, R> R test(T t)"), "{source}");
    assert!(source.contains("var instance = new Object() {"), "{source}");
    assert!(source.contains("R run(T t)"), "{source}");
    assert!(
        source.contains("return instance.run(t);") || source.contains("return (R)instance.run(t);"),
        "{source}"
    );
    assert!(!source.contains("TestNestedGenerics2$1"), "{source}");
}

#[test]
fn java8_named_local_keeps_its_explicit_type() {
    let outer = include_bytes!("smoke/java8/TestAnonymousObject.class").as_slice();
    let anonymous = include_bytes!("smoke/java8/TestAnonymousObject$1.class").as_slice();
    let source = decompile_group(outer, [anonymous], &Options::default()).unwrap().text;
    assert!(source.contains("Object o = new Object() {"), "{source}");
    assert!(source.contains("System.out.println(\"Hi\");"), "{source}");
    assert!(!source.contains("var o"), "{source}");
}

#[test]
fn java8_class_version_rejects_an_anonymous_only_local_type() {
    let downgrade = |bytes: &[u8]| {
        let mut bytes = bytes.to_vec();
        bytes[6..8].copy_from_slice(&52_u16.to_be_bytes());
        bytes
    };
    let outer = downgrade(GENERIC_OUTER);
    let anonymous = downgrade(GENERIC_ANONYMOUS);
    let error = decompile_group(&outer, [anonymous.as_slice()], &Options::default()).unwrap_err();
    assert!(error.to_string().contains("anonymous local type inference requires Java 10"), "{error}");
}
