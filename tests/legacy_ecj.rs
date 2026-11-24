use vineflower_rs::{ClassGroup, Options};

const OUTER: &[u8] = include_bytes!("smoke/jasm/TestOldECJInner.class");
const INNER: &[u8] = include_bytes!("smoke/jasm/TestOldECJInner$Inner.class");
const OWNER: &str = "pkg/TestOldECJInner";

#[test]
fn malformed_ecj_constructor_requires_the_opt_in_and_the_forwarding_member() {
    let group = ClassGroup::new([OUTER, INNER]).unwrap();
    let mut options = Options::default();
    let strict = group.decompile(OWNER, &options).unwrap_err();
    assert!(strict.to_string().contains("operand stack exceeds max_stack"));

    options.set("ignore-invalid-bytecode", "1").unwrap();
    let source = group.decompile(OWNER, &options).unwrap();
    assert!(source.text.contains("return get().new Inner();"), "{}", source.text);
    assert!(!source.text.contains("new Inner(get(), null)"));

    let without_inner = ClassGroup::new([OUTER]).unwrap();
    assert!(without_inner.decompile(OWNER, &options).is_err());
}
