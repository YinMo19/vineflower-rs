use vineflower_rs::{ClassGroup, Options, decompile};

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

#[test]
fn opt_in_recovers_void_fallthrough_without_mapping_a_synthetic_return() {
    const LEAKY: &[u8] = include_bytes!("smoke/jasm/TestLeakyMethod.class");
    const FIELD: &[u8] = include_bytes!("smoke/jasm/TestFieldSingleAccess.class");
    let mut options = Options::default();
    for bytes in [LEAKY, FIELD] {
        let error = decompile(bytes, &options).unwrap_err();
        assert!(error.to_string().contains("falls through the end of the method"), "{error}");
    }

    options.set("ignore-invalid-bytecode", "1").unwrap();
    options.include_line_mappings = true;
    let leaky = decompile(LEAKY, &options).unwrap();
    let methods = leaky.map.unwrap().methods;
    assert!(methods.iter().filter(|method| method.name == "testIllegal")
        .all(|method| method.offsets.keys().all(|offset| *offset < 2)));
    assert_eq!(methods.iter().find(|m| m.name == "test").unwrap().offsets.keys()
        .copied().collect::<Vec<_>>(), [0]);

    let field = decompile(FIELD, &options).unwrap();
    let methods = field.map.unwrap().methods;
    let offsets = &methods.iter().find(|m| m.name == "test2").unwrap().offsets;
    assert!(offsets.contains_key(&10));
    assert!(!offsets.contains_key(&13));
}
