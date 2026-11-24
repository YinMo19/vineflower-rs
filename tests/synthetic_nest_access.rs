use vineflower_rs::{Options, decompile_group};

const OUTER: &[u8] = include_bytes!("smoke/java8/TestSyntheticAccess.class");
const ASSIGNER: &[u8] = include_bytes!("smoke/java8/TestSyntheticAccess$Assigner.class");
const INCREMENTER: &[u8] = include_bytes!("smoke/java8/TestSyntheticAccess$Incrementer.class");

#[test]
fn inlines_java8_nest_field_getters_setters_and_updates() {
    let source = decompile_group(OUTER, [ASSIGNER, INCREMENTER], &Options::default())
        .unwrap()
        .text;
    assert!(!source.contains("access$"), "{source}");
    for statement in [
        "TestSyntheticAccess.this.i = newValue;",
        "TestSyntheticAccess.s = newValue;",
        "TestSyntheticAccess.this.i = TestSyntheticAccess.this.i | 1;",
        "TestSyntheticAccess.this.i++;",
        "--TestSyntheticAccess.this.i;",
        "++TestSyntheticAccess.s;",
        "TestSyntheticAccess.s--;",
    ] {
        assert!(source.lines().any(|line| line.trim() == statement), "{statement}\n{source}");
    }
}
