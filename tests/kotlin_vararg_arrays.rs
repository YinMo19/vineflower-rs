use std::ops::Range;

use vineflower_rs::{
    classfile::ClassFile,
    kotlin::{KotlinError, decompile_class},
};

// Exact upstream plugins/kotlin/testData/src/kt/pkg/TestFunVarargs.kt input.
const CLASS: &[u8] = include_bytes!("smoke/kotlin/TestFunVarargs.class");

#[test]
fn recovers_array_iteration_spread_packing_and_nested_projections() {
    let class = ClassFile::parse(CLASS).unwrap();
    let source = decompile_class(&class).unwrap().unwrap();
    for expected in [
        "fun printAll(vararg messages: String)",
        "fun printAllArray(messages: Array<out String>)",
        "this.printAll(*entries)",
        "this.printAllArray(entries)",
        "this.log(\"a\", \"b\", \"c\")",
        "fun nestedArrays(e0: Array<String>, e1: Array<in String>, e2: Array<Array<Array<String>>>)",
    ] {
        assert!(source.contains(expected), "missing {expected:?}:\n{source}");
    }
    assert_eq!(source.matches("for (m in messages)").count(), 2, "{source}");
}

fn code_range(name: &str) -> Range<usize> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == name).unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - CLASS.as_ptr() as usize;
    start..start + code.bytes.len()
}

fn rejects(changed: &[u8], method: &str) {
    let result = decompile_class(&ClassFile::parse(changed).unwrap());
    assert!(matches!(&result, Err(KotlinError::Unsupported { declaration, .. }) if declaration == method), "{result:?}");
}

#[test]
fn forwarding_the_original_reference_is_not_a_defensive_spread() {
    let mut changed = CLASS.to_vec();
    let log = &mut changed[code_range("log")];
    assert_eq!(&log[6..11], &[0x2a, 0x2b, 0x2b, 0xbe, 0xb8]);
    assert_eq!((log[13], log[16]), (0xc0, 0xb6));
    // Keep the original receiver and first array load, but delete the copy.
    // The first call now observes changes to the caller's array mid-iteration.
    log[8..16].fill(0);
    rejects(&changed, "log");
}

#[test]
fn a_truncating_copy_is_not_a_full_spread() {
    let mut changed = CLASS.to_vec();
    let log = &mut changed[code_range("log")];
    assert_eq!(&log[8..11], &[0x2b, 0xbe, 0xb8]);
    // Use a length of zero, retaining the exact copyOf method and checkcast.
    log[8..10].copy_from_slice(&[0x03, 0x00]);
    rejects(&changed, "log");
}

#[test]
fn overwriting_one_array_element_is_not_positional_packing() {
    let mut changed = CLASS.to_vec();
    let test = &mut changed[code_range("test")];
    assert_eq!(&test[10..14], &[0x53, 0x2b, 0x04, 0x12]);
    // Write "b" over "a", leaving the second array entry null.
    test[12] = 0x03;
    rejects(&changed, "test");
}
