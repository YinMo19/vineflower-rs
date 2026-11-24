use vineflower_rs::{
    classfile::{ClassFile, Member},
    kotlin::{KotlinError, decompile_class},
};

// Exact upstream plugins/kotlin/testData/src/kt/pkg inputs.
const INFIX: &[u8] = include_bytes!("smoke/kotlin/TestInfixFun.class");
const EXTENSION: &[u8] = include_bytes!("smoke/kotlin/TestExtensionFun.class");

fn source(bytes: &[u8]) -> String {
    decompile_class(&ClassFile::parse(bytes).unwrap()).unwrap().unwrap()
}

#[test]
fn repeat_is_a_char_sequence_extension() {
    let source = source(EXTENSION);
    for expected in [
        "import kotlin.text.repeat",
        "fun CharSequence.repeat2(n: Int): String",
        "this.repeat(n)",
        "kotlin.io.println((\"Bye \" as kotlin.CharSequence).repeat2(2))",
    ] {
        assert!(source.contains(expected), "missing {expected:?}:\n{source}");
    }
    assert!(!source.contains("StringsKt"));
}

#[test]
fn local_infix_functions_bind_in_their_own_enclosing_declaration() {
    let source = source(INFIX);
    for expected in [
        "\n      infix fun Int.times(str: String): String = str.repeat(this)",
        "kotlin.io.println(2 times \"Bye \")",
        "\n   public infix fun Int.mult(str: String): String",
        "\n      infix fun Int.mult(str: String): String = str.repeat(this + 1)",
    ] {
        assert!(source.contains(expected), "missing {expected:?}:\n{source}");
    }
    let first = source.split_once("fun test()").unwrap().1.split_once("public infix fun").unwrap().0;
    assert!(first.contains("infix fun Int.times"));
    let (_, outer) = source.split_once("fun testOuter()").unwrap();
    let (outer, duplicate) = outer.split_once("fun testDuplicate()").unwrap();
    assert!(!outer.contains("fun Int.mult"));
    assert!(outer.contains("kotlin.io.println(2 mult \"Bye \")"));
    assert!(duplicate.contains("fun Int.mult"));
    assert!(duplicate.contains("kotlin.io.println(2 mult \"Bye \")"));
    assert!(!source.contains('$'));
}

fn method<'a, 'data>(class: &'a ClassFile<'data>, name: &str) -> &'a Member<'data> {
    class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == name).unwrap()
}

#[test]
fn private_static_helper_cannot_be_rebound_to_a_different_enclosing_function() {
    let class = ClassFile::parse(INFIX).unwrap();
    let caller = method(&class, "test").code(&class.pool).unwrap().unwrap();
    let duplicate = method(&class, "testDuplicate").code(&class.pool).unwrap().unwrap();
    assert_eq!(caller.bytes[3], 0xb8);
    assert_eq!(duplicate.bytes[3], 0xb8);
    // Change only the symbolic target. The descriptors are identical, but the
    // second helper belongs to the other function and repeats one extra time.
    let start = caller.bytes.as_ptr() as usize - INFIX.as_ptr() as usize;
    let mut changed = INFIX.to_vec();
    changed[start + 4..start + 6].copy_from_slice(&duplicate.bytes[4..6]);
    assert!(matches!(
        decompile_class(&ClassFile::parse(&changed).unwrap()),
        Err(KotlinError::Unsupported { declaration, .. }) if declaration == "test"
    ));
}

#[test]
fn repeat_does_not_treat_a_null_checkcast_as_a_non_null_source_receiver() {
    let class = ClassFile::parse(INFIX).unwrap();
    let mult = method(&class, "mult").code(&class.pool).unwrap().unwrap();
    assert_eq!(&mult.bytes[6..8], &[0x2c, 0xc0]);
    let start = mult.bytes.as_ptr() as usize - INFIX.as_ptr() as usize;
    let mut changed = INFIX.to_vec();
    // Null passes checkcast in JVM bytecode; the stdlib's own guard throws.
    changed[start + 6] = 0x01;
    assert!(matches!(
        decompile_class(&ClassFile::parse(&changed).unwrap()),
        Err(KotlinError::Unsupported { declaration, .. }) if declaration == "mult"
    ));
}
