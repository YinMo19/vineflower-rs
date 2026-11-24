use vineflower_rs::{
    classfile::ClassFile,
    kotlin::{KotlinError, decompile_class},
};

// Original plugin fixture, including nullable Boolean and primitive boxing routes.
const CLASS: &[u8] = include_bytes!("smoke/kotlin/TestSafeCasts.class");

#[test]
fn nullable_type_tests_keep_null_in_the_success_arm() {
    let source = decompile_class(&ClassFile::parse(CLASS).unwrap()).unwrap().unwrap();
    let (before, nullable) = source.split_once("fun testBeforeNullableToNullable").unwrap();
    assert!(before.contains("(obj as? kotlin.String) == \"1\""), "{source}");
    assert!(nullable.contains("if (obj === null || obj is kotlin.Int)"), "{source}");
    assert!(nullable.contains("(obj as? kotlin.Int) == 1 else null"), "{source}");
}

#[test]
fn an_inverted_integer_branch_is_not_nullable_equality() {
    let class = ClassFile::parse(CLASS).unwrap();
    let test = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test").unwrap();
    let code = test.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - CLASS.as_ptr() as usize;
    assert_eq!(code.bytes[37], 0xa0); // if_icmpne; false for null or a different Int
    let mut modified = CLASS.to_vec();
    modified[start + 37] = 0x9f; // if_icmpeq; false for null or the same Int
    assert!(matches!(
        decompile_class(&ClassFile::parse(&modified).unwrap()),
        Err(KotlinError::Unsupported { declaration, .. }) if declaration == "test"
    ));
}
