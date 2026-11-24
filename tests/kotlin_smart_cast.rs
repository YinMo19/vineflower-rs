use vineflower_rs::{
    classfile::ClassFile,
    kotlin::{KotlinError, decompile_class},
};

const CLASS: &[u8] = include_bytes!("smoke/kotlin/TestAnyType.class");

#[test]
fn only_the_string_arm_uses_length_and_the_other_arm_keeps_its_effects() {
    let source = decompile_class(&ClassFile::parse(CLASS).unwrap()).unwrap().unwrap();
    assert!(source.contains("if (param is kotlin.String) param.length"), "{source}");
    assert!(source.contains("else kotlin.run { System.out.println(param); 0 }"), "{source}");
}

#[test]
fn the_opposite_edge_does_not_prove_a_smart_cast() {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - CLASS.as_ptr() as usize;
    assert_eq!(code.bytes[10], 0x99);
    let mut modified = CLASS.to_vec();
    modified[start + 10] = 0x9a; // A non-String now reaches the failing checkcast.
    assert!(matches!(
        decompile_class(&ClassFile::parse(&modified).unwrap()),
        Err(KotlinError::Unsupported { declaration, .. }) if declaration == "test"
    ));
}
