use vineflower_rs::{
    classfile::ClassFile,
    kotlin::{KotlinError, decompile_class},
};

// Original Kotlin plugin fixture compiled with its upstream toolchain.
const VARS: &[u8] = include_bytes!("smoke/kotlin/TestVars.class");
const SHADOW: &[u8] = include_bytes!("smoke/kotlin/TestShadowParam.class");

#[test]
fn both_stack_and_slot_joins_initialize_the_declared_local() {
    let source = decompile_class(&ClassFile::parse(VARS).unwrap()).unwrap().unwrap();
    for method in ["testPhi", "testIfExpr"] {
        let (_, body) = source.split_once(&format!("fun {method}(")).unwrap();
        let (body, _) = body.split_once("\n   }").unwrap();
        assert!(body.contains("val d = if (bl) 1 else 2"), "{method}: {body}");
        assert!(body.contains("println(d)"), "{method}: {body}");
    }
}

#[test]
fn an_arm_that_writes_a_different_slot_does_not_overwrite_the_seed() {
    let class = ClassFile::parse(VARS).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "testPhi").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - VARS.as_ptr() as usize;
    assert_eq!(code.bytes[12], 0x3d); // istore_2 (d)
    let mut modified = VARS.to_vec();
    modified[start + 12] = 0x3c; // istore_1 (bl); on this edge d still equals zero.
    assert!(matches!(
        decompile_class(&ClassFile::parse(&modified).unwrap()),
        Err(KotlinError::Unsupported { declaration, .. }) if declaration == "testPhi"
    ));
}

#[test]
fn a_shadowing_mutable_local_remains_visible_to_the_predicate_and_its_arm() {
    let source = decompile_class(&ClassFile::parse(SHADOW).unwrap()).unwrap().unwrap();
    assert!(source.contains("var x = x"), "{source}");
    assert!(source.contains("x--"), "{source}");
    assert!(source.contains("x < 0"), "{source}");
    assert_eq!(source.matches("println(x)").count(), 2, "{source}");
}

#[test]
fn continued_parameter_reads_are_distinct_from_the_shadowing_local() {
    let class = ClassFile::parse(SHADOW).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - SHADOW.as_ptr() as usize;
    assert_eq!(code.bytes[19], 0x1c); // print the incremented slot
    let mut modified = SHADOW.to_vec();
    modified[start + 19] = 0x1b; // print the original parameter instead
    let source = decompile_class(&ClassFile::parse(&modified).unwrap()).unwrap().unwrap();
    assert!(source.contains("var x_1 = x"), "{source}");
    assert!(source.contains("x_1--"), "{source}");
    assert!(source.contains("x_1 < 0"), "{source}");
    assert_eq!(source.matches("println(x_1)").count(), 1, "{source}");
    assert_eq!(source.matches("println(x)").count(), 1, "{source}");
}
