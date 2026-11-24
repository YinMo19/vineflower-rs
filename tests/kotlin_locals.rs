use vineflower_rs::{
    classfile::ClassFile,
    kotlin::{KotlinError, decompile_class},
};

// Original Kotlin plugin fixture compiled with its upstream toolchain.
const VARS: &[u8] = include_bytes!("smoke/kotlin/TestVars.class");

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
