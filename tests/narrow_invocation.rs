use vineflower_rs::{Options, classfile::ClassFile, decompile};

const TERNARY: &[u8] = include_bytes!("smoke/java8/TestReturnTernaryChar.class");
const REUSED_SLOT: &[u8] = include_bytes!("smoke/java8nodebug/TestVarIndex.class");
const INT_BOOL: &[u8] = include_bytes!("smoke/java8nodebug/TestIntBoolMergeNoDebug.class");

#[test]
fn source_retains_the_subword_invocation_types() {
    let options = Options::default();
    let ternary = decompile(TERNARY, &options).unwrap().text;
    assert!(ternary.contains("sink1((char)"), "{ternary}");
    assert!(ternary.contains("sink2((byte)"), "{ternary}");

    let reused = decompile(REUSED_SLOT, &options).unwrap().text;
    assert_eq!(reused.matches("consume((short)").count(), 4, "{reused}");
    assert_eq!(reused.matches("consume((byte)").count(), 4, "{reused}");

    let boolean = decompile(INT_BOOL, &options).unwrap().text;
    assert!(boolean.contains("System.out.println(var1);"), "{boolean}");
    assert!(boolean.contains("!= 0);"), "{boolean}");
}

#[test]
fn a_ternary_does_not_narrow_if_one_arm_could_change_value() {
    let class = ClassFile::parse(TERNARY).unwrap();
    let method = class.methods.iter().find(|method| {
        class.pool.utf8(method.name_index).unwrap() == "get3"
    }).unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - TERNARY.as_ptr() as usize;
    assert_eq!(&code.bytes[10..12], &[0x10, b'A']);
    let mut bad = TERNARY.to_vec();
    // The alternate arm now passes JVM int -1, not the char 65535.
    bad[start + 11] = 0xff;
    let error = decompile(&bad, &Options::default()).unwrap_err();
    assert!(error.to_string().contains("JVM int passed as a narrow argument"), "{error}");
}
