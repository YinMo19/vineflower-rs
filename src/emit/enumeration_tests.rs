use crate::{ClassGroup, Options};

use super::*;

const TEST_ENUM: [&[u8]; 5] = [
    include_bytes!("../../tests/smoke/java8/TestEnum.class"),
    include_bytes!("../../tests/smoke/java8/TestEnum$1.class"),
    include_bytes!("../../tests/smoke/java8/TestEnum$2.class"),
    include_bytes!("../../tests/smoke/java8/TestEnum$3.class"),
    include_bytes!("../../tests/smoke/java8/TestEnum$Type.class"),
];
const SEALED: [&[u8]; 2] = [
    include_bytes!("../../tests/smoke/java17/TestImplicitlySealedEnum.class"),
    include_bytes!("../../tests/smoke/java17/TestImplicitlySealedEnum$1.class"),
];
const INITIALIZERS: [&[u8]; 3] = [
    include_bytes!("../../tests/smoke/java17/TestDoubleBraceInitializersJ17$TestEnum1.class"),
    include_bytes!("../../tests/smoke/java17/TestDoubleBraceInitializersJ17$TestEnum1$1.class"),
    include_bytes!("../../tests/smoke/java17/TestDoubleBraceInitializersJ17$TestEnum1$2.class"),
];

#[test]
fn javac_8_subclasses_keep_constant_arguments_overrides_and_constructor_delegation() {
    let group = ClassGroup::new(TEST_ENUM).unwrap();
    let options = Options {
        remove_synthetic: false,
        ..Options::default()
    };
    let source = group.decompile("pkg/TestEnum", &options).unwrap().text;
    assert!(
        source.contains("E1,") && source.contains("E2 {"),
        "{source}"
    );
    assert!(
        source.contains("E3(\"-\", ") && source.contains(".ODD),"),
        "{source}"
    );
    assert!(
        source.contains("E4(\"+\", ") && source.contains(".EVEN) {"),
        "{source}"
    );
    assert_eq!(source.matches("void m()").count(), 3, "{source}");
    assert!(
        source.contains("this(\"?\",") && source.contains("null"),
        "{source}"
    );
    assert!(
        source.contains("switch (this)") && source.contains("case E2:"),
        "{source}"
    );
    assert!(
        !source.contains("$VALUES")
            && !source.contains("$SwitchMap$")
            && !source.contains("TestEnum$1"),
        "{source}"
    );
}

#[test]
fn implicitly_sealed_enum_reconstructs_its_anonymous_body_and_no_permits_clause() {
    let group = ClassGroup::new(SEALED).unwrap();
    let source = group
        .decompile("pkg/TestImplicitlySealedEnum", &Options::default())
        .unwrap()
        .text;
    assert!(source.contains("A,") && source.contains("B {"), "{source}");
    assert!(
        source.contains("return 2;") && source.contains("return 1;"),
        "{source}"
    );
    assert!(
        !source.contains(" permits ") && !source.contains("$values"),
        "{source}"
    );
}

#[test]
fn subclass_initializers_keep_every_effect_in_their_own_constant() {
    let group = ClassGroup::new(INITIALIZERS).unwrap();
    let source = group
        .decompile(
            "pkg/TestDoubleBraceInitializersJ17$TestEnum1",
            &Options::default(),
        )
        .unwrap()
        .text;
    let a = source.find("A {").unwrap();
    let b = source.find("B {").unwrap();
    let first = &source[a..b];
    let second = &source[b..];
    assert!(
        first.find("println(\"A\")").unwrap() < first.find("field = 1;").unwrap(),
        "{source}"
    );
    assert!(
        second.find("println(\"B\")").unwrap() < second.find("field = 2;").unwrap(),
        "{source}"
    );
    assert!(
        !first.contains("field = 2") && !second.contains("field = 1"),
        "{source}"
    );
}

#[test]
fn missing_subclass_is_not_replaced_with_an_empty_constant_body() {
    let group = ClassGroup::new([SEALED[0]]).unwrap();
    let error = group
        .decompile("pkg/TestImplicitlySealedEnum", &Options::default())
        .unwrap_err();
    assert!(
        matches!(error, DecompileError::Unsupported { feature } if feature.contains("enum constant subclass"))
    );
}

#[test]
fn malformed_values_array_is_not_silently_replaced() {
    let mut changed = TEST_ENUM[0].to_vec();
    let original = ClassFile::parse(TEST_ENUM[0]).unwrap();
    let clinit = original
        .methods
        .iter()
        .find(|method| original.pool.utf8(method.name_index).unwrap() == "<clinit>")
        .unwrap();
    let code = clinit.code(&original.pool).unwrap().unwrap();
    let ops = decode(code.bytes).unwrap();
    let length = ops.windows(2).find(|pair| pair[1].opcode == 0xbd).unwrap()[0].offset as usize;
    let offset = code.bytes.as_ptr() as usize - TEST_ENUM[0].as_ptr() as usize + length;
    assert_eq!(changed[offset], 0x07); // iconst_4
    changed[offset] = 0x06; // iconst_3: no longer a faithful values-array allocation
    let group = ClassGroup::new([
        changed.as_slice(),
        TEST_ENUM[1],
        TEST_ENUM[2],
        TEST_ENUM[3],
        TEST_ENUM[4],
    ])
    .unwrap();
    let error = group
        .decompile("pkg/TestEnum", &Options::default())
        .unwrap_err();
    assert!(matches!(
        error,
        DecompileError::Unsupported {
            feature: "nonstandard enum initialization"
        }
    ));
}

#[test]
fn a_values_method_exposing_the_backing_array_is_not_treated_as_generated() {
    let mut changed = SEALED[0].to_vec();
    let original = ClassFile::parse(SEALED[0]).unwrap();
    let method = original
        .methods
        .iter()
        .find(|method| original.pool.utf8(method.name_index).unwrap() == "values")
        .unwrap();
    let code = method.code(&original.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - SEALED[0].as_ptr() as usize;
    // Keep getstatic and areturn, suppress clone/checkcast. The resulting
    // method exposes the mutable backing array and must not disappear.
    changed[start + 3..start + code.bytes.len() - 1].fill(0);
    let group = ClassGroup::new([changed.as_slice(), SEALED[1]]).unwrap();
    let error = group
        .decompile("pkg/TestImplicitlySealedEnum", &Options::default())
        .unwrap_err();
    assert!(matches!(
        error,
        DecompileError::Unsupported {
            feature: "nonstandard enum lookup method"
        }
    ));
}
