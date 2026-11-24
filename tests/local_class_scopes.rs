use vineflower_rs::{Options, decompile_group};

const OUTER: &[u8] = include_bytes!("smoke/java8/TestLocalClassesSwitch.class");
const COMPANIONS: [&[u8]; 7] = [
    include_bytes!("smoke/java8/TestLocalClassesSwitch$1LocalClass.class"),
    include_bytes!("smoke/java8/TestLocalClassesSwitch$2LocalClass.class"),
    include_bytes!("smoke/java8/TestLocalClassesSwitch$3LocalClass.class"),
    include_bytes!("smoke/java8/TestLocalClassesSwitch$4LocalClass.class"),
    include_bytes!("smoke/java8/TestLocalClassesSwitch$5LocalClass.class"),
    include_bytes!("smoke/java8/TestLocalClassesSwitch$6LocalClass.class"),
    include_bytes!("smoke/java8/TestLocalClassesSwitch$7LocalClass.class"),
];

#[test]
fn same_named_local_classes_keep_distinct_scopes_after_default_only_switch() {
    let mut options = Options::default();
    options.include_line_mappings = true;
    let source = decompile_group(OUTER, COMPANIONS, &options).unwrap();
    let (other_cases, default_only) = source.text.split_once("public void test2(int i)").unwrap();
    assert_eq!(other_cases.matches("\n            class LocalClass {").count(), 3);
    assert_eq!(other_cases.matches("\n      class LocalClass {").count(), 2);
    assert!(default_only.contains("\n      {\n         class LocalClass {"));
    assert!(default_only.contains("\n         lc.test();\n      }\n\n      class LocalClass {"));
    assert_eq!(default_only.matches("class LocalClass {").count(), 2);

    let map = source.map.unwrap();
    let method = map.methods.iter().find(|method| method.name == "test2").unwrap();
    let lines: Vec<_> = source.text.lines().collect();
    assert_eq!(lines[method.offsets[&22]], "         lc.test();");
    assert_eq!(lines[method.offsets[&35]], "      lc_1.test();");
}
