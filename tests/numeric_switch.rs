use vineflower_rs::{Options, decompile};

// The original java8 TestClassSwitch fixture, compiled with debug info.
const CLASS: &[u8] = include_bytes!("smoke/java8/TestClassSwitch.class");

#[test]
fn lookup_switch_orders_terminal_chains_without_separating_default() {
    let mut options = Options::default();
    options.include_line_mappings = true;
    let source = decompile(CLASS, &options).unwrap();
    let (ordered, _) = source.text.split_once("public void testFallThrough").unwrap();
    let expected = concat!(
        "      switch (a) {\n",
        "         case 5:\n",
        "            System.out.println(5);\n",
        "         default:\n",
        "            return;\n",
        "         case 13:\n",
        "            System.out.println(13);\n",
        "      }\n",
        "   }\n",
    );
    assert!(ordered.contains(expected), "{ordered}");

    let lines: Vec<_> = source.text.lines().collect();
    let map = source.map.unwrap();
    let method = map.methods.iter().find(|method| method.name == "testCaseOrder").unwrap();
    for (offset, statement) in [
        (0, "      switch (a) {"),
        (28, "            System.out.println(13);"),
        (36, "   }"),
        (37, "            System.out.println(5);"),
        (44, "            return;"),
    ] {
        assert_eq!(lines[method.offsets[&offset]], statement, "offset {offset}");
    }
}

#[test]
fn table_switch_emits_only_true_default_aliases_and_keeps_fallthrough() {
    let mut options = Options::default();
    options.include_line_mappings = true;
    let source = decompile(CLASS, &options).unwrap();
    let (_, dense) = source.text.split_once("public void testFallThrough").unwrap();
    let labels: Vec<_> = dense.lines().map(str::trim).filter(|line| {
        line.starts_with("case ") || *line == "default:"
    }).collect();
    assert_eq!(labels, [
        "case 6:", "case 7:", "case 8:", "case 9:", "case 10:", "case 11:",
        "case 12:", "case 14:", "case 15:", "case 16:", "default:", "case 13:",
        "case 5:", "case 17:", "case 18:", "case 19:", "case 20:",
    ]);
    assert!(dense.contains(concat!(
        "         default:\n",
        "            break;\n",
        "         case 13:\n",
        "            System.out.println(13);\n",
        "         case 5:\n",
    )), "{dense}");
    assert_eq!(dense.matches("break;").count(), 2, "{dense}");

    let lines: Vec<_> = source.text.lines().collect();
    let map = source.map.unwrap();
    let method = map.methods.iter().find(|method| method.name == "testFallThrough").unwrap();
    for (offset, statement) in [
        (3, "switch (a) {"),
        (84, "System.out.println(13);"),
        (92, "System.out.println(5);"),
        (102, "break;"),
        (105, "System.out.println(17);"),
        (121, "System.out.println(\"hi\");"),
        (134, "System.out.println(x);"),
    ] {
        assert_eq!(lines[method.offsets[&offset]].trim(), statement, "offset {offset}");
    }
}
