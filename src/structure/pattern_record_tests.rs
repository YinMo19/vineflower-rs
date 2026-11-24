use crate::{ClassGroup, Options};

use super::*;

const J21: [&[u8]; 5] = [
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns6.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns6$I.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns6$I$R1.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns6$I$R2.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns6$I$R3.class"),
];
const J25: [&[u8]; 4] = [
    include_bytes!("../../tests/smoke/java25/TestSwitchPatternMatchingJ25.class"),
    include_bytes!("../../tests/smoke/java25/TestSwitchPatternMatchingJ25$Test5.class"),
    include_bytes!("../../tests/smoke/java25/TestSwitchPatternMatchingJ25$Test6a.class"),
    include_bytes!("../../tests/smoke/java25/TestSwitchPatternMatchingJ25$Test6b.class"),
];

#[test]
fn javac_21_record_labels_preserve_primitive_and_narrowed_bindings() {
    let group = ClassGroup::new(J21).unwrap();
    let source = group.decompile("pkg/TestRecordPatterns6", &Options::default()).unwrap().text;
    assert!(source.contains(".R1(Object o)") && source.contains(".R1(String s)"), "{source}");
    assert!(source.contains(".R2(int i)") && source.contains(".R3(String s"), "{source}");
    assert!(source.contains("return switch (") && source.contains("throw new IllegalStateException()"), "{source}");
    assert!(!source.contains("Throwable.toString") && !source.contains("catch (Throwable"), "{source}");
}

#[test]
fn javac_25_nested_and_primitive_record_paths_remain_deconstructions() {
    let group = ClassGroup::new(J25).unwrap();
    let source = group.decompile("pkg/TestSwitchPatternMatchingJ25", &Options::default()).unwrap().text;
    assert!(source.contains(".Test5(TestSwitchPatternMatchingJ25.Test5(TestSwitchPatternMatchingJ25.Test5 t)) -> t.toString();"), "{source}");
    assert!(source.contains(".Test6a(int i) -> Integer.toString(i);"), "{source}");
    assert!(source.contains(".Test6b(int i_1) -> Integer.toString(i_1);"), "{source}");
    assert!(source.contains("default -> throw new RuntimeException();"), "{source}");
    assert!(!source.contains("catch (Throwable") && !source.contains("MatchException"), "{source}");
}

#[test]
fn an_accessor_wrapper_that_covers_an_extra_instruction_is_not_removed() {
    let class = crate::classfile::ClassFile::parse(J25[0]).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test5").unwrap();
    let descriptor = crate::descriptor::MethodDescriptor::parse("(Ljava/lang/Object;)Ljava/lang/String;").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let instructions = crate::bytecode::decode(code.bytes).unwrap();
    let mut handlers = code.exceptions.clone();
    let extra = instructions.iter().find(|op| op.offset == u32::from(handlers[0].end_pc)).unwrap();
    handlers[0].end_pc = u16::try_from(extra.offset + extra.len).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &handlers).unwrap();
    let group = ClassGroup::new(J25).unwrap();
    let options = Options::default();
    let render = str::to_owned;
    let mut machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap().with_group(&group);
    assert!(Plans::prove(&instructions, &graph, &handlers, &mut machine).is_none());
}

const INSTANCEOF_21: [&[u8]; 2] = [
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns1.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns1$R.class"),
];
const INSTANCEOF_25: [&[u8]; 2] = [
    include_bytes!("../../tests/smoke/java25/TestRecordPatterns1J25.class"),
    include_bytes!("../../tests/smoke/java25/TestRecordPatterns1J25$R.class"),
];

const NARROWED: [&[u8]; 2] = [
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns5.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns5$R.class"),
];
const NESTED: [&[u8]; 4] = [
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns7.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns7$A.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns7$B.class"),
    include_bytes!("../../tests/smoke/java21/TestRecordPatterns7$C.class"),
];
const UNNAMED: [&[u8]; 2] = [
    include_bytes!("../../tests/smoke/java25/TestUnnamedVar1.class"),
    include_bytes!("../../tests/smoke/java25/TestUnnamedVar1$Point.class"),
];

#[test]
fn javac_record_instanceof_keeps_typed_bindings_and_the_short_circuit_guard() {
    for (classes, owner) in [
        (INSTANCEOF_21, "pkg/TestRecordPatterns1"),
        (INSTANCEOF_25, "pkg/TestRecordPatterns1J25"),
    ] {
        let group = ClassGroup::new(classes).unwrap();
        let source = group.decompile(owner, &Options::default()).unwrap().text;
        assert_eq!(source.matches("r instanceof ").count(), 4, "{source}");
        assert!(source.contains("R(int x, Object o)"), "{source}");
        assert!(source.contains("R(int x, Object v)"), "{source}");
        assert_eq!(source.matches("R(int x, String s)").count(), 2, "{source}");
        assert!(source.contains("&&") && source.contains("s.length() > 10"), "{source}");
        assert_eq!(source.matches("System.out.println(x);").count(), 4, "{source}");
        assert!(!source.contains("MatchException") && !source.contains("catch ("), "{source}");
    }
}

#[test]
fn a_component_branch_to_a_different_failure_edge_is_not_projected() {
    let class = crate::classfile::ClassFile::parse(INSTANCEOF_21[0]).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test2").unwrap();
    let descriptor = crate::descriptor::MethodDescriptor::parse("(Lpkg/TestRecordPatterns1$R;)V").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let mut instructions = crate::bytecode::decode(code.bytes).unwrap();
    let second_test = instructions.iter().enumerate().filter(|(_, op)| op.opcode == 0xc1).nth(1).unwrap().0;
    let early_return = instructions.last().unwrap().offset;
    instructions[second_test + 1].operand = Operand::Branch(early_return);
    let graph = ControlFlowGraph::build(&instructions, &code.exceptions).unwrap();
    let group = ClassGroup::new(INSTANCEOF_21).unwrap();
    let options = Options::default();
    let render = str::to_owned;
    let mut machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap().with_group(&group);
    assert!(Plans::prove(&instructions, &graph, &code.exceptions, &mut machine).is_none());
}

#[test]
fn a_narrowed_number_and_total_string_bind_across_guards() {
    let group = ClassGroup::new(NARROWED).unwrap();
    let source = group.decompile("pkg/TestRecordPatterns5", &Options::default()).unwrap().text;
    assert_eq!(source.matches("r instanceof TestRecordPatterns5.R(Integer x, String s)").count(), 3, "{source}");
    assert_eq!(source.matches("&& s.length() > 10").count(), 2, "{source}");
    assert!(source.contains("== 3") && !source.contains("MatchException"), "{source}");
}

#[test]
fn nested_record_receivers_bind_in_source_order_after_outer_components() {
    let group = ClassGroup::new(NESTED).unwrap();
    let options = Options { preferred_line_length: 512, ..Options::default() };
    let source = group.decompile("pkg/TestRecordPatterns7", &options).unwrap().text;
    let pattern = "TestRecordPatterns7.A(TestRecordPatterns7.C(TestRecordPatterns7.B(int i1, int i2), int i3), int i4, TestRecordPatterns7.B(int i5, int i6))";
    assert!(source.contains(&format!("o instanceof {pattern}")), "{source}");
    assert!(source.contains(&format!("case {pattern} ->")), "{source}");
    assert_eq!(source.matches("i1 + i2 + i3 + i4 + i5 + i6").count(), 2, "{source}");
    assert!(!source.contains("MatchException"), "{source}");
}

#[test]
fn nested_components_require_the_same_failure_edge_receiver_and_wrapper() {
    use crate::{bytecode, classfile::ClassFile, descriptor::MethodDescriptor};
    let class = ClassFile::parse(NESTED[0]).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test").unwrap();
    let descriptor = MethodDescriptor::parse("(Ljava/lang/Object;)V").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let instructions = bytecode::decode(code.bytes).unwrap();
    let group = ClassGroup::new(NESTED).unwrap();
    let options = Options::default();
    let render = str::to_owned;
    let mut machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap().with_group(&group);
    let rejects = |instructions: &[Instruction], handlers: &[ExceptionHandler], machine: &mut Machine<'_, '_>| {
        let graph = ControlFlowGraph::build(instructions, handlers).unwrap();
        assert!(Plans::prove(instructions, &graph, handlers, machine).is_none());
    };
    let tested = instructions.iter().enumerate().filter(|(_, op)| op.opcode == 0xc1).nth(1).unwrap().0;
    let mut inverted = instructions.clone();
    inverted[tested + 1].opcode = 0x9a; // Reject a non-null C instead of rejecting null.
    rejects(&inverted, &code.exceptions, &mut machine);

    let mut swapped = instructions.clone();
    let mut b_reads = swapped.iter().enumerate().filter_map(|(i, op)| {
        (method_ref(&class.pool, op, 0xb6) == Some(("pkg/TestRecordPatterns7$B", "i1", "()I"))).then(|| i - 1)
    });
    let (first, sibling) = (b_reads.next().unwrap(), b_reads.next().unwrap());
    assert_eq!(swapped[first].opcode, swapped[sibling].opcode);
    swapped[first].operand = swapped[sibling].operand.clone();
    rejects(&swapped, &code.exceptions, &mut machine);

    // A different handler remains independently reachable on this edge even
    // when it happens to have the same throw instructions.
    let mut split = instructions;
    let mut handlers = code.exceptions.clone();
    let graph = ControlFlowGraph::build(&split, &handlers).unwrap();
    let old = u32::from(handlers[0].handler_pc);
    let wrapper = graph.block_at(old).unwrap();
    let new = split.last().unwrap().offset + split.last().unwrap().len;
    let duplicate: Vec<_> = split[graph.blocks[wrapper].instructions.clone()].iter().cloned()
        .map(|op| Instruction { offset: op.offset - old + new, ..op }).collect();
    split.extend(duplicate);
    handlers.last_mut().unwrap().handler_pc = u16::try_from(new).unwrap();
    rejects(&split, &handlers, &mut machine);
}

#[test]
fn unnamed_record_components_drop_only_the_component_binding() {
    use crate::{bytecode, classfile::ClassFile, descriptor::MethodDescriptor, structure::structure_with_handlers};
    let class = ClassFile::parse(UNNAMED[0]).unwrap();
    let group = ClassGroup::new(UNNAMED).unwrap();
    let options = Options::default();
    let render = |name: &str| name.rsplit('/').next().unwrap().replace('$', ".");
    let descriptor = MethodDescriptor::parse("(Ljava/lang/Object;)V").unwrap();
    for (name, pattern) in [
        ("test", "o instanceof TestUnnamedVar1.Point(int x, _)"),
        ("test1", "o instanceof TestUnnamedVar1.Point(int x, Integer _)"),
    ] {
        let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == name).unwrap();
        let code = method.code(&class.pool).unwrap().unwrap();
        let instructions = bytecode::decode(code.bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &code.exceptions).unwrap();
        let machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap().with_group(&group);
        let lines = structure_with_handlers(&instructions, &graph, machine, &code.exceptions).unwrap();
        assert!(lines.iter().any(|line| line.text.contains(pattern)), "{lines:#?}");
        assert!(lines.iter().any(|line| line.text.contains("System.out.println(x);")), "{lines:#?}");
    }
}

#[test]
#[ignore = "requires a Java 21 JDK at VINEFLOWER_JDK_21"]
fn recompiles_original_nested_record_inputs_and_preserves_null_and_type_failure() {
    use std::{fs, path::Path, process::Command};

    let home = std::env::var_os("VINEFLOWER_JDK_21").expect("set VINEFLOWER_JDK_21");
    let bin = Path::new(&home).join("bin");
    let tool = |name| bin.join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
    let scratch = tempfile::tempdir().unwrap();
    let originals = scratch.path().join("original");
    let regenerated = scratch.path().join("decompiled");
    let probes = scratch.path().join("RecordPatternsProbe.java");
    fs::create_dir(&originals).unwrap();
    fs::create_dir(&regenerated).unwrap();
    fs::write(&probes, r#"package pkg;
        public class RecordPatternsProbe {
            public static void main(String[] args) {
                var narrow = new TestRecordPatterns5();
                narrow.test1(new TestRecordPatterns5.R(1, null));
                narrow.test1(new TestRecordPatterns5.R(1.0, null));
                narrow.test1(new TestRecordPatterns5.R(null, null));
                narrow.test1(null);
                narrow.test2(new TestRecordPatterns5.R(2, "01234567890"));
                narrow.test3(new TestRecordPatterns5.R(3, "01234567890"));
                narrow.test3(new TestRecordPatterns5.R(4, "01234567890"));
                var nested = new TestRecordPatterns7();
                var b = new TestRecordPatterns7.B(1, 2);
                var c = new TestRecordPatterns7.C(b, 3);
                var a = new TestRecordPatterns7.A(c, 4, new TestRecordPatterns7.B(5, 6));
                nested.test(a);
                nested.test(new TestRecordPatterns7.A(null, 4, b));
                nested.test(new TestRecordPatterns7.A(new TestRecordPatterns7.C(null, 3), 4, b));
                nested.test(new TestRecordPatterns7.A(c, 4, null));
                nested.test(null);
                nested.test2(a);
                nested.test2(new TestRecordPatterns7.A(c, 4, null));
            }
        }"#).unwrap();
    let fixtures: [(&str, &str, &[&str]); 2] = [
        ("TestRecordPatterns5", include_str!("../../tests/upstream/testData/src/java21/pkg/TestRecordPatterns5.java"), &["R"]),
        ("TestRecordPatterns7", include_str!("../../tests/upstream/testData/src/java21/pkg/TestRecordPatterns7.java"), &["A", "B", "C"]),
    ];
    let compile = |directory: &Path| {
        let result = Command::new(tool("javac")).args(["--release", "21", "-g", "-d"])
            .arg(directory).arg(&probes)
            .args(fixtures.iter().map(|(name, _, _)| directory.join(format!("{name}.java"))))
            .output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    };
    let run = |directory: &Path| {
        let result = Command::new(tool("java")).arg("-cp").arg(directory)
            .arg("pkg.RecordPatternsProbe").output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        String::from_utf8(result.stdout).unwrap().replace("\r\n", "\n")
    };
    for (name, source, _) in fixtures {
        fs::write(originals.join(format!("{name}.java")), source).unwrap();
    }
    compile(&originals);
    for (name, _, companions) in fixtures {
        let classes = std::iter::once(format!("{name}.class"))
            .chain(companions.iter().map(|suffix| format!("{name}${suffix}.class")))
            .map(|file| fs::read(originals.join("pkg").join(file)).unwrap())
            .collect::<Vec<_>>();
        let group = ClassGroup::new(classes.iter().map(Vec::as_slice)).unwrap();
        let source = group.decompile(&format!("pkg/{name}"), &Options::default()).unwrap().text;
        fs::write(regenerated.join(format!("{name}.java")), source).unwrap();
    }
    compile(&regenerated);
    let expected = run(&originals);
    assert_eq!(expected, "1\nnull\n2\n01234567890\n3\n01234567890\n21\n21\n0\n");
    assert_eq!(run(&regenerated), expected);
}
