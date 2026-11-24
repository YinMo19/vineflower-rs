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
