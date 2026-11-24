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
