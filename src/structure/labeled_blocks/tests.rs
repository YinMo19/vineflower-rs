use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{Attribute, ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    options::Options,
};

use super::{Machine, super::{Line, structure}};

// Example.side()V plus the names for a split javac LocalVariableTable entry.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x34\0\x0d\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()V\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \x01\0\x12LocalVariableTable\x01\0\x06result\x01\0\x01Z\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn lift(bytes: &[u8], debug: Option<&[u8]>) -> Vec<Line> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member { access_flags: 8, name_index: 5, descriptor_index: 6, attributes: vec![] };
    let code = Code {
        max_stack: 2, max_locals: 3, bytes, exceptions: vec![],
        attributes: debug.into_iter().map(|data| Attribute { name_index: 10, data }).collect(),
    };
    let descriptor = MethodDescriptor::parse("(ZZ)Z").unwrap();
    let options = Options::default();
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let machine = Machine::new(&class, &method, &code, &descriptor, &options, &str::to_owned).unwrap();
    structure(&instructions, &graph, machine).unwrap()
}

#[test]
fn combines_the_labeled_jump_and_normal_fallthrough_into_one_result() {
    let lines = lift(&[
        0x1a, 0x99, 0, 15, 0xb8, 0, 9, 0x1b, 0x99, 0, 8,
        0x03, 0x3d, 0xa7, 0, 5, 0x04, 0x3d, 0x1c, 0xac,
    ], Some(&[0, 2, 0, 13, 0, 3, 0, 11, 0, 12, 0, 2, 0, 18, 0, 2, 0, 11, 0, 12, 0, 2]));
    let output: Vec<_> = lines.iter().map(|line| (line.depth, line.text.as_str())).collect();
    assert_eq!(output, [
        (0, "boolean result;"), (0, "label18: {"), (1, "if (var0) {"),
        (2, "Example.side();"), (2, "if (var1) {"), (3, "result = false;"),
        (3, "break label18;"), (2, "}"), (1, "}"), (1, "result = true;"),
        (0, "}"), (0, "return result;"),
    ]);
    assert_eq!(lines[6].offsets, [13]);
    assert_eq!(lines[9].offsets, [16, 17]);
}

#[test]
fn an_ordinary_diamond_does_not_need_a_java_label() {
    let lines = lift(&[0x1a, 0x99, 0, 7, 0x03, 0xa7, 0, 4, 0x04, 0xac], None);
    assert!(lines.iter().all(|line| !line.text.contains("label")));
}
