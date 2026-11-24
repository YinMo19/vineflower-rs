use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{Attribute, ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    lift::Machine,
    options::Options,
    source_text::tokens::TokenKind,
    structure::structure,
};

use super::Line;

const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x10\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x04(Z)I\x01\0\x12LocalVariableTable\x01\0\x06result\x01\0\x01I\
    \x01\0\x05other\x01\0\x07consume\x01\0\x04(I)V\x0c\0\x0b\0\x0c\x0a\0\x02\0\x0d\x01\0\x01Z\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";
const FLAT: &[u8] = &[0x1a, 0x99, 0, 8, 0x06, 0x3c, 0xa7, 0, 5, 0x05, 0x3c, 0x1b, 0xac];

fn lift(bytes: &[u8], descriptor: &str, lvt: &[[u16; 5]], tokens: bool) -> Vec<Line> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
    let mut entries = (lvt.len() as u16).to_be_bytes().to_vec();
    entries.extend(lvt.iter().flatten().flat_map(|value| value.to_be_bytes()));
    let code = Code {
        max_stack: 4,
        max_locals: 4,
        bytes,
        exceptions: vec![],
        attributes: vec![Attribute { name_index: 7, data: &entries }],
    };
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    let options = Options { dump_text_tokens: tokens, ..Options::default() };
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let machine = Machine::new(&class, &method, &code, &descriptor, &options, &str::to_owned).unwrap();
    structure(&instructions, &graph, machine).unwrap()
}

#[test]
fn adopts_the_proven_debug_binding_and_retains_store_offsets_and_tokens() {
    let lines = lift(FLAT, "(Z)I", &[[6, 3, 8, 9, 1], [11, 2, 8, 9, 1]], true);
    assert_eq!(lines[0].text, "int result;");
    assert_eq!(lines[2].text, "result = 3;");
    assert_eq!(lines[2].offsets, [4, 5]);
    assert_eq!(lines[4].text, "result = 2;");
    assert_eq!(lines[4].offsets, [9, 10]);
    assert_eq!(lines[6].text, "return result;");
    let tokens = lines.iter().flat_map(|line| line.text.flat_tokens())
        .filter_map(|(_, token)| match &token.kind {
            TokenKind::Variable { index, name, .. } if name == "result" => Some((*index, token.declaration)),
            _ => None,
        }).collect::<Vec<_>>();
    assert_eq!(tokens, [(1, true), (1, false), (1, false), (1, false)]);
}

#[test]
fn nested_joins_share_one_declaration_without_renaming_other_bindings() {
    let code = [
        0x1a, 0x99, 0, 17, 0x1b, 0x99, 0, 8, 0x04, 0x3d, 0xa7, 0, 19, 0x05, 0x3d, 0xa7, 0, 14,
        0x1b, 0x99, 0, 8, 0x06, 0x3d, 0xa7, 0, 5, 0x07, 0x3d, 0x1c, 0xac,
    ];
    let lvt = [[10, 3, 8, 9, 2], [15, 3, 8, 9, 2], [24, 3, 8, 9, 2], [29, 2, 8, 9, 2]];
    let lines = lift(&code, "(ZZ)I", &lvt, false);
    assert_eq!(lines[0].text, "int result;");
    assert_eq!(lines.iter().filter(|line| line.text == "int result;").count(), 1);
    assert_eq!(lines.iter().filter(|line| line.text.starts_with("result = ")).count(), 4);
    assert!(!lines.iter().any(|line| line.text.contains("result_")));
}

#[test]
fn preserves_an_arm_alias_with_an_independent_use_before_the_merge() {
    let code = [0x1a, 0x99, 0, 8, 0x04, 0x3c, 0xa7, 0, 9, 0x05, 0x3c, 0x1b, 0xb8, 0, 14, 0x1b, 0xac];
    let lvt = [[6, 3, 8, 9, 1], [11, 4, 8, 9, 1], [15, 2, 8, 9, 1]];
    let lines = lift(&code, "(Z)I", &lvt, false);
    assert_eq!(lines[0].text, "int result;");
    let consume = lines.iter().position(|line| line.text.contains("consume(result_1)")).unwrap();
    assert_eq!(lines[consume - 1].text, "int result_1 = 2;");
    assert_eq!(lines[consume + 1].text, "result = result_1;");
}

#[test]
fn distinct_lvt_fragments_or_an_existing_name_do_not_grant_ownership() {
    let different = lift(FLAT, "(Z)I", &[[6, 3, 10, 9, 1], [11, 2, 8, 9, 1]], false);
    assert_eq!(different[0].text, "int result_1;");
    let collision = lift(FLAT, "(Z)I", &[[0, 13, 8, 15, 0], [6, 3, 8, 9, 1], [11, 2, 8, 9, 1]], false);
    assert!(collision[0].text.starts_with("int result_"));
    assert_eq!(collision[1].text, "if (result) {");
}
