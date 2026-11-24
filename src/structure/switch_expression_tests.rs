use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    options::Options,
    structure::{StructureError, structure},
};

use super::*;

// Example extends Object. #9/#13 method refs are side()I/take(II)I;
// #17 is Example.<init>(String)V, which competes with <init>(Integer)V.
// #23 is String.<init>()V.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3c\0\x18\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()I\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \x01\0\x04take\x01\0\x05(II)I\x0c\0\x0a\0\x0b\x0a\0\x02\0\x0c\
    \x01\0\x06<init>\x01\0\x15(Ljava/lang/String;)V\x0c\0\x0e\0\x0f\x0a\0\x02\0\x10\
    \x01\0\x16(Ljava/lang/Integer;)V\
    \x01\0\x10java/lang/String\x07\0\x13\x01\0\x03()V\x0c\0\x0e\0\x15\x0a\0\x14\0\x16\
    \0\x21\0\x02\0\x04\0\0\0\0\0\x02\
    \0\x01\0\x0e\0\x0f\0\0\0\x01\0\x0e\0\x12\0\0\0\0";

fn lift(
    bytes: &[u8],
    signature: &str,
    major: u16,
    minor: u16,
) -> Result<Vec<Line>, StructureError> {
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
    lift_method(bytes, signature, major, minor, &method)
}

fn lift_method(
    bytes: &[u8],
    signature: &str,
    major: u16,
    minor: u16,
    method: &Member<'_>,
) -> Result<Vec<Line>, StructureError> {
    let mut class = ClassFile::parse(CLASS).unwrap();
    class.major_version = major;
    class.minor_version = minor;
    let code = Code {
        max_stack: 8,
        max_locals: 3,
        bytes,
        exceptions: vec![],
        attributes: vec![],
    };
    let descriptor = MethodDescriptor::parse(signature).unwrap();
    let options = Options::default();
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let machine = Machine::new(
        &class,
        method,
        &code,
        &descriptor,
        &options,
        &|name| name.replace('/', "."),
    )
    .unwrap();
    structure(&instructions, &graph, machine)
}

// Test labels are offsets relative to the end of the dispatch instruction.
fn lookup(bytes: &mut Vec<u8>, default: usize, cases: &[(i32, usize)]) {
    let start = bytes.len();
    bytes.push(0xab);
    bytes.resize(bytes.len().next_multiple_of(4), 0);
    let end = bytes.len() + 8 + 8 * cases.len();
    let offset = |after: usize| i32::try_from(end + after - start).unwrap().to_be_bytes();
    bytes.extend(offset(default));
    bytes.extend(i32::try_from(cases.len()).unwrap().to_be_bytes());
    for &(key, after) in cases {
        bytes.extend(key.to_be_bytes());
        bytes.extend(offset(after));
    }
}

fn int_switch(prefix: &[u8], continuation: &[u8]) -> Vec<u8> {
    let mut bytes = prefix.to_vec();
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([0x05, 0xa7, 0, 4, 0x06]);
    bytes.extend(continuation);
    bytes
}

fn render(line: &Line) -> (String, Vec<(u32, usize)>) {
    let mut text = String::new();
    let mut mapping = line
        .offsets
        .iter()
        .map(|&byte| (byte, 0))
        .collect::<Vec<_>>();
    line.text.render_at(
        &mut text,
        usize::MAX,
        "   ",
        false,
        line.depth,
        |offsets, line| {
            mapping.extend(offsets.map(|byte| (byte, line)));
        },
    );
    (text, mapping)
}

#[test]
fn resumes_a_default_only_switch_at_the_selected_constructor() {
    let mut bytes = vec![0x2a, 0x1b];
    lookup(&mut bytes, 0, &[]);
    bytes.extend([0x01, 0xb7, 0, 17, 0xb1]);
    let method = Member {
        access_flags: 0x0001,
        name_index: 14,
        descriptor_index: 6,
        attributes: vec![],
    };
    let lines = lift_method(&bytes, "(I)V", 60, 0, &method).unwrap();
    let (text, mapping) = render(&lines[0]);
    assert_eq!(text, "this(switch (var1) {\n   default -> (java.lang.String)null;\n});");
    assert_eq!(mapping.iter().find(|&&(byte, _)| byte == 12), Some(&(12, 1)));
    assert_eq!(mapping.iter().find(|&&(byte, _)| byte == 13), Some(&(13, 0)));
    assert_eq!(lines[1].text.as_flat(), "return;");
    assert!(lift_method(&bytes, "(I)V", 59, 0, &method).is_err());
}

#[test]
fn retains_a_nested_allocation_in_the_default_constructor_rule() {
    let mut bytes = vec![0x2a, 0x1b];
    lookup(&mut bytes, 0, &[]);
    bytes.extend([0xbb, 0, 20, 0x59, 0xb7, 0, 23, 0xb7, 0, 17, 0xb1]);
    let method = Member {
        access_flags: 0x0001,
        name_index: 14,
        descriptor_index: 6,
        attributes: vec![],
    };
    let lines = lift_method(&bytes, "(I)V", 60, 0, &method).unwrap();
    assert_eq!(
        render(&lines[0]).0,
        "this(switch (var1) {\n   default -> new java.lang.String();\n});"
    );
}

#[test]
fn recovers_shared_predicate_continuations_with_edge_polarity() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 14, &[(1, 0), (2, 7)]);
    bytes.extend([
        0x1b, 0x9c, 0, 19, 0xa7, 0, 14,
        0x1b, 0x9d, 0, 10, 0xa7, 0, 9,
        0x1b, 0x9a, 0, 5,
        0x08, 0xac, 0x06, 0xac,
    ]);
    let lines = lift(&bytes, "(II)I", 60, 0).unwrap();
    let (text, mapping) = render(&lines[0]);
    assert_eq!(
        text,
        "if (switch (var0) {\n   case 1 -> var1 < 0;\n   case 2 -> var1 > 0;\n   default -> var1 == 0;\n}) {"
    );
    assert!(mapping.contains(&(29, 1)));
    assert!(mapping.contains(&(36, 2)));
    assert!(mapping.contains(&(43, 3)));
    assert!(!mapping.iter().any(|&(byte, _)| matches!(byte, 32..=34 | 39..=41)));
    let returns: Vec<_> = lines.iter().filter(|line| line.text.as_flat().starts_with("return "))
        .map(|line| line.text.as_flat()).collect();
    assert_eq!(returns, ["return 5;", "return 3;"]);
}

#[test]
fn accepts_the_if_body_falling_through_to_the_shared_bypass() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 14, &[(1, 0), (2, 7)]);
    bytes.extend([
        0x1b, 0x9c, 0, 21, 0xa7, 0, 14,
        0x1b, 0x9d, 0, 10, 0xa7, 0, 11,
        0x1b, 0x9a, 0, 7,
        0xb8, 0, 9, 0x57, 0xb1,
    ]);
    let lines = lift(&bytes, "(II)V", 60, 0).unwrap();
    assert_eq!(
        render(&lines[0]).0,
        "if (switch (var0) {\n   case 1 -> var1 < 0;\n   case 2 -> var1 > 0;\n   default -> var1 == 0;\n}) {"
    );
    let continuation: Vec<_> = lines[1..].iter()
        .map(|line| (line.depth, line.text.as_flat())).collect();
    assert_eq!(continuation, [(1, "Example.side();"), (0, "}"), (0, "return;")]);
}

#[test]
fn keeps_definite_assignment_on_the_predicate_success_edges() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 9, &[(0, 0)]);
    bytes.extend([
        0x1b, 0x9e, 0, 20, 0x08, 0x3d, 0xa7, 0, 13,
        0x1b, 0x9c, 0, 11, 0x10, 17, 0x3d, 0xa7, 0, 3,
        0x1c, 0xac, 0x03, 0xac,
    ]);
    let instructions = decode(&bytes).unwrap();
    let mut graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let [yes, no] = predicate::Cut::prove(&instructions, &graph, 0, None).unwrap().outcomes;
    let arm = graph.block_at(20).unwrap();
    graph.blocks[arm].predecessors.push(yes);
    assert!(predicate::Cut::prove(&instructions, &graph, 0, None).is_none());
    assert_eq!(graph.blocks[arm].predecessors.pop(), Some(yes));
    graph.blocks[arm].exception_successors.push(no);
    assert!(predicate::Cut::prove(&instructions, &graph, 0, None).is_none());

    let lines = lift(&bytes, "(II)I", 60, 0).unwrap();
    let declaration = lines[0].text.as_flat();
    assert!(declaration.starts_with("int ") && declaration.ends_with(';') && !declaration.contains('='));
    let dispatch = lines.iter().find(|line| line.text.as_flat().starts_with("predicate0False: switch")).unwrap();
    assert_eq!(render(dispatch).0.matches("break predicate0True;").count(), 2);
    assert_eq!(lines.iter().filter(|line| line.text.as_flat().starts_with("return ")).count(), 2);
}

#[test]
fn joins_return_values_with_their_bytecode_offsets() {
    let bytes = int_switch(&[0x1a], &[0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert_eq!(lines.len(), 1);
    let (text, mapping) = render(&lines[0]);
    assert_eq!(
        text,
        "return switch (var0) {\n   case 7 -> 2;\n   default -> 3;\n};"
    );
    let header = (0..20).chain(25..26).map(|byte| (byte, 0));
    assert_eq!(
        mapping,
        header.chain([(20, 1), (24, 2)]).collect::<Vec<_>>()
    );
}

#[test]
fn groups_labels_and_retains_explicit_throws_in_assignments() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 8, &[(1, 0), (2, 4), (3, 0), (4, 4)]);
    bytes.extend([
        0x05, 0xa7, 0, 9, 0x06, 0xa7, 0, 5, 0x01, 0xbf, 0x3c, 0x1b, 0xac,
    ]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    let (text, mapping) = render(&lines[0]);
    assert_eq!(
        text,
        "int var1 = switch (var0) {\n   case 1, 3 -> 2;\n   case 2, 4 -> 3;\n   default -> throw null;\n};"
    );
    assert_eq!(lines[1].text.as_flat(), "return var1;");
    let throw = u32::try_from(bytes.len() - 4).unwrap();
    assert!(mapping.contains(&(throw, 3)));
}

#[test]
fn keeps_a_preceding_argument_outside_the_switch() {
    let bytes = int_switch(&[0xb8, 0, 9, 0x1a], &[0xb8, 0, 13, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert_eq!(lines.len(), 1);
    assert_eq!(
        render(&lines[0]).0,
        "return Example.take(Example.side(), switch (var0) {\n   case 7 -> 2;\n   default -> 3;\n});"
    );
}

#[test]
fn composes_a_switch_used_as_the_next_selector() {
    let bytes = int_switch(&int_switch(&[0x1a], &[]), &[0xac]);
    let lines = lift(&bytes, "(I)I", 61, 0).unwrap();
    assert_eq!(
        render(&lines[0]).0,
        "return switch (switch (var0) {\n   case 7 -> 2;\n   default -> 3;\n}) {\n   case 7 -> 2;\n   default -> 3;\n};"
    );
}

#[test]
fn retains_arm_work_before_the_yield() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([0x05, 0xa7, 0, 8, 0xb8, 0, 9, 0x57, 0x06, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    let (text, mapping) = render(&lines[0]);
    assert_eq!(
        text,
        "return switch (var0) {\n   case 7 -> 2;\n   default -> {\n      Example.side();\n      yield 3;\n   }\n};"
    );
    assert!((24..27).all(|byte| mapping.contains(&(byte, 3))));
    assert!(!mapping.iter().any(|&(byte, _)| byte == 27));
    assert!(mapping.contains(&(28, 4)));
}

#[test]
fn keeps_a_loop_owned_by_one_rule() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([
        0x05, 0xa7, 0, 16, 0x03, 0x3c, 0x1b, 0x9c, 0, 9, 0x84, 1, 1, 0xa7, 0xff, 0xf9, 0x06, 0xac,
    ]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    let (text, _) = render(&lines[0]);
    assert!(text.starts_with("return switch "));
    assert!(text.contains("\n      while ("));
    assert!(text.contains("\n      yield 3;"));
}

#[test]
fn joins_a_single_category_two_value() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([0x09, 0xa7, 0, 4, 0x0a, 0xad]);
    let lines = lift(&bytes, "(I)J", 60, 0).unwrap();
    assert_eq!(
        render(&lines[0]).0,
        "return switch (var0) {\n   case 7 -> 0L;\n   default -> 1L;\n};"
    );
}

#[test]
fn preserves_statement_form_before_vineflowers_java16_gate() {
    let bytes = int_switch(&[0x1a], &[0xac]);
    for (major, minor) in [(52, 0), (56, u16::MAX), (57, u16::MAX), (58, 0), (59, 0)] {
        let lines = lift(&bytes, "(I)I", major, minor).unwrap();
        assert!(
            lines
                .iter()
                .any(|line| line.text.as_flat() == "switch (var0) {")
        );
        assert!(
            lines
                .iter()
                .all(|line| !line.text.as_flat().contains(" -> "))
        );
    }
    let preview = lift(&bytes, "(I)I", 60, u16::MAX).unwrap();
    assert!(preview[0].text.as_flat().starts_with("return switch "));
}

#[test]
fn falls_back_when_an_arm_uses_the_dispatch_stack_prefix() {
    let mut bytes = vec![0x04, 0x1a];
    lookup(&mut bytes, 5, &[(7, 0)]);
    bytes.extend([0x05, 0x60, 0xa7, 0, 5, 0x06, 0x60, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "switch (var0) {")
    );
    assert!(
        lines
            .iter()
            .all(|line| !line.text.as_flat().contains(" -> "))
    );
}

#[test]
fn does_not_move_a_method_return_into_a_switch_rule() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 6, &[(7, 0), (8, 2)]);
    bytes.extend([0x04, 0xac, 0x05, 0xa7, 0, 4, 0x06, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(lines.iter().any(|line| line.text.as_flat() == "return 1;"));
    assert!(
        lines
            .iter()
            .all(|line| !line.text.as_flat().contains(" -> "))
    );
}

#[test]
fn keeps_local_declarations_outside_when_the_join_reads_them() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 6, &[(7, 0)]);
    bytes.extend([
        0x06, 0x3c, 0x05, 0xa7, 0, 6, 0x07, 0x3c, 0x08, 0x1b, 0x60, 0xac,
    ]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "switch (var0) {")
    );
    assert!(
        lines
            .iter()
            .all(|line| !line.text.as_flat().contains(" -> "))
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "int var1_2;")
    );
}

#[test]
fn does_not_fold_two_joined_operands_into_one_value() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 5, &[(7, 0)]);
    bytes.extend([0x05, 0x06, 0xa7, 0, 5, 0x07, 0x08, 0x60, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "switch (var0) {")
    );
    assert!(
        lines
            .iter()
            .all(|line| !line.text.as_flat().contains(" -> "))
    );
}

#[test]
fn rejects_incompatible_result_categories() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([0x05, 0xa7, 0, 4, 0x0a, 0xac]);
    let error = lift(&bytes, "(I)I", 60, 0).unwrap_err();
    assert!(matches!(
        error,
        StructureError::Lift(crate::lift::LiftError::InvalidStack { .. })
    ));
}
