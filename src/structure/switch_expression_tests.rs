use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    options::Options,
    structure::{StructureError, structure},
};

use super::*;

// Example extends Object; #9 is Example.side()I and #13 is Example.take(II)I.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3c\0\x0e\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()I\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \x01\0\x04take\x01\0\x05(II)I\x0c\0\x0a\0\x0b\x0a\0\x02\0\x0c\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn lift(
    bytes: &[u8],
    signature: &str,
    major: u16,
    minor: u16,
) -> Result<Vec<Line>, StructureError> {
    let mut class = ClassFile::parse(CLASS).unwrap();
    class.major_version = major;
    class.minor_version = minor;
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
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
        &method,
        &code,
        &descriptor,
        &options,
        &str::to_owned,
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

#[test]
fn joins_return_values_with_their_bytecode_offsets() {
    let bytes = int_switch(&[0x1a], &[0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert_eq!(lines.len(), 1);
    assert_eq!(
        lines[0].text,
        "return switch (var0) { case 7 -> 2; default -> 3; };"
    );
    assert_eq!(lines[0].offsets, (0..21).chain(24..26).collect::<Vec<_>>());
}

#[test]
fn groups_labels_and_retains_explicit_throws_in_assignments() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 8, &[(1, 0), (2, 4), (3, 0), (4, 4)]);
    bytes.extend([
        0x05, 0xa7, 0, 9, 0x06, 0xa7, 0, 5, 0x01, 0xbf, 0x3c, 0x1b, 0xac,
    ]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert_eq!(
        lines[0].text,
        "int var1 = switch (var0) { case 1, 3 -> 2; case 2, 4 -> 3; default -> throw null; };"
    );
    assert_eq!(lines[1].text, "return var1;");
    let throw = u32::try_from(bytes.len() - 4).unwrap();
    assert!(lines[0].offsets.contains(&throw));
}

#[test]
fn keeps_a_preceding_argument_outside_the_switch() {
    let bytes = int_switch(&[0xb8, 0, 9, 0x1a], &[0xb8, 0, 13, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert_eq!(lines.len(), 1);
    assert_eq!(
        lines[0].text,
        "return Example.take(Example.side(), switch (var0) { case 7 -> 2; default -> 3; });"
    );
}

#[test]
fn composes_a_switch_used_as_the_next_selector() {
    let bytes = int_switch(&int_switch(&[0x1a], &[]), &[0xac]);
    let lines = lift(&bytes, "(I)I", 61, 0).unwrap();
    assert_eq!(
        lines[0].text,
        "return switch (switch (var0) { case 7 -> 2; default -> 3; }) { case 7 -> 2; default -> 3; };"
    );
}

#[test]
fn retains_arm_work_before_the_yield() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([0x05, 0xa7, 0, 8, 0xb8, 0, 9, 0x57, 0x06, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert_eq!(
        lines[0].text,
        "return switch (var0) { case 7 -> 2; default -> { Example.side(); yield 3; } };"
    );
}

#[test]
fn keeps_a_loop_owned_by_one_rule() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([
        0x05, 0xa7, 0, 16, 0x03, 0x3c, 0x1b, 0x9c, 0, 9, 0x84, 1, 1, 0xa7, 0xff, 0xf9, 0x06, 0xac,
    ]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(lines[0].text.starts_with("return switch "));
    assert!(lines[0].text.contains("while ("));
    assert!(lines[0].text.contains("yield 3;"));
}

#[test]
fn joins_a_single_category_two_value() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 4, &[(7, 0)]);
    bytes.extend([0x09, 0xa7, 0, 4, 0x0a, 0xad]);
    let lines = lift(&bytes, "(I)J", 60, 0).unwrap();
    assert_eq!(
        lines[0].text,
        "return switch (var0) { case 7 -> 0L; default -> 1L; };"
    );
}

#[test]
fn preserves_statement_form_before_vineflowers_java16_gate() {
    let bytes = int_switch(&[0x1a], &[0xac]);
    for (major, minor) in [(52, 0), (56, u16::MAX), (57, u16::MAX), (58, 0), (59, 0)] {
        let lines = lift(&bytes, "(I)I", major, minor).unwrap();
        assert!(lines.iter().any(|line| line.text == "switch (var0) {"));
        assert!(lines.iter().all(|line| !line.text.contains(" -> ")));
    }
    let preview = lift(&bytes, "(I)I", 60, u16::MAX).unwrap();
    assert!(preview[0].text.starts_with("return switch "));
}

#[test]
fn falls_back_when_an_arm_uses_the_dispatch_stack_prefix() {
    let mut bytes = vec![0x04, 0x1a];
    lookup(&mut bytes, 5, &[(7, 0)]);
    bytes.extend([0x05, 0x60, 0xa7, 0, 5, 0x06, 0x60, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(lines.iter().any(|line| line.text == "switch (var0) {"));
    assert!(lines.iter().all(|line| !line.text.contains(" -> ")));
}

#[test]
fn does_not_move_a_method_return_into_a_switch_rule() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 6, &[(7, 0), (8, 2)]);
    bytes.extend([0x04, 0xac, 0x05, 0xa7, 0, 4, 0x06, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(lines.iter().any(|line| line.text == "return 1;"));
    assert!(lines.iter().all(|line| !line.text.contains(" -> ")));
}

#[test]
fn keeps_local_declarations_outside_when_the_join_reads_them() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 6, &[(7, 0)]);
    bytes.extend([
        0x06, 0x3c, 0x05, 0xa7, 0, 6, 0x07, 0x3c, 0x08, 0x1b, 0x60, 0xac,
    ]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(lines.iter().any(|line| line.text == "switch (var0) {"));
    assert!(lines.iter().all(|line| !line.text.contains(" -> ")));
    assert!(lines.iter().any(|line| line.text == "int var1_2;"));
}

#[test]
fn does_not_fold_two_joined_operands_into_one_value() {
    let mut bytes = vec![0x1a];
    lookup(&mut bytes, 5, &[(7, 0)]);
    bytes.extend([0x05, 0x06, 0xa7, 0, 5, 0x07, 0x08, 0x60, 0xac]);
    let lines = lift(&bytes, "(I)I", 60, 0).unwrap();
    assert!(lines.iter().any(|line| line.text == "switch (var0) {"));
    assert!(lines.iter().all(|line| !line.text.contains(" -> ")));
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
