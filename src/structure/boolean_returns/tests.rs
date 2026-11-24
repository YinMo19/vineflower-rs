use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    lift::Machine,
    options::Options,
    structure::structure,
};

use super::Line;

// Example extends Object; constant #9 is Example.side:()Z.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x0a\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()Z\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn lift(bytes: &[u8], descriptor: &str, simplify: bool) -> Vec<Line> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
    let code = Code {
        max_stack: 4,
        max_locals: 4,
        bytes,
        exceptions: vec![],
        attributes: vec![],
    };
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    let mut options = Options::default();
    options.set("ternary-constant-simplification", if simplify { "1" } else { "0" }).unwrap();
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let machine = Machine::new(&class, &method, &code, &descriptor, &options, &str::to_owned).unwrap();
    structure(&instructions, &graph, machine).unwrap()
}

#[test]
fn the_option_controls_simplification_of_a_boolean_stack_join() {
    let code = [0x1a, 0x99, 0, 7, 0x03, 0xa7, 0, 4, 0x1b, 0xac];
    let lines = lift(&code, "(ZZ)Z", false);
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "return var0 ? false : var1;");

    let lines = lift(&code, "(ZZ)Z", true);
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "return !var0 && var1;");
    assert_eq!(lines[0].offsets, [0, 1, 2, 3, 8, 9]);
}

#[test]
fn pairs_two_terminal_returns_and_preserves_operand_offsets() {
    let code = [0x1a, 0x99, 0, 5, 0x04, 0xac, 0x1b, 0xac];
    let lines = lift(&code, "(ZZ)Z", true);
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "return var0 || var1;");
    assert_eq!(lines[0].offsets, [0, 1, 2, 3, 6]);
}

#[test]
fn nests_boolean_arms_and_reuses_only_a_stable_condition() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 11, 0x1b, 0x99, 0, 5, 0x03, 0xac, 0x1c, 0xac, 0x1c, 0x99, 0, 5,
            0x1c, 0xac, 0x1b, 0xac,
        ],
        "(ZZZ)Z",
        true,
    );
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "return var0 ? !var1 && var2 : var2 || var1;");
    assert!(!lines[0].offsets.contains(&16)); // removed second load of var2
}

#[test]
fn never_reuses_a_side_effecting_condition() {
    let lines = lift(
        &[0xb8, 0, 9, 0x99, 0, 7, 0xb8, 0, 9, 0xac, 0x1a, 0xac],
        "(Z)Z",
        true,
    );
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text.matches("side()").count(), 2);
    assert!(lines[0].text.contains(" ? "));
}

#[test]
fn leaves_explicit_branch_local_stores_as_statements() {
    let lines = lift(
        &[0x1a, 0x99, 0, 8, 0x04, 0x3d, 0xa7, 0, 5, 0x1b, 0x3d, 0x1c, 0xac],
        "(ZZ)Z",
        true,
    );
    assert!(lines.iter().any(|line| line.text == "if (var0) {"));
    assert!(lines.iter().any(|line| line.text == "} else {"));
}
