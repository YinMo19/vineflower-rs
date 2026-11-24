// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::{
    bytecode::decode,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    options::Options,
};

use super::*;

// Example extends Object; constant #9 is Example.side:()I.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x0a\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()I\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn lift(bytes: &[u8], signature: &str) -> Result<Vec<Line>, StructureError> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
    let code = Code {
        max_stack: 8,
        max_locals: 4,
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

#[test]
fn carries_preceding_evaluation_through_a_ternary_in_order() {
    let lines = lift(
        &[
            0xb8, 0, 9, 0x1a, 0x99, 0, 9, 0xb8, 0, 9, 0xa7, 0, 4, 0x05, 0x60, 0xac,
        ],
        "(Z)I",
    )
    .unwrap();
    assert_eq!(lines.len(), 1);
    assert_eq!(
        lines[0].text,
        "return Example.side() + (var0 ? Example.side() : 2);"
    );
    assert_eq!(lines[0].offsets, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15]);
}

#[test]
fn joins_category_two_values_as_one_expression() {
    let lines = lift(&[0x1a, 0x99, 0, 7, 0x0a, 0xa7, 0, 4, 0x09, 0xad], "(Z)J").unwrap();
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "return var0 ? 1L : 0L;");
}

#[test]
fn factors_short_circuit_control_with_one_shared_arm() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 11, 0x1b, 0x99, 0, 7, 0x04, 0xa7, 0, 4, 0x03, 0xac,
        ],
        "(ZZ)Z",
    )
    .unwrap();
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "return var0 && var1;");
}

#[test]
fn multiple_stack_values_share_one_condition() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 8, 0x05, 0x06, 0xa7, 0, 5, 0x07, 0x08, 0x68, 0xac,
        ],
        "(Z)I",
    )
    .unwrap();
    let lines = lines
        .iter()
        .map(|line| line.text.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        lines,
        [
            "int stack11;",
            "int stack11_1;",
            "if (var0) {",
            "stack11 = 2;",
            "stack11_1 = 3;",
            "} else {",
            "stack11 = 4;",
            "stack11_1 = 5;",
            "}",
            "return stack11 * stack11_1;",
        ]
    );
}

#[test]
fn declares_new_live_bindings_outside_both_arms() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 8, 0x06, 0x3c, 0xa7, 0, 5, 0x05, 0x3c, 0x1b, 0xac,
        ],
        "(Z)I",
    )
    .unwrap();
    let declaration = &lines[0];
    let name = declaration
        .text
        .strip_prefix("int ")
        .unwrap()
        .strip_suffix(';')
        .unwrap();
    assert_eq!(declaration.depth, 0);
    assert_eq!(lines.last().unwrap().text, format!("return {name};"));
    let copies = lines
        .iter()
        .filter(|line| line.text.starts_with(&format!("{name} = ")))
        .collect::<Vec<_>>();
    assert_eq!(copies.len(), 2);
    assert!(copies.iter().all(|line| line.depth == 1));
}

#[test]
fn rejects_incompatible_join_categories() {
    let result = lift(
        &[0x1a, 0x99, 0, 7, 0x04, 0xa7, 0, 4, 0x09, 0x58, 0xb1],
        "(Z)V",
    );
    assert!(matches!(
        result,
        Err(StructureError::Lift(LiftError::InvalidStack { .. }))
    ));
}

#[test]
fn switch_arms_definitely_assign_the_shared_local() {
    let lines = lift(
        &[
            0x1a, 0xab, 0, 0, 0, 0, 0, 24, 0, 0, 0, 1, 0, 0, 0, 7, 0, 0, 0, 19, 0x05, 0x3c, 0xa7,
            0, 5, 0x06, 0x3c, 0x1b, 0xac,
        ],
        "(I)I",
    )
    .unwrap();
    let name = lines[0]
        .text
        .strip_prefix("int ")
        .unwrap()
        .strip_suffix(';')
        .unwrap();
    assert_eq!(lines[1].text, "switch (var0) {");
    assert_eq!(lines.last().unwrap().text, format!("return {name};"));
    assert!(
        lines
            .iter()
            .any(|line| line.text == format!("{name} = 2;") && line.depth == 2)
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text == format!("{name} = 3;") && line.depth == 2)
    );
}

#[test]
fn loop_carries_a_stack_operand_through_its_backedge() {
    let lines = lift(
        &[0x03, 0x1a, 0x99, 0, 8, 0x04, 0x60, 0xa7, 0xff, 0xfa, 0xac],
        "(Z)I",
    )
    .unwrap();
    assert_eq!(
        lines
            .iter()
            .map(|line| line.text.as_str())
            .collect::<Vec<_>>(),
        [
            "int stack1 = 0;",
            "while (var0) {",
            "stack1 = stack1 + 1;",
            "}",
            "return stack1;",
        ]
    );
}

#[test]
fn loop_header_definition_can_reach_its_exit() {
    let lines = lift(
        &[
            0x1a, 0x3c, 0x1b, 0x99, 0, 9, 0x84, 0, 0xff, 0xa7, 0xff, 0xf7, 0x1b, 0xac,
        ],
        "(I)I",
    )
    .unwrap();
    let name = lines[0]
        .text
        .strip_prefix("int ")
        .unwrap()
        .strip_suffix(';')
        .unwrap();
    assert_eq!(lines[1].text, "while (true) {");
    let copy = lines
        .iter()
        .position(|line| line.text.starts_with(&format!("{name} = ")))
        .unwrap();
    assert_eq!(lines[copy + 1].text, "break;");
    assert_eq!(lines.last().unwrap().text, format!("return {name};"));
}

#[test]
fn freezes_a_loaded_value_before_an_arm_reassigns_its_local() {
    let lines = lift(
        &[
            0x1a, 0x1b, 0x99, 0, 9, 0x06, 0x3b, 0x05, 0xa7, 0, 4, 0x07, 0x60, 0xac,
        ],
        "(IZ)I",
    )
    .unwrap();
    assert_eq!(lines[0].text, "int stack2 = var0;");
    assert!(
        lines
            .iter()
            .any(|line| line.text == "var0 = 3;" && line.depth == 1)
    );
    assert_eq!(lines.last().unwrap().text, "return stack2 + stack12;");
}

#[test]
fn ternary_can_replace_an_incoming_top_operand() {
    let lines = lift(&[0x1a, 0x59, 0x9a, 0, 5, 0x57, 0x08, 0xac], "(I)I").unwrap();
    assert_eq!(lines[0].text, "int stack1 = var0;");
    assert_eq!(lines[1].text, "return stack1 == 0 ? 5 : stack1;");
    assert_eq!(lines[1].offsets, [2, 3, 4, 6, 7]);
}

#[test]
fn a_discarded_call_maps_only_the_physical_invocation() {
    let lines = lift(&[0xb8, 0, 9, 0x57, 0xb1], "()V").unwrap();
    assert_eq!(lines[0].text, "Example.side();");
    assert_eq!(lines[0].offsets, [0, 1, 2]);
}

#[test]
fn boolean_composition_keeps_operand_anchors() {
    let mut right = Document::new();
    right.anchor(11..13);
    right.push_str("second");
    let condition = logical(Document::from("first"), "&&", right);
    let statement = surrounded(condition, "if (", ") {");
    let mut output = String::new();
    let mut mapped = Vec::new();
    statement.render_at(&mut output, 80, "  ", false, 0, |range, line| {
        mapped.push((range, line));
    });
    assert_eq!(output, "if (first && second) {");
    assert_eq!(mapped, [(11..13, 0)]);
}

#[test]
fn switch_fallthrough_can_update_the_dispatch_stack_binding() {
    let lines = lift(
        &[
            0x04, 0x1a, 0xab, 0, 0, 0, 0, 33, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 26, 0, 0, 0, 2, 0,
            0, 0, 28, 0x04, 0x60, 0x05, 0x68, 0xa7, 0, 4, 0x00, 0xac,
        ],
        "(I)I",
    )
    .unwrap();
    let case_two = lines
        .iter()
        .position(|line| line.text == "case 2:")
        .unwrap();
    assert_eq!(lines[0].text, "int stack0 = 1;");
    assert!(
        lines[..case_two]
            .iter()
            .any(|line| line.text == "stack0 = stack0 + 1;")
    );
    assert!(!lines[..case_two].iter().any(|line| line.text == "break;"));
    assert!(
        lines[case_two..]
            .iter()
            .any(|line| line.text == "stack36 = stack0 * 2;")
    );
    assert_eq!(lines.last().unwrap().text, "return stack36;");
}

#[test]
fn rejects_an_incoming_path_without_a_live_local_definition() {
    let result = lift(
        &[0x1a, 0x99, 0, 8, 0x04, 0x3c, 0xa7, 0, 4, 0x00, 0x1b, 0xac],
        "(Z)I",
    );
    assert!(matches!(
        result,
        Err(StructureError::Lift(LiftError::InvalidLocal {
            index: 1,
            ..
        }))
    ));
}

#[test]
fn recognizes_a_loop_without_a_normal_exit() {
    let lines = lift(&[0xb8, 0, 9, 0x57, 0xa7, 0xff, 0xfc], "()V").unwrap();
    assert_eq!(
        lines
            .iter()
            .map(|line| line.text.as_str())
            .collect::<Vec<_>>(),
        ["while (true) {", "Example.side();", "}"]
    );
}

#[test]
fn loop_breaks_merge_their_distinct_stack_payloads() {
    let lines = lift(
        &[
            0x03, 0x1a, 0x99, 0, 15, 0x1b, 0x99, 0, 8, 0x57, 0x04, 0xa7, 0, 6, 0xa7, 0xff, 0xf3,
            0xac,
        ],
        "(ZZ)I",
    )
    .unwrap();
    assert_eq!(lines[0].text, "int stack1 = 0;");
    assert_eq!(lines[1].text, "int stack17;");
    assert_eq!(lines[2].text, "while (true) {");
    assert!(
        lines
            .windows(2)
            .any(|pair| pair[0].text == "stack17 = stack1;" && pair[1].text == "break;")
    );
    assert!(
        lines
            .windows(2)
            .any(|pair| pair[0].text == "stack17 = 1;" && pair[1].text == "break;")
    );
    assert_eq!(lines.last().unwrap().text, "return stack17;");
}

#[test]
fn nested_loop_can_transfer_to_the_outer_loop() {
    for (jump, transfer) in [
        ([0xff, 0xf4], "continue label0;"),
        ([0, 9], "break label0;"),
    ] {
        let lines = lift(
            &[
                0x1a, 0x99, 0, 20, 0x1b, 0x99, 0, 13, 0x1c, 0x99, 0, 6, 0xa7, jump[0], jump[1],
                0xa7, 0xff, 0xf5, 0xa7, 0xff, 0xee, 0xb1,
            ],
            "(ZZZ)V",
        )
        .unwrap();
        assert_eq!(lines[0].text, "label0: while (var0) {");
        assert!(
            lines
                .iter()
                .any(|line| line.text == transfer && line.depth > 1)
        );
    }
}

#[test]
fn a_larger_sibling_loop_does_not_claim_the_first_loops_exit() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 6, 0xa7, 0xff, 0xfc, 0x1b, 0x99, 0, 13, 0x1b, 0x99, 0, 6, 0xa7, 0xff,
            0xf8, 0xa7, 0xff, 0xf5, 0xb1,
        ],
        "(ZZ)V",
    )
    .unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text == "while (var0) {" && line.depth == 0)
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text == "while (var1) {" && line.depth == 0)
    );
}
