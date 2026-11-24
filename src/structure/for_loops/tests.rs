// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    lift::Machine,
    options::Options,
    structure::{Line, structure},
};

// #9 calls Example.side(I)V. #15, #21 and #25 are the enhanced-for
// protocol methods on List and Iterator, and #27 is java/lang/String.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x1c\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x04(I)V\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \x01\0\x0ejava/util/List\x07\0\x0a\x01\0\x08iterator\x01\0\x16()Ljava/util/Iterator;\
    \x0c\0\x0c\0\x0d\x0b\0\x0b\0\x0e\
    \x01\0\x12java/util/Iterator\x07\0\x10\x01\0\x07hasNext\x01\0\x03()Z\
    \x0c\0\x12\0\x13\x0b\0\x11\0\x14\
    \x01\0\x04next\x01\0\x14()Ljava/lang/Object;\x0c\0\x16\0\x17\x0b\0\x11\0\x18\
    \x01\0\x10java/lang/String\x07\0\x1a\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn lift(bytes: &[u8], signature: &str) -> Vec<Line> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
    let code = Code {
        max_stack: 8,
        max_locals: 8,
        bytes,
        exceptions: vec![],
        attributes: vec![],
    };
    let descriptor = MethodDescriptor::parse(signature).unwrap();
    let options = Options::default();
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let machine = Machine::new(&class, &method, &code, &descriptor, &options, &|name| {
        name.rsplit('/').next().unwrap().into()
    })
    .unwrap();
    structure(&instructions, &graph, machine).unwrap()
}

#[test]
fn moves_unique_initializer_and_iinc_into_the_counted_header() {
    let lines = lift(
        &[
            0x03, 0x3c, 0x1b, 0x1a, 0xa2, 0, 13, 0x1b, 0xb8, 0, 9, 0x84, 1, 1, 0xa7, 0xff, 0xf4,
            0xb1,
        ],
        "(I)V",
    );
    assert_eq!(lines[0].text, "for (int var1 = 0; var1 < var0; var1++) {");
    assert_eq!(lines[0].offsets, [0, 1, 2, 3, 4, 5, 6, 11, 12, 13]);
    assert_eq!(lines[1].text, "Example.side(var1);");
    assert_eq!(lines[1].offsets, [7, 8, 9, 10]);
}

#[test]
fn continues_share_one_update_and_keep_the_conditional_body() {
    let lines = lift(
        &[
            0x03, 0x3c, 0x1b, 0x1a, 0xa2, 0, 21, 0x1b, 0x04, 0xa0, 0, 6, 0xa7, 0, 7, 0x1b, 0xb8, 0,
            9, 0x84, 1, 1, 0xa7, 0xff, 0xec, 0xb1,
        ],
        "(I)V",
    );
    assert_eq!(lines[0].text, "for (int var1 = 0; var1 < var0; var1++) {");
    assert_eq!(lines[1].text, "if (var1 != 1) {");
    assert!(!lines.iter().any(|line| line.text == "} else {"));
    assert!(
        lines
            .iter()
            .any(|line| line.text == "Example.side(var1);" && line.depth > 1)
    );
    assert_eq!(
        lines
            .iter()
            .filter(|line| line.text.contains("var1++"))
            .count(),
        1
    );
}

#[test]
fn counter_used_after_exit_keeps_its_outer_declaration() {
    let lines = lift(
        &[
            0x03, 0x3c, 0x1b, 0x1a, 0xa2, 0, 13, 0x1b, 0xb8, 0, 9, 0x84, 1, 1, 0xa7, 0xff, 0xf4,
            0x1b, 0xac,
        ],
        "(I)I",
    );
    assert_eq!(lines[0].text, "int var1 = 0;");
    assert_eq!(lines[1].text, "while (var1 < var0) {");
    assert_eq!(lines.last().unwrap().text, "return var1;");
}

fn array_loop(step: u8) -> Vec<Line> {
    lift(
        &[
            0x2a, 0x4c, 0x2b, 0xbe, 0x3d, 0x03, 0x3e, 0x1d, 0x1c, 0xa2, 0, 19, 0x2b, 0x1d, 0x2e,
            0x36, 4, 0x15, 4, 0xb8, 0, 9, 0x84, 3, step, 0xa7, 0xff, 0xee, 0xb1,
        ],
        "([I)V",
    )
}

#[test]
fn array_foreach_eliminates_only_the_three_synthetic_locals() {
    let lines = array_loop(1);
    assert_eq!(lines[0].text, "for (int var4 : var0) {");
    assert_eq!(
        lines[0].offsets,
        [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 22, 23, 24
        ]
    );
    assert_eq!(lines[1].text, "Example.side(var4);");
}

#[test]
fn array_scan_with_a_stride_greater_than_one_remains_counted() {
    let lines = array_loop(2);
    assert_eq!(lines[0].text, "int[] var1 = var0;");
    assert!(
        lines
            .iter()
            .any(|line| line.text == "for (int var3 = 0; var3 < var2; var3 += 2) {")
    );
}

#[test]
fn iterator_foreach_keeps_the_per_element_checkcast() {
    let lines = lift(
        &[
            0x2a, 0xb9, 0, 15, 1, 0, 0x4c, 0x2b, 0xb9, 0, 21, 1, 0, 0x99, 0, 20, 0x2b, 0xb9, 0, 25,
            1, 0, 0xc0, 0, 27, 0x4d, 0x04, 0xb8, 0, 9, 0xa7, 0xff, 0xe9, 0xb1,
        ],
        "(Ljava/util/List;)V",
    );
    assert_eq!(
        lines[0].text,
        "for (String var2 : (Iterable<String>)(Iterable<?>)var0) {"
    );
    assert_eq!(lines[1].text, "Example.side(1);");
}
