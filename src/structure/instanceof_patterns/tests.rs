use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    options::Options,
};

use super::super::{Line, structure};

// #8 = String, #10 = Integer.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3c\0\x0b\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()V\x01\0\x10java/lang/String\x07\0\x07\
    \x01\0\x11java/lang/Integer\x07\0\x09\0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn lift(bytes: &[u8], signature: &str) -> Vec<Line> {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: 8,
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
    let descriptor = MethodDescriptor::parse(signature).unwrap();
    let options = Options::default();
    let render = |name: &str| name.rsplit('/').next().unwrap().to_owned();
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
    let machine =
        super::Machine::new(&class, &method, &code, &descriptor, &options, &render).unwrap();
    structure(&instructions, &graph, machine).unwrap()
}

#[test]
fn inlines_an_unobserved_alias_and_keeps_the_binding_inside_a_ternary() {
    let lines = lift(
        &[
            0x2a, 0x4d, 0x2c, 0xc1, 0, 8, 0x99, 0, 12, 0x2c, 0xc0, 0, 8, 0x4c, 0x2b, 0xa7, 0, 4,
            0x01, 0xb0,
        ],
        "(Ljava/lang/Object;)Ljava/lang/String;",
    );
    assert_eq!(lines.len(), 1);
    assert_eq!(
        lines[0].text,
        "return var0 instanceof String var1 ? var1 : null;"
    );
    assert!(lines[0].offsets.contains(&13));
}

#[test]
fn introduces_a_negated_binding_after_an_abrupt_guard() {
    let lines = lift(
        &[
            0x2a, 0xc1, 0, 8, 0x9a, 0, 5, 0x01, 0xb0, 0x2a, 0xc0, 0, 8, 0x4c, 0x2b, 0xa7, 0, 3,
            0xb0,
        ],
        "(Ljava/lang/Object;)Ljava/lang/String;",
    );
    assert_eq!(lines[0].text, "if (!(var0 instanceof String var1)) {");
    assert_eq!(lines[1].depth, 1);
    assert_eq!(lines[2].text, "}");
    assert_eq!(lines[3].text, "return var1;");
    assert_eq!(lines[3].depth, 0);
}

#[test]
fn never_rebinds_an_existing_source_local() {
    let lines = lift(
        &[
            0x01, 0x4c, 0x2a, 0xc1, 0, 8, 0x99, 0, 11, 0x2a, 0xc0, 0, 8, 0x4c, 0x2b, 0x57, 0, 0x2b,
            0xb0,
        ],
        "(Ljava/lang/Object;)Ljava/lang/Object;",
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text == "if (var0 instanceof String) {")
    );
    assert!(lines.iter().any(|line| line.text == "var1 = (String)var0;"));
}

#[test]
fn requires_the_same_selector_and_cast_type() {
    for (load, cast) in [(0x2b, 8), (0x2a, 10)] {
        let lines = lift(
            &[
                0x2a, 0xc1, 0, 8, 0x99, 0, 12, load, 0xc0, 0, cast, 0x4d, 0x2c, 0xa7, 0, 4, 0x01,
                0xb0,
            ],
            "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
        );
        assert!(
            lines
                .iter()
                .any(|line| line.text == "if (var0 instanceof String) {")
        );
        assert!(lines.iter().any(|line| line.text.contains(" var2 = (")));
    }
}

#[test]
fn rejects_a_successor_that_can_skip_the_type_test() {
    let lines = lift(
        &[
            0x1a, 0x9a, 0, 10, 0x2b, 0xc1, 0, 8, 0x99, 0, 10, 0x2b, 0xc0, 0, 8, 0x4d, 0x2c, 0xb0,
            0x01, 0xb0,
        ],
        "(ZLjava/lang/Object;)Ljava/lang/String;",
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text.contains("instanceof String"))
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text == "String var2 = (String)var1;")
    );
}

#[test]
fn scopes_a_binding_to_the_guard_when_a_true_edge_can_bypass_it() {
    let lines = lift(
        &[
            0x1a, 0x9a, 0, 19, 0x2b, 0xc1, 0, 8, 0x99, 0, 16, 0x2b, 0xc0, 0, 8, 0x4d, 0x2c, 0xc6,
            0, 7, 0x04, 0xa7, 0, 4, 0x03, 0xac,
        ],
        "(ZLjava/lang/Object;)Z",
    );
    assert_eq!(lines.len(), 1);
    assert_eq!(
        lines[0].text,
        "return var0 || var1 instanceof String var2 && var2 != null;"
    );
}

#[test]
fn keeps_a_pattern_in_a_compound_loop_test() {
    let lines = lift(
        &[
            0x2a, 0xc1, 0, 8, 0x99, 0, 17, 0x2a, 0xc0, 0, 8, 0x4c, 0x2b, 0xc6, 0, 8, 0x2b, 0x4b,
            0xa7, 0xff, 0xee, 0xb1,
        ],
        "(Ljava/lang/Object;)V",
    );
    assert_eq!(
        lines[0].text,
        "while (var0 instanceof String var1 && var1 != null) {"
    );
    assert_eq!(lines[1].text, "var0 = var1;");
}
