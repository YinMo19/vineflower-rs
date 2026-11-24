use crate::{
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, Member},
    descriptor::MethodDescriptor,
    options::Options,
    structure::{Line, structure_with_handlers},
};

use super::*;

// Example.x:I #9, Example.y:I #12, Example.<init>(I)V #16.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x1d\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x01x\x01\0\x01I\x0c\0\x06\0\x07\x09\0\x02\0\x08\
    \x01\0\x01y\x0c\0\x0a\0\x07\x09\0\x02\0\x0b\
    \x01\0\x06<init>\x01\0\x04(I)V\x0c\0\x0d\0\x0e\x0a\0\x02\0\x0f\
    \x01\0\x04next\x01\0\x0b()LExample;\x0c\0\x11\0\x12\x0a\0\x02\0\x13\
    \x01\0\x05index\x01\0\x03()I\x0c\0\x15\0\x16\x0a\0\x02\0\x17\
    \x01\0\x08getArray\x01\0\x04()[I\x0c\0\x19\0\x1a\x0a\0\x02\0\x1b\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn with_machine<T>(bytes: &[u8], descriptor: &str, is_static: bool, test: impl FnOnce(Machine<'_, '_>) -> T) -> T {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: if is_static { 8 } else { 0 },
        name_index: 5,
        descriptor_index: 14,
        attributes: Vec::new(),
    };
    let code = Code {
        max_stack: 16, max_locals: 8, bytes,
        exceptions: Vec::new(), attributes: Vec::new(),
    };
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    let options = Options::default();
    test(Machine::new(&class, &method, &code, &descriptor, &options, &str::to_owned).unwrap())
}

fn lift(bytes: &[u8], descriptor: &str, is_static: bool) -> Vec<Line> {
    with_machine(bytes, descriptor, is_static, |machine| {
        let instructions = decode(bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        structure_with_handlers(&instructions, &graph, machine, &[]).unwrap()
    })
}

fn texts(lines: &[Line]) -> Vec<&str> {
    lines.iter().map(|line| line.text.as_str()).collect()
}

#[test]
fn blank_local_declaration_does_not_move_the_store_before_an_open_constructor() {
    let bytes = [0xbb, 0, 2, 0x59, 0x1a, 0x59, 0x3c, 0xb7, 0, 16, 0xb0];
    let lines = lift(&bytes, "(I)LExample;", true);
    assert_eq!(texts(&lines), ["int var1;", "return new Example(var1 = var0);"]);
    assert!(lines[0].offsets.is_empty());
    assert!(lines[1].offsets.contains(&6));
}

#[test]
fn ordinary_typed_compound_stores_use_one_lvalue_access() {
    let lines = lift(&[0x1a, 0x1b, 0x60, 0x3b, 0x1a, 0xac], "(II)I", true);
    assert_eq!(texts(&lines), ["var0 += var1;", "return var0;"]);
    let lines = lift(&[0x1a, 0x04, 0x82, 0x3b, 0x1a, 0xac], "(Z)Z", true);
    assert_eq!(texts(&lines), ["var0 ^= true;", "return var0;"]);
}

#[test]
fn retained_long_operands_distinguish_prefix_and_postfix() {
    let postfix = lift(&[0x1e, 0x5c, 0x0a, 0x61, 0x3f, 0xad], "(J)J", true);
    assert_eq!(texts(&postfix), ["return var0++;"]);
    let prefix = lift(&[0x1e, 0x0a, 0x65, 0x5c, 0x3f, 0xad], "(J)J", true);
    assert_eq!(texts(&prefix), ["return --var0;"]);
}

#[test]
fn byte_postfix_requires_the_matching_narrowing_conversion() {
    let postfix = lift(&[0x1a, 0x1a, 0x04, 0x60, 0x91, 0x3b, 0xac], "(B)B", true);
    assert_eq!(texts(&postfix), ["return var0++;"]);
    let invalid = [0x1a, 0x04, 0x60, 0x93, 0x3b, 0xb1];
    with_machine(&invalid, "(B)V", true, |mut machine| {
        let ops = decode(&invalid).unwrap();
        machine.step(&ops[0]).unwrap();
        machine.step(&ops[1]).unwrap();
        assert!(machine.step_assignment(&ops[2..], |_, _| true).unwrap().is_none());
        assert_eq!(machine.stack.len(), 2);
    });
}

#[test]
fn field_postfix_can_be_a_constructor_argument_without_spills() {
    let bytes = [
        0xbb, 0, 2, 0x59, 0x2a, 0x59, 0xb4, 0, 9, 0x5a, 0x04, 0x60, 0xb5, 0, 9,
        0xb7, 0, 16, 0xb0,
    ];
    let lines = lift(&bytes, "()LExample;", false);
    assert_eq!(texts(&lines), ["return new Example(this.x++);"]);
}

#[test]
fn another_field_or_another_receiver_is_not_the_same_lvalue() {
    let fields = [0x2a, 0x2a, 0xb4, 0, 9, 0x04, 0x60, 0xb5, 0, 12, 0xb1];
    let lines = lift(&fields, "()V", false);
    assert_eq!(texts(&lines), ["this.y = this.x + 1;", "return;"]);
    let receivers = [0x2a, 0x2b, 0xb4, 0, 9, 0x04, 0x60, 0xb5, 0, 9, 0xb1];
    let lines = lift(&receivers, "(LExample;LExample;)V", true);
    assert_eq!(texts(&lines), ["var0.x = var1.x + 1;", "return;"]);
}

#[test]
fn an_array_update_requires_both_the_original_array_and_the_original_index() {
    let postfix = [0x2a, 0x1b, 0x5c, 0x2e, 0x5b, 0x04, 0x60, 0x4f, 0xac];
    let lines = lift(&postfix, "([II)I", true);
    assert_eq!(lines.len(), 3);
    assert!(lines[2].text.starts_with("return stack"));
    assert!(lines[2].text.ends_with("]++;"));
    let mismatch = [0x2a, 0x59, 0x03, 0x2e, 0x04, 0x5f, 0x04, 0x60, 0x4f, 0xb1];
    let lines = lift(&mismatch, "([I)V", true);
    assert!(lines[1].text.contains("[1] = stack1[0] + 1;"));
}

#[test]
fn omitted_store_or_noncontiguous_address_disables_recovery() {
    let bytes = [0x1a, 0x04, 0x60, 0x3b, 0xb1];
    with_machine(&bytes, "(I)V", true, |mut machine| {
        let mut ops = decode(&bytes).unwrap();
        machine.step(&ops[0]).unwrap();
        machine.step(&ops[1]).unwrap();
        assert!(machine.step_assignment(&ops[2..], |index, _| index != 1).unwrap().is_none());
        ops[3].offset += 1;
        assert!(machine.step_assignment(&ops[2..], |_, _| true).unwrap().is_none());
        assert!(machine.take_prelude().is_empty());
        assert_eq!(machine.stack.len(), 2);
    });
}

#[test]
fn receiver_and_index_effects_stay_single_and_ordered() {
    let field = [0xb8, 0, 20, 0x59, 0xb4, 0, 9, 0x5a, 0x04, 0x60, 0xb5, 0, 9, 0xac];
    let lines = lift(&field, "()I", true);
    assert_eq!(texts(&lines), ["Example stack3 = Example.next();", "return stack3.x++;"]);

    let independently_read = [0xb8, 0, 20, 0xb8, 0, 20, 0xb4, 0, 9, 0x04, 0x60, 0xb5, 0, 9, 0xb1];
    let lines = lift(&independently_read, "()V", true);
    assert_eq!(texts(&lines), ["Example.next().x = Example.next().x + 1;", "return;"]);

    let array = [0xb8, 0, 28, 0xb8, 0, 24, 0x5c, 0x2e, 0x5b, 0x04, 0x60, 0x4f, 0xac];
    let lines = lift(&array, "()I", true);
    assert_eq!(lines.len(), 3);
    assert!(lines[0].text.ends_with("= Example.getArray();"));
    assert!(lines[1].text.ends_with("= Example.index();"));
    assert!(lines[2].text.starts_with("return stack"));
    assert!(lines[2].text.ends_with("]++;"));
}

#[test]
fn rejected_inline_store_does_not_mutate_the_pending_constructor_arguments() {
    let bytes = [0xbb, 0, 2, 0x59, 0x1a, 0x59, 0x3c, 0xb7, 0, 16, 0xb0];
    with_machine(&bytes, "(I)LExample;", true, |mut machine| {
        let ops = decode(&bytes).unwrap();
        for op in &ops[..3] {
            machine.step(op).unwrap();
        }
        assert!(machine.step_assignment(&ops[3..], |index, _| index != 1).unwrap().is_none());
        assert_eq!(machine.stack.len(), 3);
        assert!(machine.stack[..2].iter().all(|value| matches!(value.source, Source::New(0))));
        assert!(machine.take_prelude().is_empty());
        let accepted = machine.step_assignment(&ops[3..], |_, _| true).unwrap().unwrap();
        assert_eq!(accepted.declaration.unwrap(), "int var1;");
        machine.step(&ops[5]).unwrap();
        assert_eq!(machine.stack[0].text, "new Example(var1 = var0)");
    });
}
