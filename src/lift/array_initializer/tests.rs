use crate::{
    Options,
    bytecode::decode,
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Code, ExceptionHandler, Member},
    descriptor::MethodDescriptor,
    structure::structure_with_handlers,
};

use super::*;

// Example.side(int), Example(int[]), String, int[], Example.other:Object,
// plus varargs calls used to test the preserved allocation and selected overload.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x37\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()V\x01\0\x04side\x01\0\x04(I)I\x0c\0\x07\0\x08\x0a\0\x02\0\x09\
    \x01\0\x06<init>\x01\0\x05([I)V\x0c\0\x0b\0\x0c\x0a\0\x02\0\x0d\
    \x01\0\x10java/lang/String\x07\0\x0f\x01\0\x02[I\x07\0\x11\
    \x01\0\x05other\x01\0\x12Ljava/lang/Object;\x0c\0\x13\0\x14\x09\0\x02\0\x15\
    \x01\0\x04take\x0c\0\x17\0\x0c\x0a\0\x02\0\x18\x01\0\x04(I)V\
    \x01\0\x06choose\x0c\0\x1b\0\x0c\x0a\0\x02\0\x1c\x01\0\x16(Ljava/lang/Integer;)V\
    \x01\0\x09ambiguous\x0c\0\x1f\0\x0c\x0a\0\x02\0\x20\x01\0\x17([Ljava/lang/Integer;)V\
    \x01\0\x07collect\x01\0\x06(I[I)V\x0c\0\x23\0\x24\x0a\0\x02\0\x25\
    \x01\0\x04refs\x01\0\x16([Ljava/lang/Object;)V\x0c\0\x27\0\x28\x0a\0\x02\0\x29\
    \x01\0\x06narrow\x01\0\x05([B)V\x0c\0\x2b\0\x2c\x0a\0\x02\0\x2d\
    \x01\0\x03tie\x0c\0\x2f\0\x0c\x0a\0\x02\0\x30\x01\0\x06(I[D)V\
    \x01\0\x08specific\x0c\0\x33\0\x0c\x0a\0\x02\0\x34\x01\0\x06(J[F)V\
    \0\x21\0\x02\0\x04\0\0\0\0\0\x0d\
    \0\x89\0\x17\0\x0c\0\0\0\x09\0\x17\0\x1a\0\0\
    \0\x89\0\x1b\0\x0c\0\0\0\x09\0\x1b\0\x1e\0\0\
    \0\x89\0\x1f\0\x0c\0\0\0\x89\0\x1f\0\x22\0\0\
    \0\x89\0\x23\0\x24\0\0\0\x89\0\x27\0\x28\0\0\
    \0\x89\0\x2b\0\x2c\0\0\
    \0\x89\0\x2f\0\x0c\0\0\0\x89\0\x2f\0\x32\0\0\
    \0\x89\0\x33\0\x0c\0\0\0\x89\0\x33\0\x36\0\0\
    \0\0";

fn with_machine(
    bytes: &[u8],
    descriptor: &str,
    constructor: bool,
    test: impl FnOnce(Machine<'_, '_>),
) {
    with_method(bytes, descriptor, constructor, Vec::new(), Options::default(), test);
}

fn with_method(
    bytes: &[u8],
    descriptor: &str,
    constructor: bool,
    exceptions: Vec<ExceptionHandler>,
    options: Options,
    test: impl FnOnce(Machine<'_, '_>),
) {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: if constructor { 0 } else { 8 },
        name_index: if constructor { 11 } else { 5 },
        descriptor_index: 6,
        attributes: Vec::new(),
    };
    let code = Code {
        max_stack: 16,
        max_locals: 4,
        bytes,
        exceptions,
        attributes: Vec::new(),
    };
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    test(
        Machine::new(&class, &method, &code, &descriptor, &options, &|name| {
            name.rsplit('/').next().unwrap().into()
        })
        .unwrap(),
    );
}

#[test]
fn effectful_elements_execute_once_in_bytecode_order_with_offsets() {
    let bytes = [
        0x05, 0xbc, 10, 0x59, 0x03, 0x04, 0xb8, 0, 10, 0x4f, 0x59, 0x04, 0x05, 0xb8, 0, 10, 0x4f,
        0xb0,
    ];
    with_machine(&bytes, "()[I", false, |machine| {
        let instructions = decode(&bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines.len(), 1);
        assert_eq!(
            lines[0].text,
            "return new int[]{Example.side(1), Example.side(2)};"
        );
        assert_eq!(
            lines[0].offsets,
            (0..bytes.len() as u32).collect::<Vec<_>>()
        );
    });
}

const LOCAL_RETURN: &[u8] = &[
    0x05, 0xbc, 10, 0x4c, // int[] temp = new int[2];
    0x2b, 0x03, 0x04, 0xb8, 0, 10, 0x4f, // temp[0] = Example.side(1);
    0x2b, 0x04, 0x05, 0xb8, 0, 10, 0x4f, // temp[1] = Example.side(2);
    0x2b, 0xb0, // return temp;
];

#[test]
fn return_temporary_preserves_element_evaluation_order_and_anchors() {
    let options = Options { include_line_mappings: true, ..Options::default() };
    with_method(LOCAL_RETURN, "()[I", false, Vec::new(), options, |mut machine| {
        let instructions = decode(LOCAL_RETURN).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        // Unlike dup initializers, the allocation itself is not on the
        // operand stack while evaluating an element.
        machine.max_stack = 3;
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines.len(), 1);
        assert_eq!(lines[0].offsets, (0..LOCAL_RETURN.len() as u32).collect::<Vec<_>>());
        let mut out = String::new();
        let mut anchors = Vec::new();
        lines[0].text.render_at(&mut out, 24, "  ", false, 0, |range, line| {
            anchors.push((range, line));
        });
        assert_eq!(out, "return new int[]{\n  Example.side(1),\n  Example.side(2)\n};");
        assert_eq!(anchors, [(7..10, 1), (14..17, 2)]);
    });
}

#[test]
fn rejects_an_observable_temporary_or_nonterminal_transport() {
    let cases: &[(&[u8], &str)] = &[
        // An element reads the partially constructed array.
        (&[0x04, 0xbc, 10, 0x4c, 0x2b, 0x03, 0x2b, 0xbe, 0x4f, 0x2b, 0xb0], "(I[I)[I"),
        // The temporary is published as a second local alias or overwritten.
        (&[0x04, 0xbc, 10, 0x4c, 0x2b, 0x4d, 0x2b, 0x03, 0x04, 0x4f, 0x2b, 0xb0], "()[I"),
        (&[0x04, 0xbc, 10, 0x4c, 0x01, 0x4c, 0x2b, 0x03, 0x04, 0x4f, 0x2b, 0xb0], "()[I"),
        // Nested initializers are also forbidden to read the transported slot.
        (&[0x04, 0xbd, 0, 18, 0x4c, 0x2b, 0x03, 0x04, 0xbc, 10, 0x59, 0x03,
            0x2b, 0xbe, 0x4f, 0x53, 0x2b, 0xb0], "(I[[I)[[I"),
        // The stores must proceed in source initializer order.
        (&[0x05, 0xbc, 10, 0x4c, 0x2b, 0x04, 0x04, 0x4f, 0x2b, 0x03, 0x05, 0x4f,
            0x2b, 0xb0], "()[I"),
        // This is not an immediate return of the temporary.
        (&[0x04, 0xbc, 10, 0x4c, 0x2b, 0x03, 0x04, 0x4f, 0x2b, 0x00, 0xb0], "()[I"),
    ];
    for &(bytes, desc) in cases {
        with_machine(bytes, desc, false, |mut machine| {
            let instructions = decode(bytes).unwrap();
            machine.step(&instructions[0]).unwrap();
            let original = machine.stack[0].text.clone();
            assert!(machine.try_array_initializer(&instructions[1..], |_, _| true).is_none(), "{bytes:?}");
            assert_eq!(machine.stack[0].text, original);
            assert_eq!(machine.stack_slots, 1);
            assert!(machine.take_prelude().is_empty());
        });
    }
}

#[test]
fn return_temporary_cannot_span_an_exception_handler() {
    let mut bytes = LOCAL_RETURN.to_vec();
    // The handler can read the array after assignment, if the second RHS throws.
    bytes.extend([0x57, 0x2b, 0xb0]);
    let handlers = vec![ExceptionHandler { start_pc: 11, end_pc: 18, handler_pc: 20, catch_type: 0 }];
    with_method(&bytes, "()[I", false, handlers, Options::default(), |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        let candidate = &instructions[1..instructions.len() - 3];
        assert!(machine.try_array_initializer(candidate, |_, _| true).is_none());
        assert_eq!(machine.stack[0].text, "2");
    });
}

#[test]
fn constructor_arguments_do_not_spill_open_allocations_or_uninitialized_this() {
    let allocation = [
        0xbb, 0, 2, 0x59, 0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb7, 0, 14, 0xb0,
    ];
    with_machine(&allocation, "()LExample;", false, |machine| {
        let instructions = decode(&allocation).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines.len(), 1);
        assert_eq!(lines[0].text, "return new Example(new int[]{1});");
    });

    let delegate = [
        0x2a, 0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb7, 0, 14, 0xb1,
    ];
    with_machine(&delegate, "()V", true, |machine| {
        let instructions = decode(&delegate).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0].text, "this(new int[]{1});");
    });
}

#[test]
fn constructor_array_initializer_needs_an_unchanged_prefix_in_both_arms() {
    let mut bytes = [
        0xbb, 0, 2, 0x59,       // new Example; dup
        0x04, 0xbc, 10, 0x59,   // new int[1]; dup
        0x03, 0x1a, 0x99, 0, 7, // index 0; branch on the parameter
        0x04, 0xa7, 0, 4, 0x05, // 1 or 2
        0x4f, 0xb7, 0, 14, 0xb0,
    ];
    with_machine(&bytes, "(Z)LExample;", false, |machine| {
        let instructions = decode(&bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines.len(), 1);
        let text = lines[0].text.as_str();
        assert!(text.starts_with("return new Example(new int[]{"), "{text}");
        assert!(text.ends_with(" ? 1 : 2});"), "{text}");
    });

    // A branch that consumes the saved index instead of supplying an element
    // may not be turned into a conditional over the original stack prefix.
    bytes[13] = 0x57;
    with_machine(&bytes, "(Z)LExample;", false, |machine| {
        let instructions = decode(&bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        assert!(structure_with_handlers(&instructions, &graph, machine, &[]).is_err());
    });
}

#[test]
fn primitive_elements_use_jvm_narrowing_and_nested_references_use_array_types() {
    let bytes = [0x04, 0xbc, 8, 0x59, 0x03, 0x11, 0, 255, 0x54];
    with_machine(&bytes, "()V", false, |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        assert_eq!(
            machine.try_array_initializer(&instructions[1..], |_, _| true),
            Some(5)
        );
        assert_eq!(machine.stack[0].text, "new byte[]{-1}");
    });

    let bytes = [
        0x05, 0xbc, 4, 0x59, 0x03, 0x05, 0x54, 0x59, 0x04, 0x06, 0x54,
    ];
    with_machine(&bytes, "()V", false, |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        assert_eq!(
            machine.try_array_initializer(&instructions[1..], |_, _| true),
            Some(9)
        );
        assert_eq!(machine.stack[0].text, "new boolean[]{false, true}");
    });

    let bytes = [
        0x05, 0xbd, 0, 18, 0x59, 0x03, 0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0x53, 0x59, 0x04,
        0x01, 0x53,
    ];
    with_machine(&bytes, "()V", false, |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        assert_eq!(
            machine.try_array_initializer(&instructions[1..], |_, _| true),
            Some(instructions.len() - 1)
        );
        assert_eq!(machine.stack[0].text, "new int[][]{new int[]{1}, null}");
    });
}

#[test]
fn malformed_candidate_shapes_do_not_consume_operands() {
    for bytes in [
        // Incomplete and out of bounds.
        &[0x05, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f][..],
        &[
            0x05, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0x59, 0x05, 0x04, 0x4f,
        ],
        // A second write to the same slot and an out-of-order pair.
        &[
            0x05, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0x59, 0x03, 0x05, 0x4f,
        ],
        &[
            0x05, 0xbc, 10, 0x59, 0x04, 0x05, 0x4f, 0x59, 0x03, 0x04, 0x4f,
        ],
        // The RHS reads the very array being initialized via dup2.
        &[0x04, 0xbc, 10, 0x59, 0x03, 0x5c, 0x2e, 0x4f],
        // A field write in value evaluation is not an array initializer.
        &[0x04, 0xbc, 10, 0x59, 0x03, 0x01, 0xb3, 0, 22, 0x04, 0x4f],
        // Even a well-typed value cannot consume the surrounding stack.
        &[0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x60, 0x4f],
    ] {
        with_machine(bytes, "()V", false, |mut machine| {
            let instructions = decode(bytes).unwrap();
            machine.step(&instructions[0]).unwrap();
            let original = machine.stack[0].text.clone();
            assert!(
                machine
                    .try_array_initializer(&instructions[1..], |_, _| true)
                    .is_none(),
                "{bytes:?}"
            );
            assert_eq!(machine.stack_slots, 1);
            assert_eq!(machine.stack[0].text, original);
            assert!(machine.take_prelude().is_empty());
        });
    }
}

#[test]
fn a_runtime_array_store_check_is_not_replaced_by_a_value_cast() {
    let bytes = [0x04, 0xbd, 0, 16, 0x59, 0x03, 0xb2, 0, 22, 0x53];
    with_machine(&bytes, "()V", false, |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        assert!(
            machine
                .try_array_initializer(&instructions[1..], |_, _| true)
                .is_none()
        );
        assert_eq!(machine.offset, 0);
        assert_eq!(machine.stack_slots, 1);
        assert_eq!(machine.stack[0].text, "1");
        for op in &instructions[1..instructions.len() - 1] {
            machine.step(op).unwrap();
        }
        assert!(
            matches!(machine.step(instructions.last().unwrap()).unwrap(), Effect::Statement(text)
            if text == "((Object[])stack4)[0] = Example.other;")
        );
    });
}

#[test]
fn the_selected_region_must_include_every_part_of_the_initializer() {
    let bytes = [0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f];
    with_machine(&bytes, "()V", false, |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        assert!(
            machine
                .try_array_initializer(&instructions[1..], |index, _| index != 3)
                .is_none()
        );
        assert_eq!(machine.stack[0].text, "1");
    });
}

#[test]
fn masking_operands_does_not_relax_the_verified_stack_limit() {
    let bytes = [0x09, 0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f];
    with_machine(&bytes, "()V", false, |mut machine| {
        let instructions = decode(&bytes).unwrap();
        machine.step(&instructions[0]).unwrap();
        machine.step(&instructions[1]).unwrap();
        machine.max_stack = 5;
        assert!(
            machine
                .try_array_initializer(&instructions[2..], |_, _| true)
                .is_none()
        );
        assert_eq!(machine.stack_slots, 3);
        assert_eq!(machine.stack[0].text, "0L");
        assert_eq!(machine.stack[1].text, "1");

        machine.max_stack = 6;
        assert_eq!(
            machine.try_array_initializer(&instructions[2..], |_, _| true),
            Some(5)
        );
        assert_eq!(machine.stack_slots, 3);
        assert_eq!(machine.stack[0].text, "0L");
        assert_eq!(machine.stack[1].text, "new int[]{1}");
    });
}

#[test]
fn varargs_packing_keeps_fixed_arguments_and_elements_in_evaluation_order() {
    let bytes = [
        0x04, 0xb8, 0, 10, // fixed argument
        0x05, 0xbc, 10,
        0x59, 0x03, 0x05, 0xb8, 0, 10, 0x4f, // first element
        0x59, 0x04, 0x06, 0xb8, 0, 10, 0x4f, // second element
        0xb8, 0, 38, 0xb1,
    ];
    with_machine(&bytes, "()V", false, |machine| {
        let instructions = decode(&bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines[0].text, "collect(Example.side(1), Example.side(2), Example.side(3));");
        assert_eq!(lines[0].offsets, (0..24).collect::<Vec<_>>());
    });
}

#[test]
fn varargs_unpacks_only_when_overload_resolution_still_packs_the_same_array() {
    let bytes = [
        // A competing fixed strict, fixed loose, and variable-arity method.
        0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb8, 0, 25,
        0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb8, 0, 29,
        0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb8, 0, 33,
        // A fixed invocation of the same declaration would pass a null array,
        // not an array with one null element.
        0x04, 0xbd, 0, 4, 0x59, 0x03, 0x01, 0x53, 0xb8, 0, 42,
        // A local array and an explicitly null array have no fresh allocation.
        0x2a, 0xb8, 0, 42,
        0x01, 0xb8, 0, 42,
        // Unlike array assignment, invocation needs a cast for byte literals.
        0x04, 0xbc, 8, 0x59, 0x03, 0x11, 0, 255, 0x54, 0xb8, 0, 46,
        0xb1,
    ];
    with_machine(&bytes, "([Ljava/lang/Object;)V", false, |machine| {
        let instructions = decode(&bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        let expected = [
            "take(new int[]{1});",
            "choose(new int[]{1});",
            "ambiguous(new int[]{1});",
            "refs(new Object[]{null});",
            "refs(var0);",
            "refs((Object[])null);",
            "narrow((byte)-1);",
        ];
        assert!(lines.len() >= expected.len());
        for (line, expected) in lines.iter().zip(expected) {
            assert_eq!(line.text, expected);
        }
    });
}

#[test]
fn varargs_specificity_compares_the_fixed_formal_and_unused_tail() {
    let bytes = [
        // int... versus (int, double...) and (long, float...), respectively.
        0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb8, 0, 49,
        0x04, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0xb8, 0, 53,
        0xb1,
    ];
    with_machine(&bytes, "()V", false, |machine| {
        let instructions = decode(&bytes).unwrap();
        let graph = ControlFlowGraph::build(&instructions, &[]).unwrap();
        let lines = structure_with_handlers(&instructions, &graph, machine, &[]).unwrap();
        assert_eq!(lines[0].text, "tie(new int[]{1});");
        assert_eq!(lines[1].text, "specific(1);");
    });
}
