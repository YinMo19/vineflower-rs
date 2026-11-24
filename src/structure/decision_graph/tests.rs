use crate::bytecode::Instruction;
use crate::cfg::ControlFlowGraph;
use crate::classfile::{ClassFile, ExceptionHandler};
use crate::descriptor::MethodDescriptor;
use crate::structure::{Exceptions, Layout};
use crate::Options;

use super::*;

const CLASS: &[u8] = include_bytes!("../../../tests/upstream/testData/classes/custom/TestEclipseSwitchString.class");

fn op(offset: u32, opcode: u8) -> Instruction {
    Instruction { offset, opcode, operand: Operand::None, len: 1 }
}

fn branch(offset: u32, opcode: u8, target: u32) -> Instruction {
    Instruction { operand: Operand::Branch(target), ..op(offset, opcode) }
}

fn fixture() -> Vec<Instruction> {
    vec![
        // if (p ? a < b : b > c), including javac's goto trampoline.
        op(0, 0x1b), branch(1, 0x99, 12),
        op(4, 0x1c), op(5, 0x1d), branch(6, 0xa2, 22), branch(9, 0xa7, 18),
        op(12, 0x1d), Instruction { operand: Operand::Local(4), ..op(13, 0x15) },
        branch(15, 0xa4, 22),
        op(18, 0x04), op(19, 0xac),
        op(22, 0x03), op(23, 0xac),
    ]
}

fn prove(
    instructions: &[Instruction],
    handlers: &[ExceptionHandler],
    check: impl FnOnce(&Emitter<'_>, &Condition, &[u32], RangeInclusive<u32>),
) {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = &class.methods[1];
    let mut code = method.code(&class.pool).unwrap().unwrap();
    code.max_locals = 6;
    code.max_stack = 3;
    let descriptor = MethodDescriptor::parse("(ZIII)I").unwrap();
    let options = Options { use_debug_names: false, ..Options::default() };
    let renderer = |name: &str| name.replace('/', ".");
    let machine = Machine::new(&class, method, &code, &descriptor, &options, &renderer).unwrap();
    let graph = ControlFlowGraph::build(instructions, handlers).unwrap();
    let exceptions = Exceptions::default();
    let mut emitter = Emitter {
        instructions,
        graph: &graph,
        layout: Layout::new(&graph, instructions, None).unwrap(),
        exceptions: &exceptions,
        exception_redirects: BTreeMap::new(),
        assertions: None,
        emitted: vec![false; graph.blocks.len()],
        lines: Vec::new(),
    };
    emitter.emitted[0] = true;
    let mut condition = Condition {
        taken: graph.block_at(12).unwrap(),
        fallthrough: graph.block_at(4).unwrap(),
        when_true: "!p".into(),
        when_false: "p".into(),
    };
    let mut offsets = vec![0, 1];
    let mut control = 0..=1;
    emitter.collapse_decision_graph(0, Region::METHOD, &machine, &mut condition, &mut offsets, &mut control);
    check(&emitter, &condition, &offsets, control);
}

#[test]
fn folds_the_closed_two_way_cut_and_preserves_offsets() {
    prove(&fixture(), &[], |emitter, result, offsets, control| {
        assert_eq!(result.when_false, "p ? var2 < var3 : var3 > var4");
        assert_eq!(result.when_true, "p ? var2 >= var3 : var3 <= var4");
        assert_eq!(emitter.offset(result.fallthrough), 18);
        assert_eq!(emitter.offset(result.taken), 22);
        assert_eq!(offsets, [0, 1, 4, 5, 6, 12, 13, 15]);
        assert_eq!(control, 0..=15);
        assert_eq!(emitter.emitted.iter().filter(|b| **b).count(), 4);
    });
}

#[test]
fn reuses_the_first_ternary_as_a_nested_selector() {
    let mut instructions = fixture();
    instructions.truncate(9);
    instructions.extend([
        op(18, 0x1c),
        branch(19, 0x9a, 32),
        branch(20, 0xa7, 28),
        op(22, 0x1d),
        branch(23, 0x9a, 32),
        op(28, 0x04),
        op(29, 0xac),
        op(32, 0x03),
        op(33, 0xac),
    ]);
    prove(&instructions, &[], |emitter, result, offsets, control| {
        assert_eq!(
            result.when_false,
            "(p ? var2 < var3 : var3 > var4) ? var2 == 0 : var3 == 0"
        );
        assert_eq!(emitter.offset(result.fallthrough), 28);
        assert_eq!(emitter.offset(result.taken), 32);
        assert_eq!(offsets, [0, 1, 4, 5, 6, 12, 13, 15, 18, 19, 22, 23]);
        assert_eq!(control, 0..=23);
    });
}

#[test]
fn refuses_an_assignment_a_stack_effect_an_external_entry_and_different_handlers() {
    let unchanged = |emitter: &Emitter<'_>, result: &Condition, offsets: &[u32], control| {
        assert_eq!(result.when_false, "p");
        assert_eq!(offsets, [0, 1]);
        assert_eq!(control, 0..=1);
        assert_eq!(emitter.emitted.iter().filter(|b| **b).count(), 1);
    };

    let mut assignment = fixture();
    assignment.splice(3..3, [op(5, 0x3d), op(6, 0x1c)]);
    assignment[5].offset = 7;
    assignment[6].offset = 8;
    prove(&assignment, &[], unchanged);

    let mut stack_effect = fixture();
    // Leave an extra JVM operand below the inputs to the true-arm test.
    stack_effect.insert(3, op(5, 0x03));
    stack_effect[4].offset = 6;
    stack_effect[5].offset = 7;
    prove(&stack_effect, &[], unchanged);

    let mut external_entry = fixture();
    external_entry.push(branch(28, 0xa7, 12));
    prove(&external_entry, &[], unchanged);

    let mut handlers = fixture();
    handlers.extend([op(26, 0x03), op(27, 0xac)]);
    prove(&handlers, &[ExceptionHandler { start_pc: 4, end_pc: 12, handler_pc: 26, catch_type: 0 }], unchanged);
}

#[test]
fn factors_converging_short_circuit_paths_without_copying_a_predicate() {
    let test = |taken, fallthrough, text: &str, inverse: &str| Condition {
        taken, fallthrough, when_false: text.into(), when_true: inverse.into(),
    };
    // a() && b() selects either c() or d(); d is a shared CFG node.
    let decisions = BTreeMap::from([
        (1, Decision::Test(test(3, 2, "b()", "!b()"))),
        (2, Decision::Test(test(5, 4, "c()", "!c()"))),
        (3, Decision::Test(test(5, 4, "d()", "!d()"))),
    ]);
    let root = test(3, 1, "a()", "!a()");
    let mut render = Expression { decisions: &decisions, used: BTreeSet::new() };
    assert_eq!(
        render.test(&root, [4, 5]).unwrap(),
        [Document::from("a() && b() ? c() : d()"), "a() && b() ? !c() : !d()".into()],
    );
    assert_eq!(render.used.len(), 3);
}
