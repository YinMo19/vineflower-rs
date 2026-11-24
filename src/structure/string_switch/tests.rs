use crate::bytecode::decode;
use crate::classfile::ClassFile;
use crate::descriptor::MethodDescriptor;
use crate::options::Options;
use crate::structure::{Exceptions, Layout, Line, structure};

use super::*;

const ECLIPSE: &[u8] =
    include_bytes!("../../../tests/upstream/testData/classes/custom/TestEclipseSwitchString.class");
const JAVAC_STRINGS: &[u8] = include_bytes!("../../../tests/smoke/java8/TestSwitchOnStrings.class");
const JAVAC_COLLISIONS: &[u8] =
    include_bytes!("../../../tests/smoke/java8/TestSwitchStringHashcodeCollision.class");

#[test]
fn original_javac_fixtures_collapse_without_changing_case_priority() {
    let strings = crate::decompile(JAVAC_STRINGS, &Options::default())
        .unwrap()
        .text;
    assert_eq!(strings.matches("switch (s)").count(), 3, "{strings}");
    assert_eq!(
        case_labels(&strings),
        [
            "xxx", "yyy", "xxx", "yyy", "BBAa", "AaAa", "AaBB", "xxx", "yyy", "AaAa", "AaBB",
            "BBAa"
        ],
    );
    let collision = crate::decompile(JAVAC_COLLISIONS, &Options::default())
        .unwrap()
        .text;
    assert_eq!(collision.matches("switch (s)").count(), 1, "{collision}");
    assert_eq!(case_labels(&collision), ["BB", "Aa", "FRED"]);
    assert_eq!(
        collision.matches(r#"System.out.println("Test");"#).count(),
        1
    );
    assert!(!strings.contains("hashCode()") && !collision.contains(".equals("));
}

fn case_labels(source: &str) -> Vec<&str> {
    source
        .lines()
        .filter_map(|line| {
            let (label, _) = line.trim().strip_prefix("case \"")?.split_once("\":")?;
            Some(label)
        })
        .collect()
}

fn block_match(class: &ClassFile<'_>, instructions: &[Instruction]) -> Option<Plan> {
    let graph = ControlFlowGraph::build(instructions, &[]).unwrap();
    Matcher {
        instructions,
        graph: &graph,
        pool: &class.pool,
        ascii: false,
    }
    .plan(0)
}

fn eclipse_collision(class: &ClassFile<'_>) -> Vec<Instruction> {
    let method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == "testHashcodeCollision")
        .unwrap();
    decode(method.code(&class.pool).unwrap().unwrap().bytes).unwrap()
}

fn at(offset: u32, opcode: u8, operand: Operand) -> Instruction {
    Instruction {
        offset,
        opcode,
        operand,
        len: 1,
    }
}

fn split_collision(class: &ClassFile<'_>) -> Vec<Instruction> {
    // Same lowering as TestSwitchOnStrings and TestSwitchStringHashcodeCollision:
    // the equality order is Aa then BB, but the tag order is BB then Aa.
    // Reuse the exact constant-pool entries from the upstream Eclipse fixture.
    let ecj = eclipse_collision(class);
    let operand = |offset| {
        ecj.iter()
            .find(|op| op.offset == offset)
            .unwrap()
            .operand
            .clone()
    };
    let op = |offset, opcode| at(offset, opcode, Operand::None);
    let lookup = |offset, default, cases| at(offset, 0xab, Operand::Switch { default, cases });
    vec![
        op(0, 0x2b),
        op(1, 0x4d),
        op(2, 0x02),
        op(3, 0x3e),
        op(4, 0x2c),
        at(5, 0xb6, operand(3)),
        lookup(6, 24, vec![(2112, 10)]),
        op(10, 0x2c),
        at(11, 0x12, operand(34)),
        at(12, 0xb6, operand(36)),
        at(13, 0x99, Operand::Branch(17)),
        op(14, 0x05),
        op(15, 0x3e),
        at(16, 0xa7, Operand::Branch(24)),
        op(17, 0x2c),
        at(18, 0x12, operand(25)),
        at(19, 0xb6, operand(27)),
        at(20, 0x99, Operand::Branch(24)),
        op(21, 0x04),
        op(22, 0x3e),
        op(24, 0x1d),
        lookup(25, 34, vec![(0, 34), (1, 30), (2, 32)]),
        op(30, 0x04),
        op(31, 0xac),
        op(32, 0x05),
        op(33, 0xac),
        op(34, 0x03),
        op(35, 0xac),
    ]
}

fn labels(plan: &Plan) -> Vec<(&str, u32, Vec<u32>)> {
    plan.dispatch
        .cases
        .iter()
        .map(|&(key, dest)| {
            let (text, offsets) = plan.dispatch.label(key);
            (text, dest, offsets)
        })
        .collect()
}

#[test]
fn javac_collisions_use_tag_order_and_map_the_original_literals() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let instructions = split_collision(&class);
    let plan = block_match(&class, &instructions).unwrap();
    assert_eq!(plan.dispatch.default, 34);
    assert_eq!(
        labels(&plan),
        [(r#""BB""#, 30, vec![18]), (r#""Aa""#, 32, vec![11])]
    );
    assert_eq!(plan.helpers.len(), 5);
    assert_eq!(plan.prefix_end, 1);
    assert_eq!(plan.alias, 2);
    assert_eq!(plan.tag, Some(3));

    let lines = decompile_split(&class, &instructions).unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "switch (var1) {" && line.offsets == [0, 25])
    );
    assert!(!lines.iter().any(|line| {
        let text = line.text.as_flat();
        text.contains("hashCode")
            || text.contains("equals")
            || text.contains("var2")
            || text.contains("var3")
    }));
    let marks = |label, offset| {
        lines
            .iter()
            .any(|line| line.text.as_flat().starts_with(label) && line.offsets == [offset])
    };
    assert!(marks(r#"case "BB":"#, 18));
    assert!(marks(r#"case "Aa":"#, 11));
}

#[test]
fn javac_only_elides_tags_that_are_proven_default_padding() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let mut instructions = split_collision(&class);
    let cases = switch_cases_at(&mut instructions, 25);
    cases[2].1 = 34;
    assert_eq!(
        labels(&block_match(&class, &instructions).unwrap())[1],
        (r#""Aa""#, 34, vec![11])
    );
    let lines = decompile_split(&class, &instructions).unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat().starts_with(r#"case "Aa":"#))
    );

    switch_cases_at(&mut instructions, 25)[0].1 = 32;
    assert!(block_match(&class, &instructions).is_none());
}

#[test]
fn javac_rejects_wrong_hash_receiver_and_duplicate_literal() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let mut instructions = split_collision(&class);
    switch_cases_at(&mut instructions, 6)[0].0 = 2113;
    assert!(block_match(&class, &instructions).is_none());

    let mut instructions = split_collision(&class);
    instructions
        .iter_mut()
        .find(|op| op.offset == 17)
        .unwrap()
        .opcode = 0x2b;
    assert!(block_match(&class, &instructions).is_none());

    let mut instructions = split_collision(&class);
    let literal = instructions
        .iter()
        .find(|op| op.offset == 11)
        .unwrap()
        .operand
        .clone();
    instructions
        .iter_mut()
        .find(|op| op.offset == 18)
        .unwrap()
        .operand = literal;
    assert!(block_match(&class, &instructions).is_none());
}

#[test]
fn extra_entry_or_effect_inside_a_helper_refuses_collapse() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let mut instructions = split_collision(&class);
    // Even an unreachable extra predecessor prevents claiming the helper.
    instructions.push(at(36, 0xa7, Operand::Branch(17)));
    assert!(block_match(&class, &instructions).is_none());

    let mut instructions = split_collision(&class);
    instructions
        .iter_mut()
        .find(|op| op.offset == 22)
        .unwrap()
        .opcode = 0x3c;
    assert!(block_match(&class, &instructions).is_none());
}

#[test]
fn visible_alias_or_tag_at_an_exit_prevents_consuming_its_stores() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    for load in [0x2c, 0x1d] {
        let mut instructions = split_collision(&class);
        instructions
            .iter_mut()
            .find(|op| op.offset == 34)
            .unwrap()
            .opcode = load;
        if load == 0x2c {
            // Make the reference read real bytecode, rather than leaving an
            // areturn in an int method.
            let last = instructions.last_mut().unwrap();
            *last = at(35, 0x57, Operand::None);
            instructions.extend([at(36, 0x03, Operand::None), at(37, 0xac, Operand::None)]);
        }
        assert!(block_match(&class, &instructions).is_some());
        with_split_machine(&class, &instructions, |graph, mut machine| {
            let exceptions = Exceptions::default();
            let mut emitter = Emitter {
                instructions: &instructions,
                graph,
                layout: Layout::new(graph, &instructions, None).unwrap(),
                exceptions: &exceptions,
                exception_redirects: Default::default(),
                resource_epilogue: None,
                assertions: None,
                record_patterns: None,
                emitted: vec![false; graph.blocks.len()],
                lines: Vec::new(),
            };
            assert_eq!(
                emitter
                    .try_emit_string_switch(0, Region::METHOD, &mut machine, 0, &mut Vec::new())
                    .unwrap(),
                None
            );
            assert!(emitter.lines.is_empty() && emitter.emitted.iter().all(|emitted| !*emitted));
        });
    }
}

#[test]
fn null_is_kept_as_a_string_selector_not_dispatched_to_default() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let mut instructions = split_collision(&class);
    instructions[0].opcode = 0x01;
    let lines = decompile_split(&class, &instructions).unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "switch ((String)null) {")
    );
}

#[test]
fn selector_array_read_occurs_once_and_a_source_alias_remains_live() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let mut instructions = split_collision(&class);
    // Introduce a visible alias in slot 4 and switch on alias[0]. The implicit
    // null/bounds checks must remain ahead of the switch's own null check.
    for instruction in &mut instructions {
        instruction.offset += 4;
        match &mut instruction.operand {
            Operand::Branch(target) => *target += 4,
            Operand::Switch { default, cases } => {
                *default += 4;
                for (_, target) in cases {
                    *target += 4;
                }
            }
            _ => {}
        }
    }
    instructions.splice(
        ..1,
        [
            at(0, 0x2b, Operand::None),
            at(1, 0x3a, Operand::Local(4)),
            at(2, 0x19, Operand::Local(4)),
            at(3, 0x03, Operand::None),
            at(4, 0x32, Operand::None),
        ],
    );
    instructions.truncate(instructions.len() - 2);
    instructions.extend([
        at(38, 0x19, Operand::Local(4)),
        at(39, 0xbe, Operand::None),
        at(40, 0xac, Operand::None),
    ]);
    let lines = with_machine(
        &class,
        &instructions,
        "([Ljava/lang/String;)I",
        5,
        |graph, machine| structure(&instructions, graph, machine),
    )
    .unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "String[] var4 = var1;")
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "switch (var4[0]) {")
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text.as_flat() == "return var4.length;")
    );
    assert_eq!(
        lines
            .iter()
            .filter(|line| line.text.as_flat().contains("var4[0]"))
            .count(),
        1
    );
}

#[test]
fn eclipse_buckets_route_collisions_and_fallthrough_to_real_bodies() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let instructions = eclipse_collision(&class);
    let plan = block_match(&class, &instructions).unwrap();
    assert_eq!(plan.dispatch.default, 42);
    assert_eq!(
        labels(&plan),
        [(r#""BB""#, 53, vec![25, 26]), (r#""Aa""#, 55, vec![34, 35])]
    );

    let decompiled = crate::decompile(ECLIPSE, &Options::default()).unwrap();
    let source = decompiled.text;
    assert!(
        !source.contains("hashCode()") && !source.contains(".equals("),
        "{source}"
    );
    assert_eq!(source.matches("switch (var1)").count(), 6, "{source}");
    assert!(
        source.contains(r#"System.out.println("Hello");"#),
        "{source}"
    );
    assert!(source.contains(r#"System.out.println("BB");"#), "{source}");
}

#[test]
fn java_hash_uses_wrapping_utf16_code_units() {
    assert_eq!(java_hash(&[0x0042, 0x0042]), java_hash(&[0x0041, 0x0061]));
    assert_eq!(java_hash(&[0xd83d, 0xde00]), 1_772_899);
    assert_eq!(java_hash(&[0xffff; 5]), -1_884_131_265);
}

fn switch_cases_at(instructions: &mut [Instruction], offset: u32) -> &mut Vec<(i32, u32)> {
    let Operand::Switch { cases, .. } = &mut instructions
        .iter_mut()
        .find(|op| op.offset == offset)
        .unwrap()
        .operand
    else {
        unreachable!()
    };
    cases
}

fn decompile_split(
    class: &ClassFile<'_>,
    instructions: &[Instruction],
) -> Result<Vec<Line>, StructureError> {
    with_split_machine(class, instructions, |graph, machine| {
        structure(instructions, graph, machine)
    })
}

fn with_split_machine<T>(
    class: &ClassFile<'_>,
    instructions: &[Instruction],
    run: impl FnOnce(&ControlFlowGraph, Machine<'_, '_>) -> T,
) -> T {
    with_machine(class, instructions, "(Ljava/lang/String;)I", 4, run)
}

fn with_machine<T>(
    class: &ClassFile<'_>,
    instructions: &[Instruction],
    descriptor: &str,
    max_locals: u16,
    run: impl FnOnce(&ControlFlowGraph, Machine<'_, '_>) -> T,
) -> T {
    let method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == "test")
        .unwrap();
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    let mut code = method.code(&class.pool).unwrap().unwrap();
    code.max_locals = max_locals;
    let options = Options::default();
    let renderer = |class: &str| class.rsplit('/').next().unwrap().to_owned();
    let machine = Machine::new(class, method, &code, &descriptor, &options, &renderer).unwrap();
    let graph = ControlFlowGraph::build(instructions, &[]).unwrap();
    run(&graph, machine)
}
