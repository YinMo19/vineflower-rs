use crate::bytecode;
use crate::classfile::ClassFile;
use crate::descriptor::MethodDescriptor;
use crate::options::Options;

use super::*;

const LOADER: &[u8] =
    include_bytes!("../../tests/upstream/testData/classes/bulk/pkg/res/Loader.class");
const IDEA_NOT_NULL: &[u8] =
    include_bytes!("../../tests/upstream/testData/classes/custom/TestIdeaNotNull.class");
const ECLIPSE_SWITCH: &[u8] =
    include_bytes!("../../tests/upstream/testData/classes/custom/TestEclipseSwitchEnum.class");

fn method_lines(class: &[u8], name: &str) -> Result<Vec<Line>, StructureError> {
    let class = ClassFile::parse(class).unwrap();
    let method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == name)
        .unwrap();
    let descriptor =
        MethodDescriptor::parse(class.pool.utf8(method.descriptor_index).unwrap()).unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let instructions = bytecode::decode(code.bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &code.exceptions).unwrap();
    let options = Options::default();
    let render = |name: &str| name.replace('/', ".");
    let machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap();
    structure_with_handlers(&instructions, &graph, machine, &code.exceptions)
}

#[test]
fn typed_catch_keeps_unprotected_return_split_with_its_value() {
    let lines = method_lines(LOADER, "getResource").unwrap();
    assert!(
        lines
            .iter()
            .any(|line| line.text == "if (resource == null) {" && line.depth == 0)
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text == "try {" && line.depth == 0)
    );
    assert!(
        lines
            .iter()
            .any(|line| line.text.starts_with("return new java.lang.String(")
                && line.depth == 1
                && line.offsets.contains(&79))
    );
    let catch = lines
        .iter()
        .find(|line| line.text == "} catch (java.lang.Exception e) {")
        .unwrap();
    assert_eq!(catch.depth, 0);
    assert_eq!(catch.offsets, [80]);
}

#[test]
fn natural_while_uses_the_backedge_as_its_body_boundary() {
    let lines = method_lines(IDEA_NOT_NULL, "test4").unwrap();
    let header = lines
        .iter()
        .position(|line| line.text.starts_with("while ("))
        .unwrap();
    assert_eq!(lines[header].depth, 0);
    assert!(lines[header].offsets.contains(&20));
    assert_eq!(lines[header + 1].depth, 1);
    assert!(
        lines
            .last()
            .is_some_and(|line| line.text.starts_with("throw ") && line.depth == 0)
    );
    assert!(!lines.iter().any(|line| line.offsets.contains(&45)));
}

#[test]
fn switch_breaks_share_one_final_void_return() {
    let lines = method_lines(ECLIPSE_SWITCH, "test").unwrap();
    assert_eq!(
        lines
            .iter()
            .filter(|line| line.text.starts_with("case "))
            .count(),
        3
    );
    assert!(lines.iter().any(|line| line.text == "default: {"));
    assert_eq!(
        lines.iter().filter(|line| line.text == "return;").count(),
        1
    );
    assert_eq!(lines.last().unwrap().depth, 0);
    assert_eq!(lines.last().unwrap().offsets, [66]);
}

#[test]
fn a_value_carried_across_a_conditional_edge_is_not_silently_dropped() {
    assert!(matches!(
        method_lines(IDEA_NOT_NULL, "test"),
        Err(StructureError::StackJoin { offset: 22 })
    ));
}
