// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::bytecode::{Operand, decode};
use crate::cfg::ControlFlowGraph;
use crate::classfile::ClassFile;

use super::*;

const JSR: &[u8] = include_bytes!("../../tests/upstream/testData/classes/custom/TestJsr.class");
const HOTJAVA: &[u8] =
    include_bytes!("../../tests/upstream/testData/classes/custom/TestHotjava.class");
const JSR2: &[u8] = include_bytes!("../../tests/upstream/testData/classes/custom/TestJsr2.class");

fn fixture<'a>(bytes: &'a [u8], name: &str) -> (ClassFile<'a>, crate::classfile::Code<'a>) {
    let class = ClassFile::parse(bytes).unwrap();
    let method = class
        .methods
        .iter()
        .find(|m| class.pool.utf8(m.name_index).unwrap() == name)
        .unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    (class, code)
}

fn decode_and_expand(
    bytes: &[u8],
    handlers: Vec<ExceptionHandler>,
) -> Result<NormalizedCode, LegacyError> {
    let class = ClassFile::parse(JSR).unwrap();
    normalize(decode(bytes).unwrap(), handlers, &class.pool)
}

fn at_source(code: &NormalizedCode, offset: u32) -> impl Iterator<Item = &Instruction> {
    code.instructions
        .iter()
        .filter(move |op| code.source_offset(op.offset) == Some(offset))
}

fn branch_destination(code: &NormalizedCode, op: &Instruction) -> u32 {
    let Operand::Branch(target) = op.operand else {
        panic!("expected a branch: {op:?}")
    };
    code.source_offset(target).unwrap()
}

fn assert_cfg(code: &NormalizedCode) {
    assert!(
        !code
            .instructions
            .iter()
            .any(|op| matches!(op.opcode, 0xa8 | 0xa9 | 0xc9))
    );
    for pair in code.instructions.windows(2) {
        assert_eq!(pair[0].offset + pair[0].len, pair[1].offset);
    }
    let graph = ControlFlowGraph::build(&code.instructions, &code.handlers).unwrap();
    assert!(graph.reachable().into_iter().all(|reachable| reachable));
}

fn assert_handler_sources(code: &NormalizedCode, original: &[ExceptionHandler]) {
    for op in &code.instructions {
        let Some(source) = code.source_offset(op.offset) else {
            continue;
        };
        let expected: Vec<_> = original
            .iter()
            .filter(|h| (u32::from(h.start_pc)..u32::from(h.end_pc)).contains(&source))
            .map(|h| (u32::from(h.handler_pc), h.catch_type))
            .collect();
        let actual: Vec<_> = code
            .handlers
            .iter()
            .filter(|h| (u32::from(h.start_pc)..u32::from(h.end_pc)).contains(&op.offset))
            .map(|h| {
                (
                    code.source_offset(h.handler_pc.into()).unwrap(),
                    h.catch_type,
                )
            })
            .collect();
        assert_eq!(
            actual, expected,
            "original offset {source}, normalized offset {}",
            op.offset
        );
    }
}

#[test]
fn exact_custom_jsr_clones_finally_and_keeps_both_continuations() {
    let (class, method) = fixture(JSR, "main");
    let expected = method.exceptions.clone();
    let code = normalize(
        decode(method.bytes).unwrap(),
        method.exceptions,
        &class.pool,
    )
    .unwrap();
    assert_cfg(&code);
    assert_handler_sources(&code, &expected);

    let entries: Vec<_> = at_source(&code, 18).collect();
    assert_eq!(entries.len(), 2);
    assert!(entries.iter().all(|op| op.opcode == 0x00)); // address astore removed in both clones
    assert_eq!(at_source(&code, 19).count(), 2);
    assert_eq!(at_source(&code, 12).next().unwrap().opcode, 0x4c); // throwable astore stays
    let returns: Vec<_> = at_source(&code, 27).collect();
    assert_eq!(
        returns
            .iter()
            .map(|op| branch_destination(&code, op))
            .collect::<Vec<_>>(),
        [11, 16]
    );
    for op in returns {
        assert_eq!(op.len, 3);
        assert_eq!(code.source_offset(op.offset + 1), Some(28));
        assert_eq!(code.source_offset(op.offset + 2), None);
    }
}

#[test]
fn exact_hotjava_shared_handler_covers_both_clones_with_original_priority() {
    let (class, method) = fixture(HOTJAVA, "testMonitor3");
    assert_eq!(method.exceptions.len(), 2);
    let expected = method.exceptions.clone();
    let code = normalize(
        decode(method.bytes).unwrap(),
        method.exceptions,
        &class.pool,
    )
    .unwrap();
    assert_cfg(&code);
    assert_handler_sources(&code, &expected);
    assert_eq!(at_source(&code, 24).count(), 2);
    assert_eq!(at_source(&code, 39).count(), 1);
    assert_eq!(code.handlers.len(), 3);
}

#[test]
fn exact_custom_jsr2_without_legacy_opcodes_keeps_identity_provenance() {
    let (class, method) = fixture(JSR2, "main3");
    let instructions = decode(method.bytes).unwrap();
    let input_ptr = instructions.as_ptr();
    let code = normalize(instructions, method.exceptions, &class.pool).unwrap();
    assert_eq!(code.instructions.as_ptr(), input_ptr);
    for offset in 0..method.bytes.len() as u32 {
        assert_eq!(code.source_offset(offset), Some(offset));
    }
    assert_eq!(code.source_offset(method.bytes.len() as u32), None);
}

#[test]
fn nested_jsr_w_retargets_wide_and_narrow_rets() {
    let code = decode_and_expand(
        &[
            0xc9, 0, 0, 0, 6,    // jsr_w 6
            0xb1, // 5: return
            0xc4, 0x3a, 1, 44, // wide astore 300
            0xa8, 0, 7, // 10: jsr 17
            0xc4, 0xa9, 1, 44, // 13: wide ret 300
            0x4c, 0x04, 0x57, // 17: astore_1, iconst_1, pop
            0xa9, 1, // 20: ret 1
        ],
        vec![],
    )
    .unwrap();
    assert_cfg(&code);
    for (source, target) in [(0, 6), (10, 17), (13, 5), (20, 13)] {
        assert_eq!(
            branch_destination(&code, at_source(&code, source).next().unwrap()),
            target
        );
    }
    assert_eq!(at_source(&code, 0).next().unwrap().opcode, 0xc8);
    assert_eq!(at_source(&code, 6).next().unwrap().opcode, 0x00);
    assert_eq!(at_source(&code, 19).next().unwrap().opcode, 0x57);
}

#[test]
fn remaps_switch_targets_alignment_and_operand_provenance() {
    let code = decode_and_expand(
        &[
            0x03, 0xa8, 0, 4, 0xb1, 0xc4, 0x3a, 1, 44, // 5: wide astore 300
            0xab, 0, 0, // 9: lookupswitch with two padding bytes
            0, 0, 0, 23, // default -> 32
            0, 0, 0, 1, // one pair
            0, 0, 0, 0, // key 0
            0, 0, 0, 19, // case 0 -> 28
            0xc4, 0xa9, 1, 44, 0xc4, 0xa9, 1, 44,
        ],
        vec![],
    )
    .unwrap();
    assert_cfg(&code);
    let op = at_source(&code, 9).next().unwrap();
    assert_eq!((op.offset, op.len), (6, 18));
    let Operand::Switch { default, cases } = &op.operand else {
        panic!("missing switch")
    };
    assert_eq!(code.source_offset(*default), Some(32));
    assert_eq!(code.source_offset(cases[0].1), Some(28));
    assert_eq!(code.source_offset(op.offset + 2), Some(12));
}

#[test]
fn clones_protected_ranges_with_their_subroutine_local_handlers() {
    let handlers = vec![ExceptionHandler {
        start_pc: 8,
        end_pc: 10,
        handler_pc: 10,
        catch_type: 0,
    }];
    let code = decode_and_expand(
        &[
            0xa8, 0, 7, 0xa8, 0, 4, 0xb1, // two invocations
            0x4c, 0x01, 0xbf, // store address, then throw null
            0x57, 0xa9, 1, // discard caught exception, ret
        ],
        handlers.clone(),
    )
    .unwrap();
    assert_cfg(&code);
    assert_handler_sources(&code, &handlers);
    let [first, second] = code.handlers[..] else {
        panic!("expected two ranges")
    };
    assert_ne!(first.handler_pc, second.handler_pc);
    assert!(at_source(&code, 10).all(|op| op.opcode == 0x57));
}

#[test]
fn projects_stack_manipulation_without_removing_real_values() {
    let code = decode_and_expand(
        &[
            0x03, 0xa8, 0, 4, 0xb1, // iconst_0, jsr, return
            0x59, 0x4c, 0x58, // dup returnAddress, astore_1, pop2 (address and int)
            0x01, 0x4d, // aconst_null, ordinary astore_2
            0xa9, 1,
        ],
        vec![],
    )
    .unwrap();
    assert_cfg(&code);
    for (source, opcode) in [(5, 0x00), (6, 0x00), (7, 0x57), (9, 0x4d)] {
        assert_eq!(at_source(&code, source).next().unwrap().opcode, opcode);
    }
}

#[test]
fn rejects_recursive_invocation_and_invalid_ret_locals() {
    for (bytes, offset, reason) in [
        (&[0xa9, 1][..], 0, "ret outside a subroutine"),
        (
            &[0xa8, 0, 4, 0xb1, 0x4c, 0x2b, 0x57, 0xa9, 1],
            5,
            "returnAddress read as a Java local",
        ),
        (
            &[0xa8, 0, 4, 0xb1, 0x4c, 0x03, 0x3c, 0xa9, 1],
            7,
            "ret does not read the active subroutine's returnAddress",
        ),
        (
            &[0xa8, 0, 4, 0xb1, 0x4c, 0xa8, 0xff, 0xff, 0xa9, 1],
            5,
            "recursive jsr invocation",
        ),
    ] {
        assert_eq!(
            decode_and_expand(bytes, vec![]).unwrap_err(),
            LegacyError::Invalid { offset, reason }
        );
    }
}

#[test]
fn uses_an_unmapped_bridge_when_a_subroutine_falls_into_an_ancestor_tail() {
    let code = decode_and_expand(
        &[
            0xa8, 0, 7, // jsr 7
            0xa7, 0, 5,    // 3: goto 8 (continuation not taken)
            0x00, // 6: unreachable
            0x4c, // 7: astore_1
            0xb1, // 8: return directly from the enclosing method
        ],
        vec![],
    )
    .unwrap();
    assert_cfg(&code);
    let bridge = code
        .instructions
        .iter()
        .find(|op| code.source_offset(op.offset).is_none())
        .unwrap();
    assert_eq!(bridge.opcode, 0xc8);
    assert_eq!(branch_destination(&code, bridge), 8);
    assert!(
        (bridge.offset..bridge.offset + bridge.len)
            .all(|offset| code.source_offset(offset).is_none())
    );
}
