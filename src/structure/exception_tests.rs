// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::bytecode::decode;
use crate::cfg::ControlFlowGraph;
use crate::classfile::{ClassFile, ExceptionHandler};
use crate::descriptor::MethodDescriptor;
use crate::lift::Machine;
use crate::options::Options;

use super::protected::Exceptions;
use super::{Line, StructureError, structure_with_handlers};

pub(super) fn handler(start_pc: u16, end_pc: u16, handler_pc: u16, catch_type: u16) -> ExceptionHandler {
    ExceptionHandler {
        start_pc,
        end_pc,
        handler_pc,
        catch_type,
    }
}

fn classify(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
) -> (ControlFlowGraph, Result<Exceptions, StructureError>) {
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, handlers).unwrap();
    let regions = Exceptions::new(&instructions, &graph, handlers, None);
    (graph, regions)
}

#[test]
fn equal_ranges_merge_alternatives_and_preserve_table_order() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 11,   // 3: goto 14
        0x4b, // 6: astore_0
        0xa7, 0, 7,    // 7: goto 14
        0x4b, // 10: astore_0
        0xa7, 0, 3,    // 11: goto 14
        0xb1, // 14: return
    ];
    let (graph, regions) = classify(
        &bytes,
        &[
            handler(0, 3, 10, 2),
            handler(0, 3, 10, 3),
            handler(0, 3, 6, 4),
        ],
    );
    let regions = regions.unwrap();
    let shape = regions.region(regions.at_start(None, 0).unwrap());
    assert_eq!(shape.join, graph.block_at(14));
    assert_eq!(shape.catches.len(), 2);
    assert_eq!(Some(shape.catches[0].start), graph.block_at(10));
    assert_eq!(shape.catches[0].alternatives, [2, 3]);
    assert_eq!(Some(shape.catches[1].start), graph.block_at(6));
    assert_eq!(shape.catches[1].alternatives, [4]);
}

#[test]
fn nested_same_start_regions_include_inner_handler_in_outer_body() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 6, // 3: goto 9
        0x4b, 0, 0, // 6: astore_0; nop; nop
        0xb8, 0, 1, // 9: invokestatic
        0xa7, 0, 7,    // 12: goto 19
        0x4c, // 15: astore_1
        0xa7, 0, 3,    // 16: goto 19
        0xb1, // 19: return
    ];
    let inner = handler(0, 3, 6, 1);
    let outer = handler(0, 12, 15, 2);
    let (graph, regions) = classify(&bytes, &[inner, outer]);
    let regions = regions.unwrap();
    let outer = regions.region(regions.at_start(None, 0).unwrap());
    let inner = regions.region(regions.at_start(Some(outer.body), 0).unwrap());
    assert_eq!(outer.join, graph.block_at(19));
    assert_eq!(inner.join, graph.block_at(9));
    assert!(regions.contains(Some(outer.body), inner.catches[0].start));
    assert!(!regions.contains(Some(inner.body), inner.catches[0].start));
}

#[test]
fn reversed_dispatch_order_cannot_be_rendered_as_that_nesting() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 4,    // 3: goto 7
        0x4b, // 6: astore_0
        0xb8, 0, 1, // 7: invokestatic
        0xa7, 0, 7,    // 10: goto 17
        0x4c, // 13: astore_1
        0xa7, 0, 3,    // 14: goto 17
        0xb1, // 17: return
    ];
    let (_, regions) = classify(&bytes, &[handler(0, 10, 13, 2), handler(0, 3, 6, 1)]);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn disjoint_ranges_with_distinct_handlers_are_separate_statements() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 7,    // 3: goto 10
        0x4b, // 6: astore_0
        0xa7, 0, 3, // 7: goto 10
        0xb8, 0, 1, // 10: invokestatic
        0xa7, 0, 7,    // 13: goto 20
        0x4b, // 16: astore_0
        0xa7, 0, 3,    // 17: goto 20
        0xb1, // 20: return
    ];
    let (graph, regions) = classify(&bytes, &[handler(0, 3, 6, 1), handler(10, 13, 16, 1)]);
    let regions = regions.unwrap();
    let first = regions.region(regions.at_start(None, 0).unwrap());
    let second = regions.region(regions.at_start(None, first.join.unwrap()).unwrap());
    assert_eq!(first.join, graph.block_at(10));
    assert_eq!(second.join, graph.block_at(20));
}

#[test]
fn split_rows_of_one_range_can_cross_an_unprotected_goto() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 3, // 3: goto 6
        0xb8, 0, 1, // 6: invokestatic
        0xa7, 0, 7,    // 9: goto 16
        0x4b, // 12: astore_0
        0xa7, 0, 3,    // 13: goto 16
        0xb1, // 16: return
    ];
    let (graph, regions) = classify(&bytes, &[handler(0, 3, 12, 1), handler(6, 9, 12, 1)]);
    let regions = regions.unwrap();
    let shape = regions.region(regions.at_start(None, 0).unwrap());
    assert_eq!(shape.catches.len(), 1);
    assert_eq!(shape.join, graph.block_at(16));
    for offset in [0, 3, 6, 9] {
        assert!(regions.contains(Some(shape.body), graph.block_at(offset).unwrap()));
    }
}

#[test]
fn only_identical_normal_and_exceptional_cleanup_forms_finally() {
    let mut bytes = [
        0xb8, 0, 1, // 0: invokestatic (body)
        0xb8, 0, 2, // 3: invokestatic (normal cleanup)
        0xa7, 0, 9,    // 6: goto 15
        0x4b, // 9: astore_0
        0xb8, 0, 2, // 10: invokestatic (exceptional cleanup)
        0x2a, 0xbf, // 13: aload_0; athrow
        0xb1, // 15: return
    ];
    let (graph, regions) = classify(&bytes, &[handler(0, 3, 9, 0)]);
    let regions = regions.unwrap();
    let shape = regions.region(regions.at_start(None, 0).unwrap());
    let finally = shape.finally.as_ref().unwrap();
    assert_eq!(shape.join, graph.block_at(15));
    assert_eq!(Some(finally.start()), graph.block_at(9));
    assert_eq!(
        regions.finally_range(Some(finally.arm), finally.block()),
        Some(4..5)
    );
    assert_eq!(regions.cleanup_prefix(graph.block_at(3).unwrap()), 1);

    bytes[12] = 3;
    let (_, regions) = classify(&bytes, &[handler(0, 3, 9, 0)]);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn catch_all_ranges_can_cover_inner_catches_and_their_own_initial_store() {
    let bytes = [
        0xb8, 0, 22, // 0: invokestatic (body)
        0xb8, 0, 22, // 3: invokestatic (normal cleanup)
        0xa7, 0, 19,   // 6: goto 25
        0x4c, // 9: astore_1 (typed handler)
        0xb8, 0, 22, // 10: invokestatic (catch body)
        0xb8, 0, 22, // 13: invokestatic (catch cleanup)
        0xa7, 0, 9,    // 16: goto 25
        0x4d, // 19: astore_2 (finally handler)
        0xb8, 0, 22, // 20: invokestatic (exceptional cleanup)
        0x2c, 0xbf, // 23: aload_2; athrow
        0xb1, // 25: return
    ];
    let handlers = [
        handler(0, 3, 9, 26),
        handler(0, 3, 19, 0),
        handler(9, 13, 19, 0),
        handler(19, 20, 19, 0),
    ];
    let (graph, regions) = classify(&bytes, &handlers);
    let regions = regions.unwrap();
    let outer = regions.region(regions.at_start(None, 0).unwrap());
    let inner = regions.region(regions.at_start(Some(outer.body), 0).unwrap());
    assert_eq!(outer.join, graph.block_at(25));
    assert_eq!(inner.join, graph.block_at(25));
    assert_eq!(inner.catches.len(), 1);
    let finally = outer.finally.as_ref().unwrap();
    assert_eq!(Some(finally.start()), graph.block_at(19));
    assert_eq!(Some(finally.block()), graph.block_at(20));

    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try {",
            "work();",
            "} catch (java.lang.RuntimeException var1) {",
            "work();",
            "} finally {",
            "work();",
            "}",
            "return;",
        ]
    );
}

#[test]
fn one_finally_copy_can_return_void_while_the_other_continues() {
    let bytes = [
        0xb8, 0, 22, // 0: try work
        0xb8, 0, 22, // 3: normal finally copy
        0xa7, 0, 17, // 6: goto 23
        0x4c, 0xb8, 0, 22, // 9: typed catch and work
        0xb8, 0, 22, // 13: catch's finally copy
        0xb1, // 16: catch returns
        0x4d, 0xb8, 0, 22, // 17: exceptional finally copy
        0x2c, 0xbf, // 21: rethrow
        0xb1, // 23: normal continuation
    ];
    let handlers = [
        handler(0, 3, 9, 24),
        handler(0, 3, 17, 0),
        handler(9, 13, 17, 0),
    ];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try {",
            "work();",
            "} catch (java.io.IOException var1) {",
            "work();",
            "return;",
            "} finally {",
            "work();",
            "}",
            "return;",
        ]
    );
    assert_eq!(lines[4].offsets, [16]);
}

#[test]
fn terminal_finally_supersedes_both_normal_paths_and_the_saved_throwable() {
    let mut bytes = [
        0x1a, 0x99, 0, 8, // 0: branch to 9
        0xb8, 0, 22, // 4: first protected call
        0x04, 0xac, // 7: first normal copy returns 1
        0xb8, 0, 22, // 9: second protected call
        0xa7, 0, 6, // 12: goto second normal copy
        0x4c, // 15: exceptional binding, covered by its own handler row
        0x04, 0xac, // 16: exceptional copy returns 1
        0x04, 0xac, // 18: second normal copy returns 1
    ];
    let handlers = [handler(0, 7, 15, 0), handler(9, 16, 15, 0)];
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], "(Z)I").unwrap();
    let cleanup = lines
        .iter()
        .position(|line| line.text == "} finally {")
        .unwrap();
    assert_eq!(lines[cleanup + 1].text, "return 1;");
    assert_eq!(lines[cleanup + 1].offsets, [16, 17]);
    assert_eq!(
        lines.iter().filter(|line| line.text.starts_with("return ")).count(),
        1
    );

    bytes[18] = 0x05; // Returning 2 is not the same overriding cleanup.
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn cleanup_copies_can_rename_an_unread_category_two_temporary() {
    let code = [
        0xb8, 0, 22, // 0: invokestatic C.work()
        0x0a, 0x40, // 3: lconst_1; lstore_1
        0xa7, 0, 9,    // 5: goto 14
        0x4e, // 8: astore_3
        0x0a, 0x37, 4, // 9: lconst_1; lstore 4
        0x2d, 0xbf, // 12: aload_3; athrow
    ];
    let handlers = [handler(0, 3, 8, 0)];
    let mut bytes = code.to_vec();
    bytes.push(0xb1);
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert!(lines.iter().any(|line| line.text == "long var4 = 1L;"));
    assert!(!lines.iter().any(|line| line.text.contains("var1")));

    // Reading either alias invalidates the dead-store proof.
    let mut bytes = code.to_vec();
    bytes.extend([0x1f, 0x58, 0xb1]); // lload_1; pop2; return
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn copied_cleanup_can_finish_a_try_return_while_the_catch_falls_through() {
    let mut bytes = [
        0x04, 0x3c, // 0: iconst_1; istore_1
        0xb8, 0, 22, // 2: invokestatic C.work() (return cleanup)
        0x1b, 0xac, // 5: iload_1; ireturn
        0x4c, // 7: astore_1 (typed catch)
        0xb8, 0, 22, // 8: invokestatic C.work() (catch statement)
        0xb8, 0, 22, // 11: invokestatic C.work() (catch cleanup)
        0xa7, 0, 9,    // 14: goto 23
        0x4d, // 17: astore_2
        0xb8, 0, 22, // 18: invokestatic C.work() (exceptional cleanup)
        0x2c, 0xbf, // 21: aload_2; athrow
        0x02, 0xac, // 23: iconst_m1; ireturn
    ];
    let handlers = [
        handler(0, 2, 7, 26),
        handler(0, 2, 17, 0),
        handler(7, 11, 17, 0),
    ];
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], "(Ljava/lang/AutoCloseable;)I")
        .unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try {",
            "return 1;",
            "} catch (java.lang.RuntimeException var1) {",
            "work();",
            "} finally {",
            "work();",
            "}",
            "return -1;",
        ]
    );
    assert_eq!(lines[1].offsets, [0, 1]);

    // The pending return must not move before cleanup that accesses its slot.
    for start in [2, 11, 18] {
        bytes[start..start + 3].copy_from_slice(&[0x05, 0x3c, 0x00]);
    }
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn branched_finally_matches_each_edge_and_preserves_an_overriding_return() {
    let mut bytes = [
        0xb8, 0, 22,   // 0: invokestatic C.work() (try)
        0x2a, // 3: aload_0 (normal cleanup)
        0xc6, 0, 7, // 4: ifnull 11
        0xb8, 0, 22,   // 7: invokestatic C.work()
        0xb1, // 10: return (overrides the original transfer)
        0xa7, 0, 14, // 11: goto 25
        0x4c, 0x2a, // 14: astore_1; aload_0 (exceptional cleanup)
        0xc6, 0, 7, // 16: ifnull 23
        0xb8, 0, 22,   // 19: invokestatic C.work()
        0xb1, // 22: return (overrides the exception)
        0x2b, 0xbf, // 23: aload_1; athrow
        0xb1, // 25: return
    ];
    let handlers = [handler(0, 3, 14, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "try {");
    assert_eq!(lines[2].text, "} finally {");
    assert!(
        lines
            .iter()
            .any(|line| line.depth == 2 && line.text == "return;")
    );
    assert_eq!(
        lines.iter().filter(|line| line.text == "work();").count(),
        2
    );
    assert!(!lines.iter().any(|line| line.text.starts_with("throw ")));

    bytes[4] = 0xc7; // The paired branch takes the different path on null.
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn branched_finally_matches_fallthrough_to_an_explicit_jump() {
    let mut bytes = [
        0xb8, 0, 22,   // 0: try body
        0x2a, 0xc6, 0, 19, // 3: normal cleanup; ifnull 23
        0xb8, 0, 22,   // 7: work
        0xa7, 0, 13,   // 10: jump over the exceptional copy
        0x4c, 0x2a, 0xc6, 0, 6, // 13: exceptional cleanup; ifnull 21
        0xb8, 0, 22,   // 18: work; fall through to 21
        0x2b, 0xbf,   // 21: rethrow the original exception
        0xb1, // 23: normal continuation
    ];
    let handlers = [handler(0, 3, 13, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "try {");
    assert_eq!(lines[2].text, "} finally {");
    assert_eq!(
        lines.iter().filter(|line| line.text == "work();").count(),
        2
    );

    bytes[12] = 3; // Explicit jump now enters the exception handler.
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn switch_finally_folds_only_a_mirrored_shared_return() {
    let bytes = [
        0xb8, 0, 22, // 0: protected call
        0xb8, 0, 22, 0x1a, // 3: normal cleanup prefix and selector
        0xab, 0, 0, 0, 37, 0, 0, 0, 2, // 7: lookupswitch, default 44
        0, 0, 0, 0, 0, 0, 0, 25, // case 0: 32
        0, 0, 0, 1, 0, 0, 0, 31, // case 1: 38
        0xb8, 0, 22, 0xa7, 0, 12, // 32: case 0 prints, then goto 47
        0xb8, 0, 22, 0xa7, 0, 68, // 38: case 1 prints, then goto shared return at 109
        0xb8, 0, 22, // 44: default prints and falls through
        0xb8, 0, 22, 0xa7, 0, 54, // 47: cleanup tail, then goto normal return at 104
        0x4c, 0xb8, 0, 22, 0x1a, // 53: save throwable, cleanup prefix and selector
        0xab, 0, 0, 0, 0, 38, 0, 0, 0, 2, // 58: lookupswitch, default 96
        0, 0, 0, 0, 0, 0, 0, 26, // case 0: 84
        0, 0, 0, 1, 0, 0, 0, 32, // case 1: 90
        0xb8, 0, 22, 0xa7, 0, 12, // 84: case 0 prints, then goto 99
        0xb8, 0, 22, 0xa7, 0, 16, // 90: case 1 prints, then goto 109
        0xb8, 0, 22, // 96: default prints and falls through
        0xb8, 0, 22, 0x2b, 0xbf, // 99: cleanup tail, then rethrow saved exception
        0xb8, 0, 22, 0x04, 0xac, // 104: normal continuation
        0xb8, 0, 22, 0x03, 0xac, // 109: shared overriding continuation
    ];
    let handlers = [handler(0, 3, 53, 0)];
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], "(I)I").unwrap();
    assert_eq!(
        lines
            .iter()
            .map(|line| (line.depth, line.text.as_flat()))
            .collect::<Vec<_>>(),
        [
            (0, "try {"),
            (1, "work();"),
            (0, "} finally {"),
            (1, "work();"),
            (1, "switch (var0) {"),
            (2, "case 0:"),
            (3, "work();"),
            (3, "break;"),
            (2, "case 1:"),
            (3, "work();"),
            (3, "work();"),
            (3, "return 0;"),
            (2, "default:"),
            (3, "work();"),
            (1, "}"),
            (1, "work();"),
            (0, "}"),
            (0, "work();"),
            (0, "return 1;"),
        ]
    );
    assert_eq!(lines[10].offsets, [93, 94, 95, 109, 110, 111]);
    assert_eq!(lines[17].offsets, [50, 51, 52, 104, 105, 106]);

    for (offset, displacement) in [(43, 63), (95, 11), (52, 59)] {
        // Redirect either case-1 copy or give the shared return a third
        // incoming path from the normal cleanup tail.
        let mut mismatch = bytes;
        mismatch[offset] = displacement;
        assert!(matches!(
            classify(&mismatch, &handlers).1,
            Err(StructureError::ExceptionHandlers),
        ));
    }
}

#[test]
fn exceptional_finally_copy_can_be_detached_from_the_enclosing_loop_cfg() {
    let bytes = [
        0x03, 0x3c, // 0: int induction = 0
        0x1b, 0x10, 10, 0xa2, 0, 32, // 2: loop test; if_icmpge 37
        0xb8, 0, 22,   // 8: work in the protected body
        0x2a, 0xc6, 0, 19, // 11: normal cleanup; ifnull 31
        0xb8, 0, 22,   // 15: work in the normal cleanup
        0xa7, 0, 13,   // 18: goto loop latch
        0x4d, 0x2a, 0xc6, 0, 6, // 21: exceptional cleanup; ifnull 29
        0xb8, 0, 22,   // 26: work in the exceptional cleanup
        0x2c, 0xbf,   // 29: exceptional rethrow
        0x84, 1, 1, // 31: induction++
        0xa7, 0xff, 0xe0, // 34: goto 2
        0xb1, // 37: normal exit
    ];
    let handlers = [handler(8, 11, 21, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    let cleanup = lines
        .iter()
        .position(|line| line.text == "} finally {")
        .unwrap();
    assert_eq!(lines[cleanup].depth, 1);
    assert_eq!(
        lines.iter().filter(|line| line.text == "work();").count(),
        2
    );
    assert!(!lines.iter().any(|line| line.text.starts_with("throw ")));
}

#[test]
fn each_branched_finally_copy_projects_to_one_proven_continuation() {
    let mut bytes = vec![
        0x2a, // 0: aload_0
        0xc6, 0, 20, // 1: ifnull 21 (try)
        0xb8, 0, 22, // 4: invokestatic C.work()
        0xa7, 0, 3,    // 7: goto 10
        0x2a, // 10: aload_0 (normal copy A)
        0xc6, 0, 7, // 11: ifnull 18
        0xb8, 0, 22,   // 14: invokestatic C.work()
        0xb1, // 17: return
        0xa7, 0, 25,   // 18: goto 43
        0x2a, // 21: aload_0 (normal copy B)
        0xc6, 0, 7, // 22: ifnull 29
        0xb8, 0, 22,   // 25: invokestatic C.work()
        0xb1, // 28: return
        0xa7, 0, 14, // 29: goto 43
        0x4c, 0x2a, // 32: astore_1; aload_0 (exceptional cleanup)
        0xc6, 0, 7, // 34: ifnull 41
        0xb8, 0, 22,   // 37: invokestatic C.work()
        0xb1, // 40: return
        0x2b, 0xbf, // 41: aload_1; athrow
        0xb1, // 43: return (common continuation)
    ];
    let handlers = [handler(0, 10, 32, 0)];
    let (graph, regions) = classify(&bytes, &handlers);
    let regions = regions.unwrap();
    let join = graph.block_at(43).unwrap();
    assert_eq!(regions.bypass_cleanup(graph.block_at(10).unwrap()), join);
    assert_eq!(regions.bypass_cleanup(graph.block_at(21).unwrap()), join);
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(
        lines.iter().filter(|line| line.text == "work();").count(),
        2
    );
    assert_eq!(
        lines
            .iter()
            .filter(|line| line.text == "} finally {")
            .count(),
        1
    );
    assert!(
        lines
            .iter()
            .any(|line| line.depth == 2 && line.text == "return;")
    );

    // A different observable continuation cannot be projected to 43.
    bytes[31] = 15;
    bytes.extend([0xb8, 0, 22, 0xb1]); // 44: invokestatic C.work(); return
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn resource_fold_requires_suppression_on_the_original_exception() {
    let mut bytes = [
        0x2a, 0x4c, // 0: aload_0; astore_1
        0xb8, 0, 22,   // 2: invokestatic C.work()
        0x2b, // 5: aload_1
        0xc6, 0, 34,   // 6: ifnull 40
        0x2b, // 9: aload_1
        0xb9, 0, 13, 1, 0, // 10: invokeinterface AutoCloseable.close()
        0xa7, 0, 25, // 15: goto 40
        0x4d, 0x2b, // 18: astore_2; aload_1
        0xc6, 0, 18,   // 20: ifnull 38
        0x2b, // 23: aload_1
        0xb9, 0, 13, 1, 0, // 24: invokeinterface AutoCloseable.close()
        0xa7, 0, 9, // 29: goto 38
        0x4e, 0x2c, 0x2d, // 32: astore_3; aload_2; aload_3
        0xb6, 0, 19, // 35: invokevirtual Throwable.addSuppressed(Throwable)
        0x2c, 0xbf, // 38: aload_2; athrow
        0xb1, // 40: return
    ];
    let handlers = [handler(2, 5, 18, 15), handler(23, 29, 32, 15)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "try (java.lang.AutoCloseable var1 = var0) {");
    assert!(
        lines
            .iter()
            .any(|line| line.depth == 1 && line.text == "work();")
    );
    assert!(!lines.iter().any(|line| line.text.contains("close()")));

    // An addSuppressed self-call does not have the semantics of resources.
    bytes[34] = 0x2c;
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[1].text, "try {");
    assert_eq!(
        lines
            .iter()
            .filter(|line| line.text.contains("close()"))
            .count(),
        2
    );
}

#[test]
fn nullable_resource_return_preserves_the_value_before_closing() {
    let bytes = [
        0x2a, 0x4c, // 0: aload_0; astore_1
        0x2b, 0x4d, // 2: aload_1; astore_2 (return spill)
        0x2b, // 4: aload_1
        0xc6, 0, 9,    // 5: ifnull 14
        0x2b, // 8: aload_1
        0xb9, 0, 13, 1, 0, // 9: invokeinterface AutoCloseable.close()
        0x2c, 0xb0, // 14: aload_2; areturn
        0x4d, 0x2b, // 16: astore_2; aload_1
        0xc6, 0, 18,   // 18: ifnull 36
        0x2b, // 21: aload_1
        0xb9, 0, 13, 1, 0, // 22: invokeinterface AutoCloseable.close()
        0xa7, 0, 9, // 27: goto 36
        0x4e, 0x2c, 0x2d, // 30: astore_3; aload_2; aload_3
        0xb6, 0, 19, // 33: invokevirtual Throwable.addSuppressed(Throwable)
        0x2c, 0xbf, // 36: aload_2; athrow
    ];
    let handlers = [handler(2, 4, 16, 15), handler(21, 27, 30, 15)];
    let lines = test_method_with_descriptor(
        &bytes,
        &handlers,
        &[],
        "(Ljava/lang/AutoCloseable;)Ljava/lang/AutoCloseable;",
    )
    .unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try (java.lang.AutoCloseable var1 = var0) {",
            "return var1;",
            "}"
        ]
    );
    assert_eq!(lines[1].offsets, [2, 15]);

    let mut bytes = bytes.to_vec();
    bytes.extend([0x4c, 0x01, 0xb0]); // 38: astore_1; aconst_null; areturn
    let handlers = [
        handlers[0],
        handlers[1],
        handler(0, 14, 38, 26),
        handler(16, 38, 38, 26),
    ];
    let lines = test_method_with_descriptor(
        &bytes,
        &handlers,
        &[],
        "(Ljava/lang/AutoCloseable;)Ljava/lang/AutoCloseable;",
    )
    .unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try (java.lang.AutoCloseable var1 = var0) {",
            "return var1;",
            "} catch (java.lang.RuntimeException var1_1) {",
            "return null;",
            "}",
        ]
    );
    assert_eq!(lines[1].depth, 1);
}

#[test]
fn primitive_resource_return_can_extend_to_an_exclusive_unprotected_tail() {
    let bytes = [
        0x2a, 0x4c, // 0: aload_0; astore_1
        0x08, 0x3d, // 2: iconst_5; istore_2
        0x2b, 0xc6, 0, 9, // 4: aload_1; ifnull 14
        0x2b, 0xb9, 0, 13, 1, 0, // 8: aload_1; close
        0x1c, 0xac, // 14: iload_2; ireturn (outside ambient catch range)
        0x4d, 0x2b, 0xc6, 0, 18, // 16: save original exception; ifnull 36
        0x2b, 0xb9, 0, 13, 1, 0, // 21: aload_1; close
        0xa7, 0, 9, // 27: goto 36
        0x4e, 0x2c, 0x2d, 0xb6, 0, 19, // 30: addSuppressed
        0x2c, 0xbf, // 36: rethrow original exception
        0x4c, 0x10, 0xfe, 0xac, // 38: ambient catch; return -2
    ];
    let handlers = [
        handler(2, 4, 16, 15),
        handler(21, 27, 30, 15),
        handler(0, 14, 38, 24),
        handler(16, 38, 38, 24),
    ];
    let lines =
        test_method_with_descriptor(&bytes, &handlers, &[], "(Ljava/lang/AutoCloseable;)I").unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try (java.lang.AutoCloseable var1 = var0) {",
            "return 5;",
            "} catch (java.io.IOException var1_1) {",
            "return -2;",
            "}",
        ]
    );
    assert_eq!(lines[1].offsets, [2, 15]);

    // Java 9+ permits the original variable in the resource header when
    // the copy never appears in the body and its source was not reassigned.
    let mut frames = [
        0, 5,
        255, 0, 14, 0, 3, 7, 0, 9, 7, 0, 9, 1, 0, 0, // 14: normal return
        255, 0, 1, 0, 2, 7, 0, 9, 7, 0, 9, 0, 1, 7, 0, 15, // 16: primary handler
        255, 0, 13, 0, 3, 7, 0, 9, 7, 0, 9, 7, 0, 15, 0, 1, 7, 0, 15, // 30: suppression handler
        255, 0, 5, 0, 3, 7, 0, 9, 7, 0, 9, 7, 0, 15, 0, 0, // 36: rethrow
        255, 0, 1, 0, 1, 7, 0, 9, 0, 1, 7, 0, 24, // 38: ambient catch
    ];
    let descriptor = "(Ljava/lang/AutoCloseable;)I";
    let lines = test_method_with_descriptor(&bytes, &handlers, &frames, descriptor).unwrap();
    assert_eq!(lines[0].text, "try (var0) {");
    assert!(lines[0].offsets.contains(&1));

    let mut reassigned = vec![0x01, 0x4b]; // aconst_null; astore_0
    reassigned.extend(bytes);
    frames[4] += 2; // The first stack-map offset moves with the instruction stream.
    let shifted = handlers.map(|row| {
        handler(row.start_pc + 2, row.end_pc + 2, row.handler_pc + 2, row.catch_type)
    });
    let lines = test_method_with_descriptor(&reassigned, &shifted, &frames, descriptor).unwrap();
    assert!(
        lines.iter().any(|line| line.text == "try (java.lang.AutoCloseable var1 = var0) {")
    );
}

#[test]
fn catchless_nested_resources_share_one_header_and_keep_acquisition_offsets() {
    let bytes = [
        0x2a, 0x4d, // 0: outer resource declaration
        0x2b, 0x4e, // 2: inner resource declaration
        0xb8, 0, 22, // 4: work under both resources
        0x2d, 0xc6, 0, 39, // 7: if inner resource is null, go to 47
        0x2d, 0xb9, 0, 13, 1, 0, // 11: normal inner close
        0xa7, 0, 30, // 17: goto 47
        0x3a, 4, 0x2d, 0xc6, 0, 21, // 20: save throwable; ifnull 44
        0x2d, 0xb9, 0, 13, 1, 0, // 26: exceptional inner close
        0xa7, 0, 12, // 32: goto 44
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 35: addSuppressed
        0x19, 4, 0xbf, // 44: rethrow inner exception
        0x2c, 0xc6, 0, 39, // 47: if outer resource is null, go to 87
        0x2c, 0xb9, 0, 13, 1, 0, // 51: normal outer close
        0xa7, 0, 30, // 57: goto 87
        0x3a, 4, 0x2c, 0xc6, 0, 21, // 60: save throwable; ifnull 84
        0x2c, 0xb9, 0, 13, 1, 0, // 66: exceptional outer close
        0xa7, 0, 12, // 72: goto 84
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 75: addSuppressed
        0x19, 4, 0xbf, // 84: rethrow outer exception
        0xb1, // 87: return
    ];
    let handlers = [
        handler(4, 7, 20, 15),
        handler(26, 32, 35, 15),
        handler(2, 47, 60, 15),
        handler(66, 72, 75, 15),
    ];
    let lines = test_method_with_descriptor(
        &bytes,
        &handlers,
        &[],
        "(Ljava/lang/AutoCloseable;Ljava/lang/AutoCloseable;)V",
    )
    .unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        &text[..6],
        [
            "try (",
            "java.lang.AutoCloseable var2 = var0;",
            "java.lang.AutoCloseable var3 = var1;",
            ") {",
            "work();",
            "}",
        ]
    );
    assert!(lines[1].offsets.contains(&1));
    assert!(lines[2].offsets.contains(&3));
    assert_eq!(lines[1].depth, lines[4].depth);

    // The value is selected inside the inner try, but reloaded only after
    // the outer close. The single source return must keep the real opcode.
    let mut bytes = bytes[..87].to_vec();
    bytes[4..7].copy_from_slice(&[0x2d, 0x3a, 4]); // aload_3; astore 4
    bytes.extend([0x19, 4, 0xb0]); // 87: aload 4; areturn
    let lines = test_method_with_descriptor(
        &bytes,
        &handlers,
        &[],
        "(Ljava/lang/AutoCloseable;Ljava/lang/AutoCloseable;)Ljava/lang/AutoCloseable;",
    )
    .unwrap();
    let returned: Vec<_> = lines
        .iter()
        .filter(|line| line.text.starts_with("return "))
        .collect();
    assert_eq!(returned.len(), 1);
    assert_eq!(returned[0].text, "return var3;");
    assert_eq!(returned[0].offsets, [4, 89]);
}

#[test]
fn split_normal_resource_copies_must_rejoin_at_the_same_continuation() {
    let mut bytes = [
        0x2a, 0x4d, // 0: acquire resource
        0x1b, 0x99, 0, 19, // 2: branch to 22
        0xb8, 0, 22, // 6: first work path
        0x2c, 0xc6, 0, 52, // 9: first null guard
        0x2c, 0xb9, 0, 13, 1, 0, // 13: first close copy
        0xa7, 0, 43, // 19: go to 62
        0xb8, 0, 22, // 22: second work path
        0x2c, 0xc6, 0, 36, // 25: second null guard
        0x2c, 0xb9, 0, 13, 1, 0, // 29: second close copy
        0xa7, 0, 27, // 35: go to 62
        0x4e, 0x2c, 0xc6, 0, 20, // 38: save throwable; ifnull 60
        0x2c, 0xb9, 0, 13, 1, 0, // 43: exceptional close
        0xa7, 0, 11, // 49: go to 60
        0x3a, 4, 0x2d, 0x19, 4, 0xb6, 0, 19, // 52: addSuppressed
        0x2d, 0xbf, // 60: rethrow
        0xb1, // 62: normal continuation
    ];
    let handlers = [
        handler(2, 9, 38, 15),
        handler(22, 25, 38, 15),
        handler(43, 49, 52, 15),
    ];
    let descriptor = "(Ljava/lang/AutoCloseable;Z)V";
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
    assert_eq!(
        lines[0].text,
        "try (java.lang.AutoCloseable var2 = var0) {"
    );
    assert_eq!(
        lines.iter().filter(|line| line.text == "work();").count(),
        2
    );
    assert!(!lines.iter().any(|line| line.text.as_flat().contains("close()")));

    let mut returned = bytes.to_vec();
    returned[22..25].copy_from_slice(&[0, 0x08, 0x3e]); // nop; iconst_5; istore_3
    returned[28] = 38; // 26: ifnull 64
    returned[37] = 29; // 35: goto 64
    returned[62] = 0x03;
    returned.extend([0xac, 0x1d, 0xac]); // 62: return 0; 64: iload_3; ireturn
    let int_descriptor = "(Ljava/lang/AutoCloseable;Z)I";
    let lines = test_method_with_descriptor(&returned, &handlers, &[], int_descriptor).unwrap();
    let early = lines.iter().find(|line| line.text == "return 5;").unwrap();
    let later = lines.iter().find(|line| line.text == "return 0;").unwrap();
    assert!(early.depth > later.depth);
    assert!(early.offsets.contains(&65));
    assert_eq!(later.offsets, [62, 63]);

    returned[6..9].copy_from_slice(&[0, 0x03, 0x3e]); // Same slot, different exit.
    returned[62] = 0x1d;
    let lines = test_method_with_descriptor(&returned, &handlers, &[], int_descriptor).unwrap();
    for (value, transfer) in [("return 0;", 63), ("return 5;", 65)] {
        let line = lines.iter().find(|line| line.text == value).unwrap();
        assert!(line.depth > 0);
        assert!(line.offsets.contains(&transfer));
    }

    bytes[28] = 37;
    bytes[37] = 28;
    // Both branches of the second close now agree on a different return.
    let mut bytes = bytes.to_vec();
    bytes.push(0xb1);
    assert!(matches!(
        test_method_with_descriptor(&bytes, &handlers, &[], descriptor),
        Err(StructureError::ExceptionHandlers)
    ));
}

#[test]
fn nested_split_resources_delegate_each_return_to_its_own_spill() {
    let mut bytes = [
        0x2a, 0x4d, // 0: acquire outer resource
        0x2a, 0x4e, // 2: acquire inner resource
        0x1b, 0x99, 0, 29, // 4: select between two terminal paths
        0x08, 0x36, 4, // 8: first return spill
        0x2d, 0xc6, 0, 9, // 11: test inner resource
        0x2d, 0xb9, 0, 13, 1, 0, // 15: close inner resource
        0x2c, 0xc6, 0, 9, // 21: test outer resource
        0x2c, 0xb9, 0, 13, 1, 0, // 25: close outer resource
        0x15, 4, 0xac, // 31: first return
        0x06, 0x36, 4, // 34: second return spill (reuses local slot)
        0x2d, 0xc6, 0, 9, // 37: test inner resource
        0x2d, 0xb9, 0, 13, 1, 0, // 41: close inner resource
        0x2c, 0xc6, 0, 9, // 47: test outer resource
        0x2c, 0xb9, 0, 13, 1, 0, // 51: close outer resource
        0x15, 4, 0xac, // 57: second return
        0x3a, 4, 0x2d, 0xc6, 0, 21, // 60: inner primary exception
        0x2d, 0xb9, 0, 13, 1, 0, // 66: inner exceptional close
        0xa7, 0, 12, // 72: go to inner rethrow
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 75: add suppressed
        0x19, 4, 0xbf, // 84: inner rethrow
        0x3a, 4, 0x2c, 0xc6, 0, 21, // 87: outer primary exception
        0x2c, 0xb9, 0, 13, 1, 0, // 93: outer exceptional close
        0xa7, 0, 12, // 99: go to outer rethrow
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 102: add suppressed
        0x19, 4, 0xbf, // 111: outer rethrow
    ];
    let handlers = [
        handler(4, 11, 60, 15),
        handler(34, 37, 60, 15),
        handler(66, 72, 75, 15),
        handler(2, 21, 87, 15),
        handler(34, 47, 87, 15),
        handler(60, 87, 87, 15),
        handler(93, 99, 102, 15),
    ];
    let descriptor = "(Ljava/lang/AutoCloseable;Z)I";
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
    assert!(lines[1].text.as_flat().contains("var2 = var0"));
    assert!(lines[2].text.as_flat().contains("var3 = var0"));
    for (value, spill, transfer) in [("return 5;", 8, 33), ("return 3;", 34, 59)] {
        let mut matches = lines.iter().filter(|line| line.text == value);
        let line = matches.next().unwrap();
        assert!(matches.next().is_none());
        assert!(line.offsets.contains(&spill));
        assert!(line.offsets.contains(&transfer));
    }

    bytes[51] = 0x2d; // Closing a different resource on one path is observable.
    assert!(test_method_with_descriptor(&bytes, &handlers, &[], descriptor).is_err());
}

#[test]
fn nested_split_resource_stops_at_the_enclosing_close_before_falling_through() {
    let bytes = [
        0x2a, 0x4d, // 0: acquire outer resource
        0x2a, 0x4e, // 2: acquire inner resource
        0x1b, 0x99, 0, 29, // 4: select fallthrough path at 34
        0x2d, 0x3a, 4, // 8: spill the early return value
        0x2d, 0xc6, 0, 9, // 11: first inner close guard -> 21
        0x2d, 0xb9, 0, 13, 1, 0, // 15: first inner close
        0x2c, 0xc6, 0, 9, // 21: first outer close guard -> 31
        0x2c, 0xb9, 0, 13, 1, 0, // 25: first outer close
        0x19, 4, 0xb0, // 31: reload the return value
        0xb8, 0, 22, // 34: work on the fallthrough path
        0x2d, 0xc6, 0, 39, // 37: second inner close guard -> 77
        0x2d, 0xb9, 0, 13, 1, 0, // 41: second inner close
        0xa7, 0, 30, // 47: goto 77
        0x3a, 4, 0x2d, 0xc6, 0, 21, // 50: inner primary exception
        0x2d, 0xb9, 0, 13, 1, 0, // 56: inner exceptional close
        0xa7, 0, 12, // 62: goto 74
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 65: inner addSuppressed
        0x19, 4, 0xbf, // 74: inner rethrow
        0x2c, 0xc6, 0, 39, // 77: second outer close guard -> 117
        0x2c, 0xb9, 0, 13, 1, 0, // 81: second outer close
        0xa7, 0, 30, // 87: goto 117
        0x3a, 4, 0x2c, 0xc6, 0, 21, // 90: outer primary exception
        0x2c, 0xb9, 0, 13, 1, 0, // 96: outer exceptional close
        0xa7, 0, 12, // 102: goto 114
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 105: outer addSuppressed
        0x19, 4, 0xbf, // 114: outer rethrow
        0x01, 0xb0, // 117: ordinary return after both resource scopes
    ];
    let handlers = [
        handler(4, 11, 50, 15),
        handler(34, 37, 50, 15),
        handler(56, 62, 65, 15),
        handler(2, 21, 90, 15),
        handler(34, 77, 90, 15),
        handler(96, 102, 105, 15),
    ];
    let decompile = |bytes| {
        test_method_with_descriptor(
            bytes,
            &handlers,
            &[],
            "(Ljava/lang/AutoCloseable;Z)Ljava/lang/AutoCloseable;",
        )
    };
    let lines = decompile(&bytes).unwrap();
    assert_eq!(lines[0].text, "try (");
    assert_eq!(lines[1].text, "java.lang.AutoCloseable var2 = var0;");
    assert_eq!(lines[2].text, "java.lang.AutoCloseable var3 = var0;");
    let early = lines.iter().find(|line| line.text == "return var3;").unwrap();
    assert!(early.depth > 0);
    assert_eq!(early.offsets, [8, 33]);
    let work = lines.iter().find(|line| line.text == "work();").unwrap();
    assert!(work.depth > 0 && work.offsets.contains(&34));
    let ordinary = lines.last().unwrap();
    assert_eq!(ordinary.text, "return null;");
    assert_eq!(ordinary.depth, 0);
    assert_eq!(ordinary.offsets, [117, 118]);
    assert!(!lines.iter().any(|line| line.text.contains("close()")));

    let mut wrong_landing = bytes;
    wrong_landing[40] = 79; // The null path bypasses the outer close.
    assert!(decompile(&wrong_landing).is_err());

    let mut wrong_resource = bytes;
    wrong_resource[81] = 0x2d; // The enclosing exit closes the inner slot again.
    assert!(decompile(&wrong_resource).is_err());

    let mut reversed_suppression = bytes;
    reversed_suppression.swap(68, 70);
    assert!(decompile(&reversed_suppression).is_err());
}

#[test]
fn legacy_resource_proves_the_primary_exception_and_both_closes() {
    let mut bytes = [
        0x2a, 0x4c, 0x01, 0x4d, // 0: resource store; primary = null
        0x2b, 0x4e, // 4: spill the return
        0x2b, 0xc6, 0, 33, // 6: if resource is null, return at 40
        0x2c, 0xc6, 0, 23, // 10: if primary is null, close at 34
        0x2b, 0xb9, 0, 13, 1, 0, // 14: close with primary
        0xa7, 0, 20, // 20: goto 40
        0x3a, 4, 0x2c, 0x19, 4, // 23: secondary catch; load primary and secondary
        0xb6, 0, 19, // 28: addSuppressed
        0xa7, 0, 9, // 31: goto 40
        0x2b, 0xb9, 0, 13, 1, 0, // 34: close with no primary
        0x2d, 0xb0, // 40: return spill
        0x4e, 0x2d, 0x4d, 0x2d, 0xbf, // 42: record and rethrow original failure
        0x3a, 5, // 47: catch-all stores incoming exception
        0x2b, 0xc6, 0, 33, // 49: if resource is null, rethrow at 83
        0x2c, 0xc6, 0, 23, // 53: if primary is null, close at 77
        0x2b, 0xb9, 0, 13, 1, 0, // 57: close with primary
        0xa7, 0, 20, // 63: goto 83
        0x3a, 4, 0x2c, 0x19, 4, // 66: secondary catch; load primary and secondary
        0xb6, 0, 19, // 71: addSuppressed
        0xa7, 0, 9, // 74: goto 83
        0x2b, 0xb9, 0, 13, 1, 0, // 77: close with no primary
        0x19, 5, 0xbf, // 83: rethrow incoming exception
    ];
    let handlers = [
        handler(14, 20, 23, 15),
        handler(4, 6, 42, 15),
        handler(4, 6, 47, 0),
        handler(57, 63, 66, 15),
        handler(42, 49, 47, 0),
    ];
    let descriptor = "(Ljava/lang/AutoCloseable;)Ljava/lang/AutoCloseable;";
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
    let text: Vec<_> = lines.iter().map(|line| line.text.as_flat()).collect();
    assert_eq!(
        text,
        [
            "try (java.lang.AutoCloseable var1 = var0) {",
            "return var1;",
            "}"
        ]
    );

    bytes[67] = 5; // Overwrite the exception that the catch-all must rethrow.
    assert!(matches!(
        test_method_with_descriptor(&bytes, &handlers, &[], descriptor),
        Err(StructureError::ExceptionHandlers),
    ));
}

#[test]
fn synchronized_owns_the_same_monitor_on_both_exit_paths() {
    let mut bytes = [
        0x2a, 0x59, 0x4c, 0xc2, // 0: aload_0; dup; astore_1; monitorenter
        0xb8, 0, 22, // 4: invokestatic C.work()
        0x2b, 0xc3, // 7: aload_1; monitorexit
        0xa7, 0, 8, // 9: goto 17
        0x4d, 0x2b, 0xc3, // 12: astore_2; aload_1; monitorexit
        0x2c, 0xbf, // 15: aload_2; athrow
        0xb1, // 17: return
    ];
    let handlers = [handler(4, 9, 12, 0), handler(12, 15, 12, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "synchronized (var0) {");
    assert_eq!(lines[0].offsets, [0, 3]);
    assert_eq!(lines[1].text, "work();");
    assert_eq!(lines[1].depth, 1);
    assert_eq!(lines[2].text, "}");
    assert_eq!(lines[2].offsets, [8]);
    assert_eq!(lines[3].text, "return;");

    // Changing the lock on only one exit must not yield synchronized source.
    bytes[7] = 0x2a;
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn synchronized_finally_copies_can_use_distinct_synthetic_slots() {
    // javac's TestSynchronizedTry.test1 layout, with C.work() in each body
    // and a second parameter to exercise genuinely different lock objects.
    let mut bytes = [
        0x2a, 0x59, 0x4d, 0xc2, // 0: acquire the try-body monitor
        0x00, 0xb8, 0, 22, // 4: work
        0x2c, 0xc3, // 8: release
        0xa7, 0, 8, // 10: goto 18
        0x4e, 0x2c, 0xc3, // 13: exception and release
        0x2d, 0xbf, // 16: rethrow
        0x2a, 0x59, 0x4d, 0xc2, // 18: acquire the normal cleanup monitor
        0x00, 0xb8, 0, 22, // 22: work
        0x2c, 0xc3, // 26: release
        0xa7, 0, 8, // 28: goto 36
        0x4e, 0x2c, 0xc3, // 31: exception and release
        0x2d, 0xbf, // 34: rethrow
        0xa7, 0, 31, // 36: goto 67
        0x3a, 4, // 39: finally handler saves the throwable
        0x2a, 0x59, 0x3a, 5, 0xc2, // 41: acquire the exceptional cleanup monitor
        0x00, 0xb8, 0, 22, // 46: work
        0x19, 5, 0xc3, // 50: release
        0xa7, 0, 11, // 53: goto 64
        0x3a, 3, 0x19, 5, 0xc3, // 56: exception and release
        0x19, 3, 0xbf, // 61: rethrow failure from synchronized
        0x19, 4, 0xbf, // 64: rethrow original failure
        0xb1, // 67: return
    ];
    let mut handlers = [
        handler(4, 10, 13, 0),
        handler(13, 16, 13, 0),
        handler(22, 28, 31, 0),
        handler(31, 34, 31, 0),
        handler(0, 18, 39, 0),
        handler(46, 53, 56, 0),
        handler(56, 61, 56, 0),
        handler(39, 41, 39, 0),
    ];
    let descriptor = "(Ljava/lang/Object;Ljava/lang/Object;)V";
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
    assert_eq!(
        lines
            .iter()
            .map(|line| (line.depth, line.text.as_flat()))
            .collect::<Vec<_>>(),
        [
            (0, "try {"),
            (1, "synchronized (var0) {"),
            (2, "work();"),
            (1, "}"),
            (0, "} finally {"),
            (1, "synchronized (var0) {"),
            (2, "work();"),
            (1, "}"),
            (0, "}"),
            (0, "return;"),
        ]
    );

    // The exceptional copy must evaluate the same lock expression.
    bytes[41] = 0x2b; // aload_1
    assert!(matches!(classify(&bytes, &handlers).1, Err(StructureError::ExceptionHandlers)));
    bytes[41] = 0x2a;

    // A different reference on just one release is not synthetic.
    bytes[51] = 1; // aload 1
    assert!(matches!(classify(&bytes, &handlers).1, Err(StructureError::ExceptionHandlers)));
    bytes[51] = 5;

    // A handler cannot release a monitor whose acquisition just failed.
    handlers[2].start_pc = 18;
    assert!(matches!(classify(&bytes, &handlers).1, Err(StructureError::ExceptionHandlers)));
    handlers[2].start_pc = 22;

    // An enclosing catch-all must not intercept the inner monitor retry.
    handlers.swap(1, 4);
    assert!(matches!(classify(&bytes, &handlers).1, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn synchronized_can_release_outside_an_older_protected_range() {
    let bytes = [
        0x2a, 0x4c, 0x2b, 0xc2, // 0: aload_0; astore_1; aload_1; monitorenter
        0xb8, 0, 22, // 4: invokestatic C.work()
        0x2b, 0xc3, // 7: aload_1; monitorexit
        0xa7, 0, 6, // 9: goto 15
        0x2b, 0xc3, 0xbf, // 12: aload_1; monitorexit; athrow
        0xb1, // 15: return
    ];
    let handlers = [handler(4, 7, 12, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "synchronized (var0) {");
    assert_eq!(lines[1].text, "work();");
    assert_eq!(lines[3].text, "return;");
}

#[test]
fn synchronized_handler_may_protect_only_its_exception_store() {
    let bytes = [
        0x2a, 0x4c, 0x2b, 0xc2, // 0: aload_0; astore_1; aload_1; monitorenter
        0xb8, 0, 22, // 4: work
        0x2b, 0xc3, // 7: release outside the protected range
        0xa7, 0, 8, // 9: goto 17
        0x4d, // 12: isolated, self-protected throwable store
        0x2b, 0xc3, 0x2c, 0xbf, // 13: release and rethrow
        0xb1, // 17: return
    ];
    let handlers = [handler(4, 7, 12, 0), handler(12, 13, 12, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "synchronized (var0) {");
    assert_eq!(lines[1].text, "work();");
    assert_eq!(lines[3].text, "return;");
}

#[test]
fn synchronized_split_departure_preserves_the_enclosing_try_tail() {
    let mut bytes = [
        0x2a, 0x59, 0x4d, 0xc2, // 0: acquire monitor
        0x1b, 0x9e, 0, 8, // 4: if var1 <= 0, goto 13
        0x2c, 0xc3, // 8: unlock to leave the entire try
        0xa7, 0, 27, // 10: goto 37
        0xb8, 0, 22, // 13: work while holding the monitor
        0x2c, 0xc3, // 16: unlock to continue the try
        0xa7, 0, 8, // 18: goto 26
        0x4e, 0x2c, 0xc3, // 21: release on exception
        0x2d, 0xbf, // 24: rethrow
        0xb8, 0, 22, // 26: work after releasing the monitor
        0xa7, 0, 8, // 29: goto 37
        0x3a, 4, // 32: catch Exception
        0xb8, 0, 22, // 34: work in the catch
        0xb1, // 37: return
    ];
    let monitor_rows = [
        handler(4, 10, 21, 0),
        handler(13, 18, 21, 0),
        handler(21, 24, 21, 0),
    ];
    let descriptor = "(Ljava/lang/Object;I)V";
    for jump_via_stub in [false, true] {
        let mut handlers = monitor_rows.to_vec();
        if jump_via_stub {
            bytes[12] = 19; // goto 29; the label still ends at 37
            handlers.push(handler(0, 29, 32, 28));
        } else {
            handlers.extend([handler(0, 10, 32, 28), handler(13, 29, 32, 28)]);
        }
        let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
        assert_eq!(lines[0].text, "try {");
        assert_eq!(lines[1].text, "label37: {");
        assert_eq!(lines[2].text, "synchronized (var0) {");
        assert!(lines.iter().any(|line| line.depth == 4 && line.text == "break label37;"));
        let work_depths: Vec<_> = lines
            .iter()
            .filter(|line| line.text == "work();")
            .map(|line| line.depth)
            .collect();
        assert!(matches!(work_depths.as_slice(), [3 | 4, 2, 1]));

        bytes[8] = 0x01; // aconst_null on only the abrupt unlock
        assert!(matches!(classify(&bytes, &handlers).1, Err(StructureError::ExceptionHandlers)));
        bytes[8] = 0x2c;
    }
}

#[test]
fn synchronized_inner_catch_stops_at_the_normal_unlock() {
    let bytes = [
        0x2a, 0x59, 0x4d, 0xc2, // 0: acquire monitor
        0x00, // 4: enter the monitor scope before the typed try
        0x2b, 0xc7, 0, 6, // 5: if var1 != null, goto 12
        0x2c, 0xc3, 0xb1, // 9: release and return
        0x2c, 0xc3, 0xb1, // 12: release and return
        0x4e, 0x2c, 0xc3, // 15: catch Exception; release the monitor
        0xa7, 0, 10, // 18: goto 28
        0x3a, 4, 0x2c, 0xc3, // 21: release on uncaught exception
        0x19, 4, 0xbf, // 25: rethrow
        0xb8, 0, 22, // 28: work outside synchronized and outside the catch
        0xb1, // 31: return
    ];
    let handlers = [
        handler(5, 9, 15, 28),
        handler(4, 11, 21, 0),
        handler(12, 14, 21, 0),
        handler(15, 18, 21, 0),
        handler(21, 25, 21, 0),
    ];
    let descriptor = "(Ljava/lang/Object;Ljava/lang/Object;)V";
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
    assert_eq!(lines[0].text, "synchronized (var0) {");
    assert!(lines.iter().any(|line| {
        line.depth == 1 && line.text.as_flat().starts_with("} catch (java.lang.Exception ")
    }));
    let work = lines.iter().find(|line| line.text == "work();").unwrap();
    assert_eq!(work.depth, 0);
}

#[test]
fn synchronized_finally_can_leave_the_monitor_from_within_a_loop() {
    let mut bytes = [
        0x2a, 0x59, 0x4d, 0xc2, // 0: acquire monitor
        0xb8, 0, 22, // 4: work inside the monitor
        0x1b, 0x9e, 0, 44, // 7: loop header; leave the loop at 52
        0x84, 1, 0xff, // 11: decrement var1
        0xb8, 0, 22, // 14: work before the try
        0xb8, 0, 22, // 17: work in the try
        0xb8, 0, 22, // 20: work in the normal cleanup copy
        0x1b, 0x08, 0xa4, 0, 24, // 23: if var1 <= 5, loop again at 49
        0x2c, 0xc3, // 28: otherwise unlock
        0xa7, 0, 37, // 30: goto 67
        0x4e, // 33: finally handler
        0xb8, 0, 22, // 34: work in the exceptional cleanup copy
        0x1b, 0x08, 0xa4, 0, 8, // 37: if var1 <= 5, rethrow at 47
        0x2c, 0xc3, // 42: otherwise unlock and override the exception
        0xa7, 0, 23, // 44: goto 67
        0x2d, 0xbf, // 47: rethrow original failure
        0xa7, 0xff, 0xd6, // 49: goto 7
        0xb8, 0, 22, // 52: work after the loop, still holding the lock
        0x2c, 0xc3, // 55: ordinarily unlock
        0xa7, 0, 10, // 57: goto 67
        0x3a, 4, 0x2c, 0xc3, // 60: unlock on uncaught exception
        0x19, 4, 0xbf, // 64: rethrow
        0xb8, 0, 22, // 67: work outside synchronized
        0xb1, // 70: return
    ];
    let handlers = [
        handler(17, 20, 33, 0),
        handler(4, 30, 60, 0),
        handler(33, 44, 60, 0),
        handler(47, 57, 60, 0),
        handler(60, 64, 60, 0),
    ];
    let descriptor = "(Ljava/lang/Object;I)V";
    let lines = test_method_with_descriptor(&bytes, &handlers, &[], descriptor).unwrap();
    assert_eq!(lines[0].text, "synchronized (var0) {");
    assert_eq!(lines[1].text, "label67: {");
    assert!(lines.iter().any(|line| line.depth == 2 && line.text.as_flat().starts_with("while (")));
    assert!(lines.iter().any(|line| line.depth == 3 && line.text == "} finally {"));
    assert!(lines.iter().any(|line| line.depth == 5 && line.text == "break label67;"));
    let work = lines.iter().rev().find(|line| line.text == "work();").unwrap();
    assert_eq!(work.depth, 0);

    // The exceptional copy cannot bypass a statement done on normal exit.
    bytes[46] = 26; // goto 70, not 67
    assert!(matches!(classify(&bytes, &handlers).1, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn monitor_head_cannot_be_entered_without_acquisition() {
    let bytes = [
        0x03, // 0: iconst_0
        0x99, 0, 7, // 1: ifeq 8
        0x2a, 0x59, 0x4c, 0xc2, // 4: aload_0; dup; astore_1; monitorenter
        0xb8, 0, 22, // 8: invokestatic C.work()
        0x2b, 0xc3, // 11: aload_1; monitorexit
        0xa7, 0, 8, // 13: goto 21
        0x4d, 0x2b, 0xc3, // 16: astore_2; aload_1; monitorexit
        0x2c, 0xbf, // 19: aload_2; athrow
        0xb1, // 21: return
    ];
    let handlers = [handler(8, 13, 16, 0), handler(16, 19, 16, 0)];
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn multicatch_binds_the_verifier_type_without_narrowing_the_union() {
    let bytes = [
        0xb8, 0, 22, // 0: invokestatic C.work()
        0xa7, 0, 9,    // 3: goto 12
        0x4c, // 6: astore_1
        0x2b, // 7: aload_1
        0xb6, 0, 33,   // 8: invokevirtual Exception.getMessage()
        0x57, // 11: pop
        0xb1, // 12: return
    ];
    let handlers = [handler(0, 3, 6, 24), handler(0, 3, 6, 26)];
    let stack_map = [0, 2, 70, 7, 0, 28, 5]; // handler at 6 with Exception; join at 12
    let lines = test_method(&bytes, &handlers, &stack_map).unwrap();
    assert!(lines.iter().any(|line| {
        line.text == "} catch (java.io.IOException | java.lang.RuntimeException var1) {"
    }));
    assert!(lines.iter().any(|line| line.text == "var1.getMessage();"));
}

#[test]
fn overriding_finally_returns_through_its_enclosing_resource() {
    let mut bytes = [
        0xbb, 0, 2, 0x59, 0xb7, 0, 36, 0x4d, // 0: acquire outer resource, slot 2
        0xbb, 0, 2, 0x59, 0xb7, 0, 36, 0x4e, // 8: acquire inner resource, slot 3
        0x2d, 0x3a, 4, // 16: save inner return
        0x2d, 0xb6, 0, 37, // 19: close inner resource
        0x2c, 0x3a, 5, // 23: inner finally saves overriding return
        0x2c, 0xb6, 0, 37, // 26: close outer resource
        0x01, 0xb0, // 30: outer finally's overriding return
        0x3a, 4, // 32: inner primary exception
        0x2d, 0xb6, 0, 37, // 34: close inner resource
        0xa7, 0, 12, // 38: go to rethrow
        0x3a, 5, 0x19, 4, 0x19, 5, 0xb6, 0, 19, // 41: add suppressed
        0x19, 4, 0xbf, // 50: rethrow
        0x3a, 6, // 53: inner finally entry
        0x2c, 0x3a, 7, // 55: save its overriding return
        0x2c, 0xb6, 0, 37, // 58: close outer resource normally even on inner exception
        0x01, 0xb0, // 62: outer finally's overriding return
        0x4e, // 64: outer primary exception
        0x2c, 0xb6, 0, 37, // 65: outer exceptional close
        0xa7, 0, 11, // 69: go to rethrow
        0x3a, 4, 0x2d, 0x19, 4, 0xb6, 0, 19, // 72: add suppressed
        0x2d, 0xbf, // 80: rethrow
        0x3a, 8, 0x01, 0xb0, // 82: outer finally returns null
    ];
    let handlers = [
        handler(16, 19, 32, 15),
        handler(34, 38, 41, 15),
        handler(8, 23, 53, 0),
        handler(32, 55, 53, 0),
        handler(8, 26, 64, 15),
        handler(32, 58, 64, 15),
        handler(65, 69, 72, 15),
        handler(0, 30, 82, 0),
        handler(32, 62, 82, 0),
        handler(64, 84, 82, 0),
    ];
    let decompile = |bytes: &[u8]| test_method_in_class(bytes, &handlers, &[], "()LC;", true);
    let lines = decompile(&bytes).unwrap();
    assert_eq!(
        lines.iter().filter(|line| line.text.as_flat().starts_with("try (")).count(),
        2,
    );
    assert_eq!(lines.iter().filter(|line| line.text == "} finally {").count(), 2);
    assert!(!lines.iter().any(|line| line.text.as_flat().contains("addSuppressed")));
    let inner_return = lines.iter().find(|line| line.text == "return var2;").unwrap();
    let outer_return = lines.iter().find(|line| line.text == "return null;").unwrap();
    assert!(inner_return.depth > outer_return.depth);
    assert_eq!(inner_return.offsets, [55]);
    assert_eq!(outer_return.offsets, [84, 85]);

    // If a different local is closed, suppression/no-suppression semantics
    // are not interchangeable and the synthetic return is not justified.
    bytes[58] = 0x2d;
    assert!(decompile(&bytes).is_err());
}

fn test_method(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
    stack_map: &[u8],
) -> Result<Vec<Line>, StructureError> {
    test_method_with_descriptor(bytes, handlers, stack_map, "(Ljava/lang/AutoCloseable;)V")
}

pub(super) fn test_method_with_descriptor(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
    stack_map: &[u8],
    descriptor: &str,
) -> Result<Vec<Line>, StructureError> {
    test_method_in_class(bytes, handlers, stack_map, descriptor, false)
}

fn test_method_in_class(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
    stack_map: &[u8],
    descriptor: &str,
    closeable: bool,
) -> Result<Vec<Line>, StructureError> {
    fn words(buffer: &mut Vec<u8>, values: &[u16]) {
        buffer.extend(values.iter().flat_map(|value| value.to_be_bytes()));
    }
    fn utf8(buffer: &mut Vec<u8>, text: &str) {
        buffer.push(1);
        words(buffer, &[text.len().try_into().unwrap()]);
        buffer.extend_from_slice(text.as_bytes());
    }
    fn entry(buffer: &mut Vec<u8>, tag: u8, indices: &[u16]) {
        buffer.push(tag);
        words(buffer, indices);
    }

    let mut class = vec![0xca, 0xfe, 0xba, 0xbe];
    let version = if stack_map.is_empty() { 49 } else { 55 };
    words(&mut class, &[0, version, if closeable { 39 } else { 34 }]);
    utf8(&mut class, "C"); // #1
    entry(&mut class, 7, &[1]);
    utf8(&mut class, "java/lang/Object");
    entry(&mut class, 7, &[3]);
    utf8(&mut class, "m");
    utf8(&mut class, descriptor);
    utf8(&mut class, "Code");
    utf8(&mut class, "java/lang/AutoCloseable"); // #8
    entry(&mut class, 7, &[8]);
    utf8(&mut class, "close");
    utf8(&mut class, "()V");
    entry(&mut class, 12, &[10, 11]);
    entry(&mut class, 11, &[9, 12]); // #13: InterfaceMethodref
    utf8(&mut class, "java/lang/Throwable");
    entry(&mut class, 7, &[14]); // #15: catch type
    utf8(&mut class, "addSuppressed");
    utf8(&mut class, "(Ljava/lang/Throwable;)V");
    entry(&mut class, 12, &[16, 17]);
    entry(&mut class, 10, &[15, 18]); // #19: addSuppressed
    utf8(&mut class, "work");
    entry(&mut class, 12, &[20, 11]);
    entry(&mut class, 10, &[2, 21]); // #22: work
    utf8(&mut class, "java/io/IOException");
    entry(&mut class, 7, &[23]); // #24
    utf8(&mut class, "java/lang/RuntimeException");
    entry(&mut class, 7, &[25]); // #26
    utf8(&mut class, "java/lang/Exception");
    entry(&mut class, 7, &[27]); // #28
    utf8(&mut class, "StackMapTable"); // #29
    utf8(&mut class, "getMessage");
    utf8(&mut class, "()Ljava/lang/String;");
    entry(&mut class, 12, &[30, 31]);
    entry(&mut class, 10, &[28, 32]); // #33: getMessage
    if closeable {
        utf8(&mut class, "<init>"); // #34
        entry(&mut class, 12, &[34, 11]);
        entry(&mut class, 10, &[2, 35]); // #36: C.<init>
        entry(&mut class, 10, &[2, 12]); // #37: C.close
        entry(&mut class, 10, &[4, 35]); // #38: Object.<init>
        words(&mut class, &[0x0021, 2, 4, 1, 9, 0, 4]); // implements AutoCloseable
    } else {
        words(&mut class, &[0x0021, 2, 4, 0, 0, 2]);
    }
    words(&mut class, &[0x0009, 5, 6, 1, 7]); // public static m, Code
    let mut code = Vec::new();
    words(&mut code, &[2, if closeable { 9 } else { 6 }]);
    code.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    code.extend_from_slice(bytes);
    words(&mut code, &[handlers.len() as u16]);
    for handler in handlers {
        words(
            &mut code,
            &[
                handler.start_pc,
                handler.end_pc,
                handler.handler_pc,
                handler.catch_type,
            ],
        );
    }
    if stack_map.is_empty() {
        words(&mut code, &[0]);
    } else {
        words(&mut code, &[1, 29]);
        code.extend_from_slice(&(stack_map.len() as u32).to_be_bytes());
        code.extend_from_slice(stack_map);
    }
    class.extend_from_slice(&(code.len() as u32).to_be_bytes());
    class.extend_from_slice(&code);
    words(&mut class, &[0x0109, 20, 11, 0]); // native work
    if closeable {
        words(&mut class, &[0x0101, 10, 11, 0]); // native close
        words(&mut class, &[0x0001, 34, 11, 1, 7, 0, 17, 1, 1, 0, 5]);
        class.extend([0x2a, 0xb7, 0, 38, 0xb1]);
        words(&mut class, &[0, 0]);
    }
    words(&mut class, &[0]); // class attrs

    let class_bytes = class.as_slice();
    let class = ClassFile::parse(class_bytes).unwrap();
    let method = &class.methods[0];
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let instructions = decode(code.bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &code.exceptions).unwrap();
    let options = Options::default();
    let render = |name: &str| name.replace('/', ".");
    let machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap();
    let group = closeable.then(|| crate::ClassGroup::new([class_bytes]).unwrap());
    let machine = match &group {
        Some(group) => machine.with_group(group),
        None => machine,
    };
    structure_with_handlers(&instructions, &graph, machine, &code.exceptions)
}
