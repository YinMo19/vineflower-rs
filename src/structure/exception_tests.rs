// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::bytecode::decode;
use crate::cfg::ControlFlowGraph;
use crate::classfile::{ClassFile, ExceptionHandler};
use crate::descriptor::MethodDescriptor;
use crate::lift::Machine;
use crate::options::Options;

use super::protected::Exceptions;
use super::{Line, StructureError, structure_with_handlers};

fn handler(start_pc: u16, end_pc: u16, handler_pc: u16, catch_type: u16) -> ExceptionHandler {
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
            "C.work();",
            "} catch (java.lang.RuntimeException var1) {",
            "C.work();",
            "} finally {",
            "C.work();",
            "}",
            "return;",
        ]
    );
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
            "C.work();",
            "} finally {",
            "C.work();",
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
        lines.iter().filter(|line| line.text == "C.work();").count(),
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
        lines.iter().filter(|line| line.text == "C.work();").count(),
        2
    );

    bytes[12] = 3; // Explicit jump now enters the exception handler.
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
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
        lines.iter().filter(|line| line.text == "C.work();").count(),
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
            .any(|line| line.depth == 1 && line.text == "C.work();")
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
            "java.lang.AutoCloseable var3 = var1",
            ") {",
            "C.work();",
            "}",
        ]
    );
    assert!(lines[1].offsets.contains(&1));
    assert!(lines[2].offsets.contains(&3));
    assert_eq!(lines[1].depth, lines[4].depth);
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
    assert_eq!(lines[1].text, "C.work();");
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
    assert_eq!(lines[1].text, "C.work();");
    assert_eq!(lines[3].text, "return;");
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

fn test_method(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
    stack_map: &[u8],
) -> Result<Vec<Line>, StructureError> {
    test_method_with_descriptor(bytes, handlers, stack_map, "(Ljava/lang/AutoCloseable;)V")
}

fn test_method_with_descriptor(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
    stack_map: &[u8],
    descriptor: &str,
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
    words(&mut class, &[0, version, 34]); // minor, major, constant_pool_count
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
    words(&mut class, &[0x0021, 2, 4, 0, 0, 2]); // public class, two methods
    words(&mut class, &[0x0009, 5, 6, 1, 7]); // public static m, Code
    let mut code = Vec::new();
    words(&mut code, &[2, 6]); // max_stack, max_locals
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
    words(&mut class, &[0x0109, 20, 11, 0, 0]); // native work, class attrs

    let class = ClassFile::parse(&class).unwrap();
    let method = &class.methods[0];
    let descriptor = MethodDescriptor::parse(descriptor).unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let instructions = decode(code.bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &code.exceptions).unwrap();
    let options = Options::default();
    let render = |name: &str| name.replace('/', ".");
    let machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap();
    structure_with_handlers(&instructions, &graph, machine, &code.exceptions)
}
