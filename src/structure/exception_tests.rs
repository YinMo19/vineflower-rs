// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::bytecode::decode;
use crate::cfg::ControlFlowGraph;
use crate::classfile::{ClassFile, ExceptionHandler};
use crate::descriptor::MethodDescriptor;
use crate::lift::Machine;
use crate::options::Options;

use super::{Line, StructureError, structure_with_handlers};
use super::protected::Exceptions;

fn handler(start_pc: u16, end_pc: u16, handler_pc: u16, catch_type: u16) -> ExceptionHandler {
    ExceptionHandler { start_pc, end_pc, handler_pc, catch_type }
}

fn classify(
    bytes: &[u8],
    handlers: &[ExceptionHandler],
) -> (ControlFlowGraph, Result<Exceptions, StructureError>) {
    let instructions = decode(bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, handlers).unwrap();
    let regions = Exceptions::new(&instructions, &graph, handlers);
    (graph, regions)
}

#[test]
fn equal_ranges_merge_alternatives_and_preserve_table_order() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 11, // 3: goto 14
        0x4b, // 6: astore_0
        0xa7, 0, 7, // 7: goto 14
        0x4b, // 10: astore_0
        0xa7, 0, 3, // 11: goto 14
        0xb1, // 14: return
    ];
    let (graph, regions) = classify(
        &bytes,
        &[handler(0, 3, 10, 2), handler(0, 3, 10, 3), handler(0, 3, 6, 4)],
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
        0xa7, 0, 7, // 12: goto 19
        0x4c, // 15: astore_1
        0xa7, 0, 3, // 16: goto 19
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
        0xa7, 0, 4, // 3: goto 7
        0x4b, // 6: astore_0
        0xb8, 0, 1, // 7: invokestatic
        0xa7, 0, 7, // 10: goto 17
        0x4c, // 13: astore_1
        0xa7, 0, 3, // 14: goto 17
        0xb1, // 17: return
    ];
    let (_, regions) = classify(&bytes, &[handler(0, 10, 13, 2), handler(0, 3, 6, 1)]);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn disjoint_ranges_with_distinct_handlers_are_separate_statements() {
    let bytes = [
        0xb8, 0, 1, // 0: invokestatic
        0xa7, 0, 7, // 3: goto 10
        0x4b, // 6: astore_0
        0xa7, 0, 3, // 7: goto 10
        0xb8, 0, 1, // 10: invokestatic
        0xa7, 0, 7, // 13: goto 20
        0x4b, // 16: astore_0
        0xa7, 0, 3, // 17: goto 20
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
        0xa7, 0, 7, // 9: goto 16
        0x4b, // 12: astore_0
        0xa7, 0, 3, // 13: goto 16
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
        0xa7, 0, 9, // 6: goto 15
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
    assert_eq!(regions.finally_range(Some(finally.arm), finally.block()), Some(4..5));
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
        0xa7, 0, 19, // 6: goto 25
        0x4c, // 9: astore_1 (typed handler)
        0xb8, 0, 22, // 10: invokestatic (catch body)
        0xb8, 0, 22, // 13: invokestatic (catch cleanup)
        0xa7, 0, 9, // 16: goto 25
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
    let text: Vec<_> = lines.iter().map(|line| line.text.as_str()).collect();
    assert_eq!(text, [
        "try {",
        "C.work();",
        "} catch (java.lang.RuntimeException var1) {",
        "C.work();",
        "} finally {",
        "C.work();",
        "}",
        "return;",
    ]);
}

#[test]
fn branched_finally_matches_each_edge_and_preserves_an_overriding_return() {
    let mut bytes = [
        0xb8, 0, 22, // 0: invokestatic C.work() (try)
        0x2a, // 3: aload_0 (normal cleanup)
        0xc6, 0, 7, // 4: ifnull 11
        0xb8, 0, 22, // 7: invokestatic C.work()
        0xb1, // 10: return (overrides the original transfer)
        0xa7, 0, 14, // 11: goto 25
        0x4c, 0x2a, // 14: astore_1; aload_0 (exceptional cleanup)
        0xc6, 0, 7, // 16: ifnull 23
        0xb8, 0, 22, // 19: invokestatic C.work()
        0xb1, // 22: return (overrides the exception)
        0x2b, 0xbf, // 23: aload_1; athrow
        0xb1, // 25: return
    ];
    let handlers = [handler(0, 3, 14, 0)];
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[0].text, "try {");
    assert_eq!(lines[2].text, "} finally {");
    assert!(lines.iter().any(|line| line.depth == 2 && line.text == "return;"));
    assert_eq!(lines.iter().filter(|line| line.text == "C.work();").count(), 2);
    assert!(!lines.iter().any(|line| line.text.starts_with("throw ")));

    bytes[4] = 0xc7; // The paired branch takes the different path on null.
    let (_, regions) = classify(&bytes, &handlers);
    assert!(matches!(regions, Err(StructureError::ExceptionHandlers)));
}

#[test]
fn resource_fold_requires_suppression_on_the_original_exception() {
    let mut bytes = [
        0x2a, 0x4c, // 0: aload_0; astore_1
        0xb8, 0, 22, // 2: invokestatic C.work()
        0x2b, // 5: aload_1
        0xc6, 0, 34, // 6: ifnull 40
        0x2b, // 9: aload_1
        0xb9, 0, 13, 1, 0, // 10: invokeinterface AutoCloseable.close()
        0xa7, 0, 25, // 15: goto 40
        0x4d, 0x2b, // 18: astore_2; aload_1
        0xc6, 0, 18, // 20: ifnull 38
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
    assert!(lines.iter().any(|line| line.depth == 1 && line.text == "C.work();"));
    assert!(!lines.iter().any(|line| line.text.contains("close()")));

    // An addSuppressed self-call does not have the semantics of resources.
    bytes[34] = 0x2c;
    let lines = test_method(&bytes, &handlers, &[]).unwrap();
    assert_eq!(lines[1].text, "try {");
    assert_eq!(lines.iter().filter(|line| line.text.contains("close()")).count(), 2);
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
        0xa7, 0, 9, // 3: goto 12
        0x4c, // 6: astore_1
        0x2b, // 7: aload_1
        0xb6, 0, 33, // 8: invokevirtual Exception.getMessage()
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
    utf8(&mut class, "(Ljava/lang/AutoCloseable;)V");
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
    words(&mut code, &[2, 4]); // max_stack, max_locals
    code.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    code.extend_from_slice(bytes);
    words(&mut code, &[handlers.len() as u16]);
    for handler in handlers {
        words(&mut code, &[handler.start_pc, handler.end_pc, handler.handler_pc, handler.catch_type]);
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
    let descriptor = MethodDescriptor::parse("(Ljava/lang/AutoCloseable;)V").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let instructions = decode(code.bytes).unwrap();
    let graph = ControlFlowGraph::build(&instructions, &code.exceptions).unwrap();
    let options = Options::default();
    let render = |name: &str| name.replace('/', ".");
    let machine = Machine::new(&class, method, &code, &descriptor, &options, &render).unwrap();
    structure_with_handlers(&instructions, &graph, machine, &code.exceptions)
}
