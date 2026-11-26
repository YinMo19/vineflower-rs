// SPDX-License-Identifier: Apache-2.0

use std::{collections::BTreeMap, fs, sync::Arc};

use vineflower_rs::{
    decompiler::stats::{StatementKind, write},
    engine::{
        Cx, Options,
        class_nodes::load_classes,
        class_processor::process_class,
        class_wrapper::MethodWrapper,
        class_writer::{prepare_class_for_writing, with_method_for_writing},
        context_source::RuntimeImage,
    },
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

use crate::{upstream_reference, writer_snapshot};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn non_switch_statements_write_like_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let corpus = upstream_reference::Corpus::discover();
    let failure = corpus
        .classes
        .iter()
        .find(|path| path.ends_with("java8/pkg/TestTryReturn.class"))
        .expect("missing Java 8 TestTryReturn fixture");
    let failure_input = scratch.path().join("TestTryReturn.class");
    fs::copy(failure, &failure_input).unwrap();
    let oracle = corpus.run(
        "StatementWriterReference",
        &["WriterSnapshot"],
        scratch.path(),
    );
    let runtime = Arc::new(RuntimeImage::open(&upstream_reference::jdk_home()).unwrap());
    let mut mappings = Vec::new();
    let mut states = Vec::new();

    for width in [26, 37, 160] {
        let mut options = Options::default();
        options.preferred_line_length = width;
        if width == 37 {
            options.decompile_finally = false;
            options.new_line_separator = false;
            options.indent_string = "\t".to_owned();
        }
        let options = Arc::new(options);
        let mut context = StructContext::new(options.clone(), None);
        context
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        context.add_file(&failure_input, true).unwrap();
        context.add_space(runtime.clone(), false);
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let node = cx.class_nodes.id("FlowSubject").unwrap();
        process_class(&mut cx, node).unwrap();
        prepare_class_for_writing(&mut cx, node).unwrap();

        let mut bodies = 0;
        let count = cx.class_nodes[node].wrapper.as_ref().unwrap().methods.len();
        for index in 0..count {
            let method = &cx.class_nodes[node].wrapper.as_ref().unwrap().methods[index];
            let name = format!("{}|{}", method.method.name, method.method.descriptor);
            let state = method_state(method);
            states.push(format!("{width}|FlowSubject|{name}|{state}"));
            if state != "code" {
                continue;
            }
            let root = method.root().unwrap();
            let mut body =
                with_method_for_writing(&mut cx, node, index, |cx| write::to_java(cx, root, 2))
                    .unwrap();
            let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
                panic!("Expected a method root");
            };
            let StatementKind::DummyExit { bytecode } = &cx.ir[dummy_exit].kind else {
                panic!("Expected a dummy exit");
            };
            for offset in bytecode.iter().flat_map(|offsets| offsets.iter()) {
                body.add_bytecode_mapping(offset as i32);
            }
            let mut buffer = TextBuffer::new(&cx);
            buffer.append_buffer_for(&body, Some("FlowSubject"), Some(&name));
            writer_snapshot::compare_snapshot(
                &oracle,
                &format!("{width}|statement|{name}"),
                &mut buffer,
            );
            let tracers = buffer.get_tracers();
            let mapping: BTreeMap<_, _> = tracers
                .values()
                .next()
                .into_iter()
                .flat_map(|tracer| tracer.get_mapping().iter())
                .collect();
            let offsets = mapping
                .iter()
                .map(|(offset, line)| format!("{offset}={line}"))
                .collect::<Vec<_>>()
                .join(", ");
            mappings.push(format!("{width}|{name}|{{{offsets}}}"));
            bodies += 1;
        }
        let prefix = format!("section={width}|statement|");
        assert_eq!(
            bodies,
            oracle
                .lines()
                .filter(|row| row.starts_with(&prefix))
                .count()
        );

        let failures = cx.class_nodes.id("pkg/TestTryReturn").unwrap();
        process_class(&mut cx, failures).unwrap();
        let method = cx.class_nodes[failures]
            .wrapper
            .as_ref()
            .unwrap()
            .methods
            .iter()
            .find(|wrapper| wrapper.method.name == "testParsingFailure")
            .unwrap();
        states.push(format!(
            "{width}|pkg/TestTryReturn|testParsingFailure|()V|{}",
            method_state(method)
        ));
    }

    assert_eq!(mappings, section(&oracle, "section=bytecode-mappings"));
    assert_eq!(states, section(&oracle, "section=method-states"));
    assert!(states.iter().any(|row| row.ends_with("|no-code")));
    assert!(states.iter().any(|row| row.ends_with("|failed")));
}

fn section<'a>(oracle: &'a str, title: &str) -> Vec<&'a str> {
    oracle
        .lines()
        .skip_while(|line| *line != title)
        .skip(1)
        .take_while(|line| !line.starts_with("section="))
        .collect()
}

fn method_state(wrapper: &MethodWrapper) -> &'static str {
    if wrapper.decompile_error().is_some() {
        "failed"
    } else if wrapper.root().is_none() {
        "no-code"
    } else {
        "code"
    }
}
