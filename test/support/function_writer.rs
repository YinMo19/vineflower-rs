use std::{collections::BTreeMap, sync::Arc};

use vineflower_rs::{
    decompiler::{
        exps::{ExitType, ExprKind, write},
        ir::ExprId,
    },
    engine::{
        Cx, Options,
        class_nodes::{ClassNodeId, load_classes},
        class_processor::process_class,
        class_writer::with_method_for_writing,
        context_source::RuntimeImage,
    },
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

use crate::{upstream_reference, writer_snapshot};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn function_and_cast_writing_matches_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let oracle = upstream_reference::Corpus::discover().run(
        "FunctionWriterReference",
        &["WriterSnapshot"],
        scratch.path(),
    );
    let runtime = Arc::new(RuntimeImage::open(&upstream_reference::jdk_home()).unwrap());
    let mut mappings = Vec::new();
    for width in [24, 160] {
        let mut options = Options::default();
        options.preferred_line_length = width;
        options.keep_literals = width == 160;
        let options = Arc::new(options);
        let mut context = StructContext::new(options.clone(), None);
        context
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        context.add_space(runtime.clone(), false);
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let node = cx.class_nodes.id("OperatorSubject").unwrap();
        process_class(&mut cx, node).unwrap();

        let mut cases = 0;
        let count = cx.class_nodes[node].class.methods.len();
        for index in 0..count {
            let method = &cx.class_nodes[node].class.methods[index];
            if method.name == "<init>" {
                continue;
            }
            let name = format!("{}|{}", method.name, method.descriptor);
            for (number, expr) in returns(&mut cx, node, index).into_iter().enumerate() {
                let actual =
                    with_method_for_writing(&mut cx, node, index, |cx| write::to_java(cx, expr, 1))
                        .unwrap();
                let name = format!("{name}|{number}");
                let mut buffer = TextBuffer::new(&cx);
                buffer.append_buffer_for(&actual, Some("OperatorSubject"), Some(&name));
                writer_snapshot::compare_snapshot(
                    &oracle,
                    &format!("{width}|expression|{name}"),
                    &mut buffer,
                );
                let tracers = buffer.get_tracers();
                let tracer = tracers.values().next().unwrap();
                let offsets: BTreeMap<_, _> = tracer.get_mapping().iter().collect();
                let row = offsets
                    .iter()
                    .map(|(offset, line)| format!("{offset}={line}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                mappings.push(format!("{width}|{name}|{{{row}}}"));
                cases += 1;
            }
        }
        let prefix = format!("section={width}|expression|");
        assert_eq!(
            cases,
            oracle
                .lines()
                .filter(|row| row.starts_with(&prefix))
                .count()
        );
    }
    let expected = oracle
        .lines()
        .skip_while(|line| *line != "section=bytecode-mappings")
        .skip(1)
        .collect::<Vec<_>>();
    assert_eq!(mappings, expected);
}

fn returns(cx: &mut Cx, node: ClassNodeId, index: usize) -> Vec<ExprId> {
    let method = &mut cx.class_nodes[node].wrapper.as_mut().unwrap().methods[index];
    let graph = method
        .body
        .as_mut()
        .unwrap()
        .as_mut()
        .unwrap()
        .graph(&mut cx.ir);
    let lists: Vec<_> = graph
        .regular_breadth_first()
        .map(|node| graph[node].exprents)
        .collect();
    let expressions: Vec<_> = lists
        .iter()
        .flat_map(|&list| cx.ir[list].iter().copied())
        .filter(|&expr| {
            matches!(
                cx.ir[expr].kind,
                ExprKind::Exit {
                    kind: ExitType::Return,
                    ..
                }
            )
        })
        .collect();
    assert!(!expressions.is_empty(), "{}", method.method);
    expressions
}
