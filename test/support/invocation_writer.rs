use std::sync::Arc;

use vineflower_rs::{
    decompiler::{
        exps::{ExprKind, write},
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
};

use crate::{upstream_reference, writer_snapshot};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn invocation_writing_matches_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let oracle = upstream_reference::Corpus::discover().run(
        "InvocationWriterReference",
        &["WriterSnapshot"],
        scratch.path(),
    );
    let home = upstream_reference::jdk_home();
    for width in [44, 140] {
        let mut options = Options::default();
        options.preferred_line_length = width;
        options.explicit_generics = width != 44;
        options.include_runtime = if width == 44 { "0" } else { "1" }.into();
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        context
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        context.set_bootstrap_java_home(Some(home.clone()));
        if width != 44 {
            context.add_space(Arc::new(RuntimeImage::open(&home).unwrap()), false);
        }
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let root = cx.class_nodes.id("CallSubject").unwrap();
        process_class(&mut cx, root).unwrap();

        let mut cases = 0;
        for index in 0..cx.class_nodes[root].class.methods.len() {
            let method = &cx.class_nodes[root].class.methods[index];
            let name = format!("{}{}", method.name, method.descriptor);
            for (number, expr) in invocations(&mut cx, root, index).into_iter().enumerate() {
                let mut actual =
                    with_method_for_writing(&mut cx, root, index, |cx| write::to_java(cx, expr, 1))
                        .unwrap();
                writer_snapshot::compare_snapshot(
                    &oracle,
                    &format!("{width}|invocation|{name}|{number}"),
                    &mut actual,
                );
                cases += 1;
            }
        }
        let prefix = format!("section={width}|invocation|");
        assert_eq!(
            cases,
            oracle
                .lines()
                .filter(|row| row.starts_with(&prefix))
                .count()
        );
    }
}

fn invocations(cx: &mut Cx, node: ClassNodeId, index: usize) -> Vec<ExprId> {
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
    lists
        .iter()
        .flat_map(|&list| cx.ir[list].iter().copied())
        .filter_map(|expr| match cx.ir[expr].kind {
            ExprKind::Exit { value, .. } => value,
            _ => Some(expr),
        })
        .filter(|&expr| matches!(cx.ir[expr].kind, ExprKind::Invocation(_)))
        .collect()
}
