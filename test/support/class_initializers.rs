// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use vineflower_rs::decompiler::{
    exps::{ConstantValue, Expr, ExprKind},
    ir::{ExprId, Ir, StatId},
};
use vineflower_rs::engine::{
    Cx, Options, class_nodes::load_classes, class_processor::process_class,
    class_writer::prepare_class_for_writing, context_source::RuntimeImage,
};
use vineflower_rs::structs::StructContext;

use super::upstream_reference::{Corpus, jdk_home};

fn shape(ir: &Ir, expression: ExprId) -> String {
    Expr::all_exprents(ir, expression, true, true)
        .into_iter()
        .filter_map(|id| {
            Some(match &ir[id].kind {
                ExprKind::Field(field) => format!(
                    "field {}.{}{}",
                    field.classname.as_deref().unwrap(),
                    field.name,
                    if field.force_qualified {
                        " qualified"
                    } else {
                        ""
                    }
                ),
                ExprKind::Invocation(call) => format!(
                    "call {}.{}{}",
                    call.classname.as_deref().unwrap(),
                    call.name,
                    call.descriptor.as_str()
                ),
                ExprKind::Function { op, .. } => format!("{op:?}").to_ascii_uppercase(),
                ExprKind::Constant { value, .. } => match value {
                    ConstantValue::Null => "constant null".into(),
                    value => format!("constant {}", value.java_string().unwrap().as_utf8_lossy()),
                },
                ExprKind::New { lambda: true, .. } => "lambda".into(),
                ExprKind::Assignment { .. } => "assignment".into(),
                _ => return None,
            })
        })
        .collect::<Vec<_>>()
        .join("; ")
}

fn dump_body(ir: &Ir, stat: StatId, method: &str, rows: &mut Vec<String>) {
    if let Some(list) = ir[stat].exprents {
        rows.extend(
            ir[list]
                .iter()
                .map(|&expr| format!("body\t{method}\t{}", shape(ir, expr))),
        );
    }
    for &child in &ir[stat].stats {
        dump_body(ir, child, method, rows);
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn initializer_extraction_preserves_constructor_and_static_prefixes() {
    let scratch = tempfile::tempdir().unwrap();
    let reference = Corpus::discover().run("ClassInitializersReference", &[], scratch.path());
    let options = Arc::new(Options::default());
    let mut context = StructContext::new(Arc::clone(&options), None);
    context.add_space(Arc::new(RuntimeImage::open(&jdk_home()).unwrap()), false);
    context
        .add_file(&scratch.path().join("classes"), true)
        .unwrap();
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );

    let node = cx.class_nodes.id("InitializerSubject").unwrap();
    process_class(&mut cx, node).unwrap();
    prepare_class_for_writing(&mut cx, node).unwrap();
    let wrapper = cx.class_nodes[node].wrapper.as_ref().unwrap();
    let mut rows = Vec::new();
    for (kind, table) in [
        ("static", &wrapper.static_field_initializers),
        ("dynamic", &wrapper.dynamic_field_initializers),
    ] {
        for (index, &expr) in table.iter().enumerate() {
            rows.push(format!(
                "{kind}\t{}\t{}",
                table.get_key(index).unwrap(),
                shape(&cx.ir, expr)
            ));
        }
    }
    for method in &wrapper.methods {
        let name = method.method.name.as_str();
        if matches!(name, "<init>" | "<clinit>") || name.starts_with("lambda$") {
            assert!(method.decompile_error().is_none());
            dump_body(
                &cx.ir,
                method.root().unwrap(),
                &format!("{name}{}", method.method.descriptor),
                &mut rows,
            );
        }
    }
    assert_eq!(rows, reference.lines().collect::<Vec<_>>());
    assert!(
        rows.iter()
            .any(|row| row.starts_with("dynamic\tunboxed Z\t") && row.ends_with("CAST"))
    );
    assert!(
        rows.iter()
            .any(|row| row.starts_with("body\tlambda$") && row.ends_with("later qualified"))
    );
    assert!(
        rows.iter()
            .any(|row| row.starts_with("body\t<clinit>()V\t") && row.contains("sideEffect"))
    );
}
