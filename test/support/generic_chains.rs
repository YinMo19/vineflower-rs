use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use vineflower_rs::{
    decompiler::{
        exps::{Expr, ExprKind},
        ir::{ExprId, StatId},
    },
    engine::{
        Cx, Options,
        class_nodes::{ClassKind, load_classes},
        class_processor::process_class_methods,
        context_source::RuntimeImage,
        method_processor::defined_method,
    },
    structs::StructContext,
    types::VarType,
};

fn ty(ty: Option<&VarType>) -> String {
    let Some(t) = ty else { return "-".to_owned() };
    let args = t
        .arguments()
        .iter()
        .map(|a| self::ty(a.as_ref()))
        .collect::<Vec<_>>()
        .join(",");
    let parent = self::ty(t.parent());
    format!(
        "{}/{}/{}/{}/{parent}[{args}]",
        format!("{:?}", t.ty).to_uppercase(),
        t.array_dim,
        t.value.as_deref().unwrap_or("-"),
        t.wildcard()
    )
}

fn expression(cx: &Cx, expr: ExprId, seen: &mut HashSet<ExprId>, output: &mut Vec<String>) {
    if !seen.insert(expr) {
        return;
    }
    match &cx.ir[expr].kind {
        ExprKind::Invocation(call) => {
            if let Some(g) = &call.generics {
                let mut map = g
                    .mappings
                    .iter()
                    .map(|(k, v)| format!("{}={}", ty(Some(k)), ty(v.as_ref())))
                    .collect::<Vec<_>>();
                map.sort();
                let args = g.arguments.iter().map(|a| ty(Some(a))).collect::<Vec<_>>();
                if g.resolved_method.is_some()
                    || !args.is_empty()
                    || !map.is_empty()
                    || g.force_qualification
                    || g.is_invocation_instance
                    || g.remapped_instance.is_some()
                    || g.keep_unboxing_cast
                {
                    let selected = g
                        .resolved_method
                        .as_ref()
                        .map(|m| format!("{}.{}{}", m.class_qualified_name, m.name, m.descriptor))
                        .unwrap_or("-".into());
                    output.push(format!(
                        "call\t{}.{}{}\t{selected}\t{}\t{}\t{}\t{}\t{}\t{}",
                        call.classname.as_deref().unwrap_or("null"),
                        call.name,
                        call.string_descriptor(),
                        g.is_invocation_instance,
                        g.force_qualification,
                        g.keep_unboxing_cast,
                        ty(g.remapped_instance.as_ref()),
                        args.join(";"),
                        map.join(";")
                    ));
                }
            }
        }
        ExprKind::New {
            new_type,
            generics: Some(g),
            ..
        } if g.inferred_lambda_type.is_some() || !g.arguments.is_empty() => {
            let args = g
                .arguments
                .iter()
                .map(|a| ty(Some(a)))
                .collect::<Vec<_>>()
                .join(";");
            output.push(format!(
                "new\t{}\t{}\t{args}",
                new_type.name(),
                ty(g.inferred_lambda_type.as_ref())
            ));
        }
        _ => {}
    }
    for child in Expr::children(&cx.ir, expr) {
        expression(cx, child, seen, output);
    }
}

fn statement(cx: &Cx, stat: StatId, seen: &mut HashSet<ExprId>, output: &mut Vec<String>) {
    if let Some(list) = cx.ir[stat].exprents {
        for &expr in &cx.ir[list] {
            expression(cx, expr, seen, output);
        }
    }
    for &child in &cx.ir[stat].stats {
        statement(cx, child, seen, output);
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn generic_call_chains_infer_and_qualify_like_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let corpus = super::upstream_reference::Corpus::discover();
    let expected = corpus.run("GenericChainsReference", &[], scratch.path());
    let jdk = super::upstream_reference::jdk_home();
    let class_files = scratch.path().join("classes");
    let runtime = Arc::new(RuntimeImage::open(&jdk).unwrap());
    let mut actual = Vec::new();
    for explicit in [false, true] {
        actual.push(format!("explicit={}", u8::from(explicit)));
        let mut options = Options::default();
        options.explicit_generics = explicit;
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        context.add_space(runtime.clone(), false);
        context.add_file(&class_files, true).unwrap();
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let subject = cx.class_nodes.id("ChainSubject").unwrap();
        let mut qualified = Vec::new();
        process_class_methods(&mut cx, subject, |cx, class, method| {
            let Some(mut result) = defined_method(cx, class, method)? else {
                return Ok(None);
            };
            result.prepare_generic_chains(cx);
            if result.qualify_generic_chains(cx)? {
                qualified.push(method.name.as_str().to_owned());
            }
            Ok(Some(result))
        })
        .unwrap();
        qualified.sort();
        assert_eq!(
            qualified,
            [
                "classGenericOnly",
                "directLambda",
                "inheritedOwner",
                "overloadedReference",
                "sameFormal"
            ]
        );

        for (name, node) in cx.class_nodes.iter().collect::<BTreeMap<_, _>>() {
            if node.kind == ClassKind::Lambda {
                continue;
            }
            for method in &node.wrapper.as_ref().unwrap().methods {
                let Some(body) = method.body.as_ref().unwrap() else {
                    continue;
                };
                let mut rows = Vec::new();
                statement(&cx, body.root, &mut HashSet::new(), &mut rows);
                for row in rows {
                    actual.push(format!(
                        "{name}.{}{}\t{row}",
                        method.method.name, method.method.descriptor
                    ));
                }
            }
        }
    }
    assert_eq!(actual, expected.lines().collect::<Vec<_>>());
}
