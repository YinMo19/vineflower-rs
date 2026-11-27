use super::*;
use vineflower_rs::engine::{class_processor::initialize_java_wrappers, nested};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn nested_captures_follow_declared_and_invoked_constructors() {
    let scratch = tempfile::tempdir().unwrap();
    let reference = upstream_reference::Corpus::discover().run(
        "NestedCapturesReference",
        &["WrapperStages", "NestedCorpusReference"],
        scratch.path(),
    );
    let mut rows = Vec::new();
    for debug in [false, true] {
        for anonymous in [false, true] {
            rows.push(format!(
                "options {} {}",
                u8::from(debug),
                u8::from(anonymous)
            ));
            let mut options = Options::default();
            options.use_lvt_names = debug;
            options.lambda_to_anonymous_class = anonymous;
            let mut cx = registered(&scratch.path().join("classes"), Arc::new(options));
            let root = cx.class_nodes.id("CaptureHost").unwrap();
            initialize_java_wrappers(&mut cx, root).unwrap();
            nested::process_class(&mut cx, root).unwrap();
            snapshot(&cx, root, &mut rows);
        }
    }
    assert!(rows.iter().any(|row| row.starts_with("field val$")));
    assert!(
        rows.iter()
            .any(|row| row.starts_with("var ") && row.contains('@'))
    );
    assert_eq!(rows, reference.lines().collect::<Vec<_>>());
}

fn registered(group: &Path, options: Arc<Options>) -> Cx {
    let mut context = StructContext::new(options.clone(), None);
    context.add_file(group, true).unwrap();
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    cx
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn nested_class_processing_matches_upstream() {
    use std::collections::BTreeSet;
    let corpus = upstream_reference::Corpus::discover();
    let root = corpus.root.canonicalize().unwrap();
    let groups: BTreeSet<_> = if root.file_name().is_some_and(|name| name == "classes") {
        corpus
            .classes
            .iter()
            .map(|file| {
                root.join(
                    file.strip_prefix(&root)
                        .unwrap()
                        .components()
                        .next()
                        .unwrap(),
                )
            })
            .collect()
    } else {
        BTreeSet::from([root])
    };
    let scratch = tempfile::tempdir().unwrap();
    let manifest = scratch.path().join("groups");
    fs::write(
        &manifest,
        groups
            .iter()
            .map(|p| p.to_str().unwrap())
            .collect::<Vec<_>>()
            .join("\n"),
    )
    .unwrap();
    let reference = corpus.run("NestedCorpusReference", &["WrapperStages"], &manifest);
    let mut rows = Vec::new();
    let options = Arc::new(Options::default());
    for group in groups {
        let mut cx = registered(&group, options.clone());
        let mut roots: Vec<_> = cx
            .class_nodes
            .iter()
            .filter(|(_, node)| {
                node.kind == ClassKind::Root
                    && (!node.nested.is_empty()
                        || node.class.attributes.bootstrap_methods.is_some())
            })
            .map(|(name, _)| name.clone())
            .collect();
        roots.sort();
        for name in roots {
            let root = cx.class_nodes.id(&name).unwrap();
            rows.push(format!("root {} {name}", group.display()));
            if let Err(error) = initialize_java_wrappers(&mut cx, root) {
                rows.push(format!("prepare error {error}"));
                continue;
            }
            vineflower_rs::engine::nested::process_class(&mut cx, root).unwrap();
            snapshot(&cx, root, &mut rows);
        }
    }
    let mut owner = "";
    for (n, (rust, java)) in rows.iter().zip(reference.lines()).enumerate() {
        if java.starts_with("root ") {
            owner = java
        }
        assert_eq!(rust, java, "{owner}, row {}", n + 1);
    }
    assert_eq!(rows.len(), reference.lines().count());
}

fn snapshot(cx: &Cx, id: ClassNodeId, rows: &mut Vec<String>) {
    use vineflower_rs::decompiler::vars::versions::FinalType;
    use vineflower_rs::engine::counter_container::{EXPRESSION_COUNTER, VAR_COUNTER};
    let node = &cx.class_nodes[id];
    rows.push(format!(
        "class {} {} {}",
        format!("{:?}", node.kind).to_uppercase(),
        node.simple_name.as_deref().unwrap_or("null"),
        node.enclosing_method.as_deref().unwrap_or("null")
    ));
    if let Some(wrapper) = &node.wrapper {
        let mut hidden: Vec<_> = node.hidden_members.iter().collect();
        hidden.sort();
        rows.extend(hidden.into_iter().map(|key| format!("hide {key}")));
        if let Some(expr) = node.super_invocation {
            rows.push(format!("super {}", cx.ir[expr].id));
        }
        for (key, v) in node
            .fields_to_vars
            .iter()
            .collect::<std::collections::BTreeMap<_, _>>()
        {
            rows.push(format!("field {key} {},{}", v.var, v.version));
        }
        for method in &wrapper.methods {
            rows.push(format!("method {}", method.method));
            let Ok(Some(body)) = &method.body else {
                rows.push(
                    if method.body.is_err() {
                        "failed"
                    } else {
                        "no code"
                    }
                    .to_owned(),
                );
                continue;
            };
            rows.push(format!(
                "counters {} {}",
                body.counters.get_counter(VAR_COUNTER),
                body.counters.get_counter(EXPRESSION_COUNTER)
            ));
            if let Some(mask) = &method.synthetic_parameters {
                rows.push(format!(
                    "params {}",
                    mask.iter()
                        .map(|v| v
                            .map_or_else(|| "-".to_owned(), |p| format!("{},{}", p.var, p.version)))
                        .collect::<Vec<_>>()
                        .join("/")
                ));
            }
            let mut outer: Vec<_> = method.outer_var_names.iter().collect();
            outer.sort();
            rows.extend(
                outer
                    .into_iter()
                    .map(|n| format!("outer {}", n.as_deref().unwrap_or("null"))),
            );
            let vars = &cx.ir[method.variables];
            if vars.nested_processed {
                rows.push("lambda bindings".to_owned());
            }
            let mut names: Vec<_> = vars.names.iter().collect();
            names.sort_by_key(|(p, _)| (p.var, p.version));
            for (p, name) in names {
                let fin = match vars.versions.final_vars.get(p).unwrap_or(&FinalType::Final) {
                    FinalType::Final => "FINAL",
                    FinalType::ExplicitFinal => "EXPLICIT_FINAL",
                    FinalType::NonFinal => "NON_FINAL",
                };
                let source = vars
                    .sources
                    .get(p)
                    .map(|(method, v)| format!("{method}@{},{}", v.var, v.version));
                rows.push(format!(
                    "var {},{} {} {fin} {} {} {} {}",
                    p.var,
                    p.version,
                    name.as_deref().unwrap_or("null"),
                    vars.this_vars.get(p).map_or("null", |s| s.as_str()),
                    vars.inherited_names.contains_key(p),
                    vars.external_vars.contains(p),
                    format!(
                        "{} {}",
                        source.as_deref().unwrap_or("-"),
                        vars.local_variables
                            .get(p)
                            .map_or_else(|| "null".to_owned(), |lv| lv.to_string())
                    )
                ));
            }
            expression_rows(cx, body.root, method.variables, rows);
        }
    }
    for &child in &node.nested {
        snapshot(cx, child, rows);
    }
}

fn expression_rows(
    cx: &Cx,
    stat: vineflower_rs::decompiler::ir::StatId,
    vars: vineflower_rs::decompiler::ir::VarProcessorId,
    rows: &mut Vec<String>,
) {
    let s = &cx.ir[stat];
    let roots = s
        .exprents
        .map(|list| cx.ir[list].clone())
        .unwrap_or_else(|| stat.stat_exprents(&cx.ir));
    for &expr in s.var_definitions.iter().chain(&roots) {
        for e in Expr::all_exprents(&cx.ir, expr, true, true) {
            if let vineflower_rs::decompiler::exps::ExprKind::Variable(v) = &cx.ir[e].kind
                && (v.class_definition || cx.ir[vars].external_vars.contains(&v.pair()))
            {
                rows.push(format!(
                    "use {} {} {},{} {} {} {}",
                    s.id,
                    cx.ir[e].id,
                    v.index,
                    v.version,
                    v.class_definition,
                    Expr::expr_type(cx, e),
                    v.lvt
                        .as_ref()
                        .map_or_else(|| "null".to_owned(), |lv| lv.to_string())
                ));
            }
        }
    }
    for &child in &s.stats {
        expression_rows(cx, child, vars, rows);
    }
}
