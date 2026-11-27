use std::{
    collections::{BTreeMap, HashMap},
    sync::Arc,
};
use vineflower_rs::{
    decompiler::{
        exps::{ConstantValue, Expr, ExprKind},
        ir::{ExprId, Ir},
    },
    engine::{
        Cx, Options,
        class_nodes::{ClassKind, load_classes},
        class_processor::process_class,
        context_source::RuntimeImage,
        counter_container::{EXPRESSION_COUNTER, VAR_COUNTER},
    },
    structs::StructContext,
};
fn expr(ir: &Ir, id: ExprId, aliases: &mut HashMap<ExprId, usize>) -> String {
    if let Some(alias) = aliases.get(&id) {
        return format!("@{alias}");
    }
    let index = aliases.len();
    aliases.insert(id, index);
    let e = &ir[id];
    let data = match &e.kind {
        ExprKind::Field(f) => format!(
            "FIELD:{}.{}{}:{}",
            f.classname.as_deref().unwrap_or("null"),
            f.name,
            f.descriptor.descriptor_string,
            f.is_static()
        ),
        ExprKind::Invocation(i) => format!(
            "INVOCATION:{}.{}{}:{}",
            i.classname.as_deref().unwrap_or("null"),
            i.name,
            i.string_descriptor(),
            i.is_static
        ),
        ExprKind::Function { op, .. } => format!("FUNCTION:{}", format!("{op:?}").to_uppercase()),
        ExprKind::Variable(v) => format!("VAR:{},{}", v.index, v.version),
        ExprKind::Exit { kind, .. } => format!("EXIT:{}", format!("{kind:?}").to_uppercase()),
        ExprKind::Constant { value, .. } => format!(
            "CONST:{}",
            match value {
                ConstantValue::Integer(x) => x.to_string(),
                ConstantValue::Long(x) => x.to_string(),
                ConstantValue::Float(x) => x.to_string(),
                ConstantValue::Double(x) => x.to_string(),
                ConstantValue::Null => "null".to_owned(),
                ConstantValue::String(x) => x.as_utf8_lossy().to_string(),
            }
        ),
        ExprKind::Assignment { .. } => "ASSIGNMENT".to_owned(),
        ExprKind::New { .. } => "NEW".to_owned(),
        _ => panic!("unexpected expression: {:?}", e.kind),
    };
    let mut children = Vec::new();
    for child in Expr::children(ir, id) {
        children.push(expr(ir, child, aliases));
    }
    let offsets = e
        .bytecode
        .as_ref()
        .map(|offsets| {
            format!(
                "{{{}}}",
                offsets
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .unwrap_or("null".into());
    format!("{index}#{}#{data}#{offsets}[{}]", e.id, children.join("|"))
}
fn sequence<I: IntoIterator<Item = String>>(iter: I) -> String {
    format!("[{}]", iter.into_iter().collect::<Vec<_>>().join(", "))
}
fn option(s: Option<&str>) -> &str {
    s.unwrap_or("null")
}
fn dump(cx: &mut Cx, output: &mut Vec<String>) {
    let classes = cx
        .class_nodes
        .iter()
        .map(|(name, _)| (name.clone(), cx.class_nodes.id(name).unwrap()))
        .collect::<BTreeMap<_, _>>();
    for (name, node) in classes {
        let class = &mut cx.class_nodes[node];
        if class.kind == ClassKind::Lambda {
            continue;
        }
        let mut hidden = class.hidden_members.iter().cloned().collect::<Vec<_>>();
        hidden.sort();
        output.push(format!("{name} hidden={}", sequence(hidden)));
        for method in &mut class.wrapper.as_mut().unwrap().methods {
            let Some(body) = method
                .body
                .as_mut()
                .unwrap_or_else(|e| panic!("{} {e}", method.method))
            else {
                continue;
            };
            let proc = &cx.ir[method.variables];
            let vars = proc
                .names
                .iter()
                .map(|(p, n)| (format!("{},{}", p.var, p.version), option(n.as_deref())))
                .collect::<BTreeMap<_, _>>();
            let inherited = proc
                .inherited_names
                .iter()
                .map(|(p, n)| (format!("{},{}", p.var, p.version), option(n.as_deref())))
                .collect::<BTreeMap<_, _>>();
            let mut outer = method
                .outer_var_names
                .iter()
                .map(|n| option(n.as_deref()).to_owned())
                .collect::<Vec<_>>();
            outer.sort();
            let mut external = proc
                .external_vars
                .iter()
                .map(|p| format!("{},{}", p.var, p.version))
                .collect::<Vec<_>>();
            external.sort();
            let format_map = |m: BTreeMap<String, &str>| {
                format!(
                    "{{{}}}",
                    m.iter()
                        .map(|(p, n)| format!("{p}={n}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            output.push(format!(
                "{}{} counters={},{} vars={} outer={} inherited={} external={}",
                method.method.name,
                method.method.descriptor,
                body.counters.get_counter(EXPRESSION_COUNTER),
                body.counters.get_counter(VAR_COUNTER),
                format_map(vars),
                sequence(outer),
                format_map(inherited),
                sequence(external)
            ));
            let graph = body.graph(&mut cx.ir);
            let mut aliases = HashMap::new();
            for id in graph.regular_breadth_first() {
                let node = &graph[id];
                let line = cx.ir[node.exprents]
                    .iter()
                    .map(|&id| expr(&cx.ir, id, &mut aliases))
                    .collect::<Vec<_>>()
                    .join(";");
                output.push(format!("{} {line}", node.id));
            }
        }
    }
}
#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn nested_member_access_matches_upstream_for_javac_accessors() {
    let scratch = tempfile::tempdir().unwrap();
    let expected = super::upstream_reference::Corpus::discover().run(
        "NestedMemberAccessReference",
        &[],
        scratch.path(),
    );
    let runtime = Arc::new(RuntimeImage::open(&super::upstream_reference::jdk_home()).unwrap());
    let mut actual = Vec::new();
    let profiles = [
        ("AccessSubject", 8, false),
        ("AccessSubject", 8, true),
        ("AccessSubject", 17, false),
        ("AccessSubject", 17, true),
        ("AliasSubject", 17, true),
    ];
    for (subject, release, synthetic_not_set) in profiles {
        actual.push(format!(
            "{subject} {release} {}",
            u8::from(synthetic_not_set)
        ));
        let mut options = Options::default();
        options.synthetic_not_set = synthetic_not_set;
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        context.add_space(runtime.clone(), false);
        context
            .add_file(&scratch.path().join(format!("{subject}-{release}")), true)
            .unwrap();
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let root = cx.class_nodes.id(subject).unwrap();
        process_class(&mut cx, root).unwrap();
        let first = actual.len();
        dump(&mut cx, &mut actual);
        let rows = &actual[first..];
        let hidden_accessors = rows
            .iter()
            .filter(|row| row.contains(" hidden="))
            .map(|row| row.matches("access$").count())
            .sum::<usize>();
        assert_eq!(hidden_accessors, if release == 8 { 12 } else { 0 });
        if release == 8 {
            let nested = rows
                .iter()
                .position(|row| row.starts_with("nested("))
                .unwrap();
            assert_eq!(
                rows[nested + 1]
                    .matches("FIELD:AccessSubject.instance")
                    .count(),
                if synthetic_not_set { 2 } else { 0 }
            );
        }
        if subject == "AliasSubject" {
            let alias = rows
                .iter()
                .find(|row| row.starts_with("copyAlias("))
                .unwrap();
            assert!(alias.contains("capturedx") && alias.contains("outer=[captured]"));
        }
    }
    assert_eq!(actual, expected.lines().collect::<Vec<_>>());
}
