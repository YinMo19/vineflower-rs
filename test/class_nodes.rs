// SPDX-License-Identifier: Apache-2.0

use std::{fmt::Display, io::Write, sync::Arc};

#[path = "support/lambda_nodes.rs"]
mod lambda_nodes;
#[path = "support/upstream_reference.rs"]
mod upstream_reference;

use vineflower_rs::decompiler::exps::Expr;
use vineflower_rs::engine::{
    Cx, Options,
    class_nodes::{ClassKind, ClassNodeId, load_classes},
    counter_container::CounterContainer,
    import_collector::{ImportCollector, get_short_name_in_class_context},
};
use vineflower_rs::structs::{StructContext, single_file_context_source::SingleFileContextSource};
use vineflower_rs::types::VarType;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn loaded_class_nodes_and_imports_match_upstream() {
    let corpus = upstream_reference::Corpus::discover();
    let mut paths = tempfile::NamedTempFile::new().unwrap();
    for path in &corpus.classes {
        writeln!(paths, "{}", path.display()).unwrap();
    }
    let expected = corpus.run("ClassNodeReference", &[], paths.path());
    let mut records = Vec::new();
    for mode in ["default", "verify", "flat"] {
        let mut options = Options::default();
        options.verify_anonymous_classes = mode == "verify";
        options.decompile_inner = mode != "flat";
        let mut cx = load_context(&corpus, options);
        let mut roots: Vec<_> = cx
            .class_nodes
            .iter()
            .filter(|(_, n)| n.kind == ClassKind::Root)
            .map(|(name, _)| name.clone())
            .collect();
        roots.sort_unstable_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
        for name in roots {
            let id = cx.class_nodes.id(&name).unwrap();
            cx.imports =
                ImportCollector::for_root(&cx.struct_context, &cx.class_nodes, &cx.class_nodes[id]);
            snapshot(&mut cx, id, mode, &mut records);
            records.push(format!(
                "{mode}\timports\t{name}\t{}",
                list(cx.imports.imports())
            ));
        }
    }
    let expected: Vec<_> = expected.lines().collect();
    assert_eq!(
        records.len(),
        expected.len(),
        "class and import record count"
    );
    for (actual, reference) in records.iter().zip(expected) {
        assert_eq!(actual, reference);
    }
    eprintln!(
        "{} class discovery and import records matched over {} input paths",
        records.len(),
        corpus.classes.len()
    );
}

fn load_context(corpus: &upstream_reference::Corpus, options: Options) -> Cx {
    let options = Arc::new(options);
    let mut context = StructContext::new(options.clone(), None);
    for path in &corpus.classes {
        context.add_space(
            Arc::new(SingleFileContextSource::open(path, &options, None).unwrap()),
            true,
        );
    }
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

fn snapshot(cx: &mut Cx, id: ClassNodeId, mode: &str, records: &mut Vec<String>) {
    let node = &cx.class_nodes[id];
    let class = Arc::clone(&node.class);
    let name = &class.qualified_name;
    let mut owners: Vec<_> = node.enclosing_classes.iter().collect();
    owners.sort_unstable_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
    let nested = node.nested.clone();
    let details = [
        format!("{:?}", node.kind).to_uppercase(),
        node.access.to_string(),
        node.simple_name.as_deref().unwrap_or("null").to_string(),
        node.enclosing_method
            .as_deref()
            .unwrap_or("null")
            .to_string(),
        list(owners),
        node.parent.map_or_else(
            || "null".to_owned(),
            |parent| cx.class_nodes[parent].class.qualified_name.to_string(),
        ),
        list(
            nested
                .iter()
                .map(|&child| &cx.class_nodes[child].class.qualified_name),
        ),
        node.anonymous_type
            .as_ref()
            .map_or_else(|| "null".into(), ToString::to_string),
    ];
    cx.current_class_node = Some(name.clone());
    let alloc = Expr::new_allocation(
        cx,
        &mut CounterContainer::default(),
        VarType::from_signature_cl(&class.qualified_name, true),
        vec![],
        None,
    );
    let ty = Expr::expr_type(cx, alloc);

    let mut names = vec![class.qualified_name.clone()];
    names.extend(class.super_class.iter().map(|s| s.get_string().clone()));
    names.extend(class.interface_names.iter().cloned());
    if let Some(attr) = &class.attributes.inner_classes {
        names.extend(attr.entries.iter().map(|e| e.inner_name.clone()));
    }
    names.sort_unstable_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
    names.dedup();
    let resolved = names
        .iter()
        .map(|n| get_short_name_in_class_context(cx, &n.replace('/', ".")));
    records.push(format!(
        "{mode}\tnode\t{name}\t{}\t{ty}\t{}",
        details.join("\t"),
        list(resolved)
    ));
    for child in nested {
        snapshot(cx, child, mode, records);
    }
}

fn list(items: impl IntoIterator<Item = impl Display>) -> String {
    format!("[{}]", itertools::join(items, ", "))
}
