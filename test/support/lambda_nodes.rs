use std::io::Write;

use rustc_hash::FxHashMap;
use vineflower_rs::engine::class_nodes::{ClassKind, ClassNodeId};
use vineflower_rs::engine::class_processor::prepare_class;
use vineflower_rs::engine::import_collector::get_short_name;
use vineflower_rs::engine::{Cx, Options};

use super::{load_context, upstream_reference::Corpus};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn prepared_lambda_nodes_match_upstream() {
    let corpus = Corpus::discover();
    let mut paths = tempfile::NamedTempFile::new().unwrap();
    for path in &corpus.classes {
        writeln!(paths, "{}", path.display()).unwrap();
    }
    let reference = corpus.run("LambdaReference", &[], paths.path());
    let mut expected = reference.lines();
    let mut count = 0;
    let mut lambdas = 0;
    let mut rejected = 0;
    for mode in ["default", "flat"] {
        let mut options = Options::default();
        options.decompile_inner = mode != "flat";
        let mut cx = load_context(&corpus, options);
        let mut roots: Vec<_> = cx
            .class_nodes
            .iter()
            .filter(|(_, node)| node.kind == ClassKind::Root)
            .map(|(name, _)| name.clone())
            .collect();
        roots.sort_unstable_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
        for name in roots {
            let root = cx.class_nodes.id(&name).unwrap();
            if let Err(error) = prepare_class(&mut cx, root) {
                let message = format!("{mode}\t{name}\trejected\t{error}");
                assert_eq!(Some(message.as_str()), expected.next());
                rejected += 1;
            }
            for (line, is_lambda) in snapshot(&mut cx, root, mode) {
                assert_eq!(Some(line.as_str()), expected.next());
                count += 1;
                lambdas += usize::from(is_lambda);
            }
        }
    }
    assert_eq!(expected.next(), None);
    eprintln!(
        "{count} prepared class and import records matched, including {lambdas} lambda nodes and {rejected} matching preparation rejections across both configurations"
    );
}

fn snapshot(cx: &mut Cx, root: ClassNodeId, mode: &str) -> Vec<(String, bool)> {
    // Use local object numbers. A duplicate bootstrap key may name several
    // node instances, and a nested lambda can occur under two owners.
    let mut nodes = vec![root];
    let mut ids = FxHashMap::default();
    ids.insert(root, 0);
    let mut pos = 0;
    while pos < nodes.len() {
        for &child in &cx.class_nodes[nodes[pos]].nested {
            ids.entry(child).or_insert_with(|| {
                nodes.push(child);
                nodes.len() - 1
            });
        }
        pos += 1;
    }
    let index = |id: Option<ClassNodeId>| {
        id.and_then(|id| ids.get(&id))
            .map_or_else(|| "-".to_owned(), ToString::to_string)
    };
    let name = cx.class_nodes[root].class.qualified_name.clone();
    let mut lines = Vec::new();
    for id in nodes {
        let node = &cx.class_nodes[id];
        let is_lambda = node.kind == ClassKind::Lambda;
        let key = if is_lambda {
            node.simple_name.as_ref().unwrap()
        } else {
            &node.class.qualified_name
        };
        let named = index(cx.class_nodes.id(key));
        let lambda = node.lambda.as_ref().map_or_else(
            || "-".into(),
            |l| {
                format!(
                    "{}|{}|{}|{}|{}|{}|{}|{}|{}",
                    l.method_name,
                    l.method_descriptor,
                    l.content_class_name,
                    l.content_method_name,
                    l.content_method_descriptor,
                    l.content_method_invocation_type,
                    l.content_method_key,
                    l.is_method_reference,
                    l.is_content_method_static
                )
            },
        );
        let owner = node
            .lambda
            .as_ref()
            .map(|l| l.content_class_name.replace('/', "."));
        let prefix = [
            mode.to_owned(),
            name.to_string(),
            index(Some(id)),
            format!("{:?}", node.kind).to_uppercase(),
            node.class.qualified_name.to_string(),
            node.simple_name.as_deref().unwrap_or("null").into(),
            node.enclosing_method.as_deref().unwrap_or("null").into(),
            node.anonymous_type
                .as_ref()
                .map_or_else(|| "null".into(), ToString::to_string),
            index(node.parent),
            itertools::join(node.nested.iter().map(|child| ids[child]), ","),
            named,
            lambda,
        ]
        .join("\t");
        let imported = owner.map_or_else(|| "-".to_owned(), |owner| get_short_name(cx, &owner));
        lines.push((format!("{prefix}\t{imported}"), is_lambda));
    }
    lines.push((
        format!(
            "{mode}\t{name}\timports\t[{}]",
            cx.imports.imports().join(", ")
        ),
        false,
    ));
    lines
}
