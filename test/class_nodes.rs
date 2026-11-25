// SPDX-License-Identifier: Apache-2.0

use std::{env, fmt::Display, fs, io::Write, path::Path, process::Command, sync::Arc};

#[path = "support/lambda_nodes.rs"]
mod lambda_nodes;
#[path = "support/upstream_reference.rs"]
mod upstream_reference;

use vineflower_rs::decompiler::exps::Expr;
use vineflower_rs::engine::{
    Cx, Options,
    class_nodes::{ClassKind, ClassNodeId, load_classes},
    context_source::{ContextSource, RuntimeImage},
    counter_container::CounterContainer,
    import_collector::{ImportCollector, get_short_name_in_class_context},
};
use vineflower_rs::structs::{StructContext, single_file_context_source::SingleFileContextSource};
use vineflower_rs::types::VarType;

#[test]
#[ignore = "requires a modular JDK 17 or later"]
fn runtime_image_entries_and_lookup_match_jrt() {
    let java_home = upstream_reference::jdk_home();
    let java_tool = |name| {
        java_home
            .join("bin")
            .join(format!("{name}{}", env::consts::EXE_SUFFIX))
    };
    let scratch = tempfile::tempdir().unwrap();
    let reference =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("test/support/RuntimeImageReference.java");
    let compilation = Command::new(java_tool("javac"))
        .args(["-d"])
        .arg(scratch.path())
        .arg(reference)
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    // Running a separately compiled class keeps the compiler's earlier
    // resource reads out of the JRT filesystem traversal.
    let reference = Command::new(java_tool("java"))
        .arg("-cp")
        .arg(scratch.path())
        .arg("RuntimeImageReference")
        .arg(&java_home)
        .arg(scratch.path())
        .output()
        .unwrap();
    assert!(
        reference.status.success(),
        "{}",
        String::from_utf8_lossy(&reference.stderr)
    );
    let reference = String::from_utf8(reference.stdout).unwrap();
    let runtime = Arc::new(RuntimeImage::open(&java_home).unwrap());
    let children = runtime.get_entries();
    assert!(children.classes.is_empty());
    assert!(children.directories.is_empty());
    assert!(children.others.is_empty());
    assert_eq!(runtime.get_input_stream("module-info.class").unwrap(), None);

    let mut expected = reference.lines();
    for module in &children.child_contexts {
        let name = module.get_name();
        assert_eq!(
            expected.next(),
            Some(format!("module\t{}", name.strip_prefix("module ").unwrap()).as_str())
        );
        let entries = module.get_entries();
        assert!(entries.child_contexts.is_empty());
        for class in entries.classes {
            assert_eq!(
                expected.next(),
                Some(format!("class\t{}", class.path()).as_str())
            );
        }
        for dir in entries.directories {
            assert_eq!(expected.next(), Some(format!("dir\t{dir}").as_str()));
        }
        for entry in entries.others {
            assert_eq!(
                expected.next(),
                Some(format!("other\t{}", entry.path()).as_str())
            );
        }
    }
    assert_eq!(expected.next(), None);

    let base = &children.child_contexts[0];
    let resource = base
        .get_input_stream("java/util/currency.data")
        .unwrap()
        .unwrap();
    assert_eq!(
        resource,
        fs::read(scratch.path().join("currency.data")).unwrap()
    );
    assert_eq!(base.get_input_stream("java/util").unwrap(), None);
    assert_eq!(base.get_input_stream("no-such-resource").unwrap(), None);

    let iterator = "java/util/ListIterator";
    let own_file = scratch.path().join("ListIterator.class");
    assert_eq!(
        base.get_class_bytes(iterator).unwrap().unwrap(),
        fs::read(&own_file).unwrap()
    );
    let options = Arc::new(Options::default());
    let mut context = StructContext::new(Arc::clone(&options), None);
    context.add_space(runtime.clone(), false);
    assert!(!context.get_class(iterator).unwrap().own);
    assert!(context.instance_of(iterator, "java/util/Iterator"));
    let descriptor = context.get_class("module-info").unwrap();
    assert_eq!(
        descriptor.attributes.module.as_ref().unwrap().module_name,
        "java.base"
    );

    let own = Arc::new(SingleFileContextSource::open(&own_file, &options, None).unwrap());
    for own_first in [true, false] {
        let mut context = StructContext::new(Arc::clone(&options), None);
        if own_first {
            context.add_space(own.clone(), true);
            context.add_space(runtime.clone(), false);
        } else {
            context.add_space(runtime.clone(), false);
            context.add_space(own.clone(), true);
        }
        assert!(context.get_class(iterator).unwrap().own);
    }
}

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

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn method_properties_match_upstream() {
    use vineflower_rs::structs::StructClass;
    use vineflower_rs::util::data_input::DataInputFullStream;

    let corpus = upstream_reference::Corpus::discover();
    let mut paths = tempfile::NamedTempFile::new().unwrap();
    let mut actual = Vec::new();
    let options = Options::default();
    for path in &corpus.classes {
        writeln!(paths, "{}", path.display()).unwrap();
        let bytes = std::fs::read(path).unwrap();
        let class =
            StructClass::create(&mut DataInputFullStream::new(&bytes), true, &options, None)
                .unwrap();
        for method in &class.methods {
            let key = method.to_string();
            let props = class.method_properties(&key).unwrap();
            let field = props.assert_field.as_ref().map_or("-", |f| f.name.as_str());
            actual.push(format!(
                "{}\t{key}\t{}\t{field}",
                class.qualified_name, props.is_synthetic_reference_lambda
            ));
        }
    }
    let reference = corpus.run("MethodPropertiesReference", &[], paths.path());
    assert_eq!(actual.len(), reference.lines().count());
    for (actual, expected) in actual.iter().zip(reference.lines()) {
        assert_eq!(actual, expected);
    }
    eprintln!(
        "{} bytecode-derived method properties matched",
        actual.len()
    );
}
