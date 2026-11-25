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
use vineflower_rs::structs::StructContext;
use vineflower_rs::types::VarType;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn class_wrappers_publish_declared_methods_in_order() {
    use vineflower_rs::engine::{
        class_processor::process_class_methods, method_processor::after_main_method,
    };

    fn dump_cases(cx: &Cx, stat: vineflower_rs::decompiler::ir::StatId, rows: &mut Vec<String>) {
        use vineflower_rs::decompiler::{
            exps::{ConstantValue, ExprKind},
            stats::StatementKind,
        };
        if let StatementKind::Switch(switch) = &cx.ir[stat].kind {
            for case in &switch.cases {
                for value in &case.values {
                    let label = match value.map(|id| &cx.ir[id].kind) {
                        Some(ExprKind::Field(field)) => {
                            format!("field {}.{}", field.classname.as_ref().unwrap(), field.name)
                        }
                        Some(ExprKind::Constant {
                            value: ConstantValue::String(s),
                            ..
                        }) => format!("constant {}", s.as_utf8_lossy()),
                        Some(ExprKind::Constant {
                            value: ConstantValue::Integer(n),
                            ..
                        }) => format!("constant {n}"),
                        None => "default".to_owned(),
                        _ => panic!("Unexpected case label"),
                    };
                    rows.push(format!("case\t{label}"));
                }
            }
        }
        for &child in &cx.ir[stat].stats {
            dump_cases(cx, child, rows);
        }
    }

    let scratch = tempfile::tempdir().unwrap();
    let corpus = upstream_reference::Corpus::discover();
    let reference = corpus.run("ClassWrappersReference", &[], scratch.path());
    let options = Arc::new(Options::default());
    let mut context = StructContext::new(options.clone(), None);
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
    let root = cx.class_nodes.id("WrapperSubject").unwrap();

    process_class_methods(&mut cx, root, |cx, class, method| {
        let id = cx.class_nodes.id(&class.qualified_name).unwrap();
        let order = cx.class_nodes.wrapper_order(root);
        let current = order.iter().position(|&node| node == id).unwrap();
        for (index, &node) in order.iter().enumerate() {
            assert_eq!(cx.class_nodes[node].wrapper.is_some(), index < current);
        }
        after_main_method(cx, class, method)
    })
    .unwrap();

    let classes: std::collections::BTreeMap<_, _> = cx.class_nodes.iter().collect();
    let mut rows = Vec::new();
    for (name, class) in classes {
        for method in &class.wrapper.as_ref().unwrap().methods {
            let state = match &method.body {
                Ok(Some(_)) => "code",
                Ok(None) => "no-code",
                Err(_) => "failed",
            };
            rows.push(format!(
                "{name}\t{}\t{}\t{state}",
                method.method.name, method.method.descriptor
            ));
            if let Ok(Some(body)) = &method.body {
                dump_cases(&cx, body.root, &mut rows);
            } else if let Ok(None) = &method.body {
                let variables = &cx.ir[method.variables];
                for pair in &variables.params {
                    rows.push(format!(
                        "param\t{}\t{}\t{}",
                        pair.var,
                        variables
                            .names
                            .get(pair)
                            .and_then(Option::as_deref)
                            .unwrap_or("null"),
                        variables
                            .this_vars
                            .get(pair)
                            .map_or("-", |name| name.as_str()),
                    ));
                }
            }
        }
    }
    assert!(
        rows.iter()
            .any(|row| row == "case\tfield WrapperSubject$Kind.LEFT")
    );
    assert!(rows.iter().any(|row| row == "case\tconstant Aa"));
    assert_eq!(rows, reference.lines().collect::<Vec<_>>());
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn file_and_archive_registration_matches_upstream() {
    fn context() -> StructContext {
        StructContext::new(Arc::new(Options::default()), None)
    }

    fn dump(label: &str, context: &StructContext, rows: &mut Vec<String>) {
        let entry = |kind, entry: &vineflower_rs::engine::context_source::Entry| {
            format!(
                "{kind}\t{}\t{}\t{}",
                entry.base_path,
                entry.multirelease,
                entry.path()
            )
        };
        rows.push(label.to_owned());
        for unit in context.get_units() {
            rows.push(format!(
                "unit\t{}\t{}\t{}",
                unit.own,
                unit.root,
                unit.get_name()
            ));
            let raw = unit.source.get_entries();
            rows.extend(raw.classes.iter().map(|file| entry("raw-class", file)));
            rows.extend(
                unit.class_entries
                    .iter()
                    .map(|class| format!("class\t{class}")),
            );
            rows.extend(unit.dir_entries.iter().map(|dir| format!("dir\t{dir}")));
            rows.extend(unit.other_entries.iter().map(|file| entry("other", file)));
        }
    }

    fn resource(context: &StructContext, path: &str) -> String {
        let bytes = context.get_units()[0]
            .source
            .get_input_stream(path)
            .unwrap()
            .unwrap();
        String::from_utf8(bytes).unwrap()
    }

    let scratch = tempfile::tempdir().unwrap();
    let corpus = upstream_reference::Corpus::discover();
    let reference = corpus.run(
        "InputSourcesReference",
        &["AnnotationIdsReference"],
        scratch.path(),
    );
    let mut rows = Vec::new();

    let mut directory = context();
    let folder = scratch.path().join("folder");
    directory.add_file(&folder, true).unwrap();
    dump("folder", &directory, &mut rows);
    rows.push(format!(
        "directory-resource\t{}",
        resource(&directory, "/assets/note.txt")
    ));
    for path in ["assets", "absent"] {
        assert_eq!(
            directory.get_units()[0]
                .source
                .get_input_stream(path)
                .unwrap(),
            None
        );
    }
    assert!(!directory.has_class("InputAddedFixture"));
    fs::copy(
        scratch.path().join("InputAddedFixture.class"),
        folder.join("InputAddedFixture.class"),
    )
    .unwrap();
    directory.try_reload_context(None).unwrap();
    dump("reloaded", &directory, &mut rows);
    assert!(directory.get_class("InputAddedFixture").unwrap().own);

    let mut archive = context();
    for (path, own) in [
        ("archive.data", false),
        ("long-comment.data", true),
        ("empty.data", true),
        ("missing.jar", true),
    ] {
        archive.add_file(&scratch.path().join(path), own).unwrap();
    }
    dump("archives", &archive, &mut rows);
    rows.push(format!(
        "duplicate-resource\t{}",
        resource(&archive, "copy-a.txt")
    ));
    rows.push(format!(
        "utf8-resource\t{}",
        resource(&archive, "unicodé.txt")
    ));
    for name in ["alpha.txt", "beta.txt"] {
        rows.push(format!(
            "raw-name-resource\t{name}\t{}",
            resource(&archive, name)
        ));
    }
    for path in ["empty/", "absent"] {
        assert_eq!(
            archive.get_units()[0]
                .source
                .get_input_stream(path)
                .unwrap(),
            None
        );
    }
    let class = archive.get_class("InputNestedFixture").unwrap();
    rows.push(format!("archive-class\t{}", class.qualified_name));
    assert!(!class.own);

    let mut single = context();
    single
        .add_file(&scratch.path().join("Alias.class"), true)
        .unwrap();
    dump("renamed", &single, &mut rows);
    let class = single.get_class("IdDecor").unwrap();
    let ids: Vec<_> = class
        .attributes
        .runtime_visible_annotations
        .as_ref()
        .unwrap()
        .annotations
        .iter()
        .map(|annotation| annotation.id)
        .collect();
    rows.push(format!("annotation-ids\t{ids:?}"));

    for bad in ["broken.zip", "broken-folder", "broken.class"] {
        let error = single
            .add_file(&scratch.path().join(bad), true)
            .unwrap_err();
        let kind = if bad.ends_with(".class") {
            "file"
        } else {
            "archive"
        };
        assert!(
            error.to_string().starts_with(&format!("Invalid {kind} ")),
            "{error}"
        );
        assert_eq!(single.get_units().len(), 1);
        rows.push(format!("rejected\t{bad}"));
    }
    fs::copy(
        scratch.path().join("broken.zip"),
        folder.join("invalid.zip"),
    )
    .unwrap();
    assert!(directory.try_reload_context(None).is_err());
    assert!(directory.get_class("InputAddedFixture").unwrap().own);

    let expected: Vec<_> = reference.lines().collect();
    assert_eq!(rows.len(), expected.len());
    for (actual, expected) in rows.iter().zip(expected) {
        assert_eq!(actual, expected);
    }
}

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

    for own_first in [true, false] {
        let mut context = StructContext::new(Arc::clone(&options), None);
        if own_first {
            context.add_file(&own_file, true).unwrap();
            context.add_space(runtime.clone(), false);
        } else {
            context.add_space(runtime.clone(), false);
            context.add_file(&own_file, true).unwrap();
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
        context.add_file(path, true).unwrap();
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

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn annotation_expression_ids_match_upstream() {
    use vineflower_rs::structs::attr::{AnnotationData, AnnotationElement, ElementValue};
    use vineflower_rs::structs::{Attributes, StructClass};
    use vineflower_rs::util::data_input::DataInputFullStream;

    fn collect_annotation(annotation: &AnnotationData, ids: &mut Vec<i32>) {
        for parameter in &annotation.par_values {
            collect_element(parameter, ids);
        }
        ids.push(annotation.id);
    }

    fn collect_element(element: &AnnotationElement, ids: &mut Vec<i32>) {
        match &element.value {
            ElementValue::Annotation(annotation) => {
                assert_eq!(element.id, annotation.id);
                collect_annotation(annotation, ids);
                return;
            }
            ElementValue::Array(children) => {
                for child in children {
                    collect_element(child, ids);
                }
            }
            _ => {}
        }
        ids.push(element.id);
    }

    fn collect(attrs: &Attributes, ids: &mut Vec<i32>) {
        for attribute in [
            &attrs.runtime_visible_annotations,
            &attrs.runtime_invisible_annotations,
        ]
        .into_iter()
        .flatten()
        {
            for annotation in &attribute.annotations {
                collect_annotation(annotation, ids);
            }
        }
        for attribute in [
            &attrs.runtime_visible_type_annotations,
            &attrs.runtime_invisible_type_annotations,
        ]
        .into_iter()
        .flatten()
        {
            for annotation in &attribute.annotations {
                collect_annotation(&annotation.annotation, ids);
            }
        }
        for attribute in [
            &attrs.runtime_visible_parameter_annotations,
            &attrs.runtime_invisible_parameter_annotations,
        ]
        .into_iter()
        .flatten()
        {
            for annotation in attribute.param_annotations.iter().flatten() {
                collect_annotation(annotation, ids);
            }
        }
        if let Some(default) = &attrs.annotation_default {
            collect_element(&default.default_value, ids);
        }
    }

    let scratch = tempfile::tempdir().unwrap();
    let corpus = upstream_reference::Corpus::discover();
    let expected = corpus.run("AnnotationIdsReference", &[], scratch.path());
    let actual: Vec<_> = ["IdDecor", "AnnotationIdFixture"]
        .into_iter()
        .map(|name| {
            let bytes = fs::read(scratch.path().join(format!("{name}.class"))).unwrap();
            let class = StructClass::create(
                &mut DataInputFullStream::new(&bytes),
                true,
                &Options::default(),
                None,
            )
            .unwrap();
            let mut ids = Vec::new();
            for field in &class.fields {
                collect(&field.attributes, &mut ids);
            }
            for method in &class.methods {
                collect(&method.attributes, &mut ids);
            }
            collect(&class.attributes, &mut ids);
            for component in class.get_record_components().into_iter().flatten() {
                collect(&component.attributes, &mut ids);
            }
            format!("{ids:?}")
        })
        .collect();
    assert_eq!(actual, expected.lines().collect::<Vec<_>>());
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn variable_names_and_debug_tables_match_published_method_wrappers() {
    use vineflower_rs::engine::{
        class_processor::process_class_methods, method_processor::defined_method,
    };
    let scratch = tempfile::tempdir().unwrap();
    let reference =
        upstream_reference::Corpus::discover().run("VariableNamesReference", &[], scratch.path());
    let mut rows = Vec::new();
    for provider in ["identity", "jad", "tiny"] {
        for debug in [false, true] {
            let mut options = Options::default();
            options.rename_parameters = true;
            options.use_lvt_names = debug;
            options.variable_renaming = (provider != "identity").then(|| provider.to_owned());
            let options = Arc::new(options);
            let mut classes = StructContext::new(options.clone(), None);
            classes
                .add_file(&scratch.path().join("classes"), true)
                .unwrap();
            let mut cx = Cx::new(Arc::new(classes));
            cx.class_nodes = load_classes(
                &cx.struct_context,
                &options,
                |_| true,
                |_| true,
                |_, _| None,
            );
            let root = cx.class_nodes.id("Names").unwrap();
            process_class_methods(&mut cx, root, defined_method).unwrap();
            rows.push(format!("{provider} {}", i32::from(debug)));
            for (name, node) in cx
                .class_nodes
                .iter()
                .collect::<std::collections::BTreeMap<_, _>>()
            {
                if node.kind == ClassKind::Lambda {
                    continue;
                }
                for wrapper in &node.wrapper.as_ref().unwrap().methods {
                    rows.push(format!("{name} {}", wrapper.method));
                    if let Err(error) = &wrapper.body {
                        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
                        rows.push(error.to_string());
                        continue;
                    }
                    let vars = &cx.ir[wrapper.variables];
                    let mut pairs: Vec<_> = vars.names.keys().copied().collect();
                    pairs.sort_unstable();
                    for pair in pairs {
                        rows.push(format!(
                            "{} {} {} {} {}",
                            pair.var,
                            pair.version,
                            vars.names
                                .get(&pair)
                                .and_then(Option::as_deref)
                                .unwrap_or("null"),
                            vars.local_variables
                                .get(&pair)
                                .map_or("-", |lvt| lvt.get_name().as_str()),
                            vars.clashing_names
                                .get(&pair)
                                .map_or("-", |name| name.as_str())
                        ));
                    }
                }
            }
        }
    }
    assert_eq!(rows, reference.lines().collect::<Vec<_>>());
}
