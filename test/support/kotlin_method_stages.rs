// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::{
    REFERENCE_HELPERS, control_flow_snapshot, expression_snapshot, stack_snapshot,
    structure_snapshot_with_edges, upstream_reference,
};
use vineflower_rs::engine::{
    Cx, Options,
    class_nodes::{ClassKind, load_classes},
    class_processor::process_class_methods,
    context_source::RuntimeImage,
};
use vineflower_rs::kotlin::passes::defined_method;
use vineflower_rs::structs::StructContext;

const MODERN: &[&str] = &[
    "TestDestructors",
    "TestFunVarargs",
    "TestNonInlineLambda",
    "TestSynchronized",
    "TestTryReturn",
    "TestWhenBoolean",
];

pub(super) fn check() {
    let fixture_root = upstream_reference::upstream_root().join("plugins/kotlin/testData/classes");
    let runtime = upstream_reference::jdk_home();
    let groups = [
        ("kt", MODERN, "", true),
        ("ktold", &["TestClassicStringInterpolation"][..], "", true),
        ("kt", MODERN, runtime.to_str().unwrap(), false),
    ];

    let mut input = tempfile::NamedTempFile::new().unwrap();
    let mut rust = BTreeMap::new();
    for (index, (version, names, runtime, configured)) in groups.into_iter().enumerate() {
        let paths = fixture_files(&fixture_root.join(version).join("pkg"), names);
        let configured = u8::from(configured);
        write!(input, "{index}\t{runtime}\t{configured}").unwrap();
        for path in &paths {
            write!(input, "\t{}", path.display()).unwrap();
        }
        writeln!(input).unwrap();
        snapshot_group(index, &paths, runtime, configured == 1, &mut rust);
    }

    let corpus = upstream_reference::Corpus::discover();
    let helpers: Vec<_> = REFERENCE_HELPERS
        .iter()
        .copied()
        .chain(["ControlFlowReference", "StructureReference"])
        .collect();
    let reference = corpus.run_with_kotlin("KotlinMethodStagesReference", &helpers, input.path());
    let java: BTreeMap<_, _> = reference
        .lines()
        .map(|line| {
            let separator = line.match_indices('\t').nth(2).unwrap().0;
            line.split_at(separator + 1)
        })
        .collect();
    assert!(!java.is_empty(), "Kotlin plugin did not run");
    assert!(
        java.keys().copied().eq(rust.keys().map(String::as_str)),
        "Kotlin method sets differ"
    );
    for (key, expected) in java {
        assert_eq!(rust[key], expected, "Kotlin SetVarDefinitions for {key}");
    }
}

fn fixture_files(package: &Path, names: &[&str]) -> Vec<PathBuf> {
    let mut files: Vec<_> = fs::read_dir(package)
        .unwrap_or_else(|error| panic!("reading {}: {error}", package.display()))
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension().is_some_and(|ext| ext == "class")
                && path
                    .file_stem()
                    .and_then(|stem| stem.to_str())
                    .is_some_and(|stem| {
                        names.iter().any(|name| {
                            stem == *name
                                || stem
                                    .strip_prefix(name)
                                    .is_some_and(|tail| tail.starts_with('$'))
                        })
                    })
        })
        .collect();
    files.sort_unstable();
    for name in names {
        assert!(
            files.contains(&package.join(format!("{name}.class"))),
            "missing Kotlin fixture {name}"
        );
    }
    files
}

fn snapshot_group(
    group: usize,
    paths: &[PathBuf],
    runtime: &str,
    configured: bool,
    rows: &mut BTreeMap<String, String>,
) {
    let mut options = Options::default();
    options.include_runtime = runtime.to_owned();
    options.thread_count = 1;
    options.remove_synthetic = false;
    options.ignore_invalid_bytecode = true;
    options.verify_anonymous_classes = true;
    options.unit_test_mode = true;
    options.keep_literals = true;
    options.dump_exception_on_error = false;
    options.remove_empty_try_catch = configured;
    options.ensure_synchronized_monitors = configured;
    options.incorporate_returns = configured;
    let options = Arc::new(options);

    let mut context = StructContext::new(Arc::clone(&options), None);
    if !runtime.is_empty() {
        context.add_space(
            Arc::new(RuntimeImage::open(Path::new(runtime)).unwrap()),
            false,
        );
    }
    for path in paths {
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
    let roots: BTreeMap<_, _> = cx
        .class_nodes
        .iter()
        .filter(|(_, node)| node.kind == ClassKind::Root)
        .map(|(name, _)| (name.clone(), cx.class_nodes.id(name).unwrap()))
        .collect();
    let mut failure = None;
    for root in roots.into_values() {
        process_class_methods(&mut cx, root, |cx, class, method| {
            let key = format!(
                "{group}\t{}\t{}{}\t",
                class.qualified_name, method.name, method.descriptor
            );
            let result = match defined_method(cx, class, method) {
                Ok(result) => result,
                Err(error) => {
                    failure = Some(format!("{key}{error}"));
                    return Err(error);
                }
            };
            if let Some(result) = &result {
                let root = result.root;
                let flow = &result.flow;
                let cfg = control_flow_snapshot::snapshot(&cx.ir, &flow.graph, false);
                let tree = structure_snapshot_with_edges(cx, root, &flow.counters, true, true);
                let exprs = expression_snapshot::snapshot_details(
                    cx,
                    root,
                    &flow.counters,
                    expression_snapshot::Detail::VariableDefinitions,
                );
                let vars = &cx.ir[flow.variables];
                let mut versions = stack_snapshot::variable_snapshot(&vars.versions);
                stack_snapshot::append_definition_metadata(&mut versions, vars);
                assert!(
                    rows.insert(key, format!("{cfg}\t{tree}\t{exprs}\t{versions}"))
                        .is_none()
                );
            }
            Ok(result)
        })
        .unwrap();
    }
    assert!(failure.is_none(), "{failure:?}");
}
