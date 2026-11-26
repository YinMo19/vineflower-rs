// SPDX-License-Identifier: Apache-2.0

use std::{
    collections::BTreeMap,
    env, fs, io,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use vineflower_rs::{
    decompiler::stats::StatementKind,
    engine::{
        Cx, Options,
        class_nodes::{ClassKind, load_classes},
        class_processor::process_class_methods,
        class_writer::with_method_for_writing,
        context_source::RuntimeImage,
        counter_container::{EXPRESSION_COUNTER, STATEMENT_COUNTER},
    },
    kotlin::{body, imports, members, passes},
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

#[path = "support/upstream_reference.rs"]
mod upstream_reference;

#[test]
#[ignore = "requires an upstream build, a modular JDK, KOTLINC or KOTLIN_COMPILER_CLASSPATH and KOTLIN_STDLIB"]
fn kotlin_method_bodies_match_plugin() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"));
    let scratch = tempfile::tempdir().unwrap();
    let stdlib = PathBuf::from(env::var_os("KOTLIN_STDLIB").expect("set KOTLIN_STDLIB"));
    let jdk = upstream_reference::jdk_home();
    let classes = scratch.path().join("classes");
    let mut compile = if let Some(classpath) = env::var_os("KOTLIN_COMPILER_CLASSPATH") {
        let mut cmd = Command::new(jdk.join("bin/java"));
        cmd.arg("-classpath")
            .arg(classpath)
            .arg("org.jetbrains.kotlin.cli.jvm.K2JVMCompiler");
        cmd
    } else {
        Command::new(env::var_os("KOTLINC").unwrap_or_else(|| "kotlinc".into()))
    };
    let output = compile
        .args([
            "-no-stdlib",
            "-no-reflect",
            "-jvm-target",
            "17",
            "-classpath",
        ])
        .arg(&stdlib)
        .arg("-d")
        .arg(&classes)
        .arg(workspace.join("test/fixtures/kotlin_body/BodySubject.kt"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "kotlinc: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let corpus = upstream_reference::Corpus::discover();
    let request = scratch.path().join("request.txt");
    for collapse in [true, false] {
        fs::write(
            &request,
            format!(
                "{}\n{}\n{}\n{}\n",
                classes.display(),
                stdlib.display(),
                jdk.display(),
                i32::from(collapse)
            ),
        )
        .unwrap();
        let expected_source = corpus.run_with_kotlin("KotlinBodyReference", &[], &request);
        let expected = expected_source
            .lines()
            .map(|line| {
                let fields: Vec<_> = line.split('\t').collect();
                let [class, key, counts, text, mapping] = fields[..] else {
                    panic!("Kotlin body oracle: {line}")
                };
                let text = text
                    .as_bytes()
                    .chunks_exact(2)
                    .map(|bytes| {
                        u8::from_str_radix(std::str::from_utf8(bytes).unwrap(), 16).unwrap()
                    })
                    .collect::<Vec<_>>();
                (
                    format!("{class} {key}"),
                    (
                        counts.to_owned(),
                        String::from_utf8(text).unwrap(),
                        mapping.to_owned(),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let actual = native_bodies(&classes, &stdlib, &jdk, collapse).unwrap();
        assert_eq!(expected.len(), actual.len());
        for (key, expected) in expected {
            assert_eq!(
                &expected,
                actual.get(&key).unwrap(),
                "method {key}, templates {collapse}"
            );
        }
    }
}

fn native_bodies(
    classes: &Path,
    stdlib: &Path,
    jdk: &Path,
    collapse: bool,
) -> io::Result<BTreeMap<String, (String, String, String)>> {
    let mut options = Options::default();
    options.include_runtime = jdk.display().to_string();
    options.thread_count = 1;
    options.unit_test_mode = true;
    options.keep_literals = true;
    options.preferred_line_length = 60;
    options.kt_collapse_string_concat = collapse;
    let options = Arc::new(options);
    let mut structure = StructContext::new(Arc::clone(&options), None);
    structure.add_space(Arc::new(RuntimeImage::open(jdk)?), false);
    structure.add_file(classes, true)?;
    structure.add_file(stdlib, false)?;
    let mut cx = Cx::new(Arc::new(structure));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    let roots = cx
        .class_nodes
        .iter()
        .filter(|(_, node)| node.kind == ClassKind::Root)
        .map(|(name, _)| (name.clone(), cx.class_nodes.id(name).unwrap()))
        .collect::<BTreeMap<_, _>>();
    let mut source = BTreeMap::new();
    for (class_name, node) in roots {
        let class = cx.class_nodes[node].class.clone();
        members::parse_metadata_for(&mut cx, &class);
        process_class_methods(&mut cx, node, |cx, class, method| {
            let Some(mut method) = passes::defined_method(cx, class, method)? else {
                return Ok(None);
            };
            body::prepare(cx, &mut method)?;
            Ok(Some(method))
        })?;
        cx.imports = imports::from_parent(&cx.imports);
        let count = cx.class_nodes[node].wrapper.as_ref().unwrap().methods.len();
        for index in 0..count {
            let method = &cx.class_nodes[node].wrapper.as_ref().unwrap().methods[index];
            assert!(
                method.decompile_error().is_none(),
                "{}: {:?}",
                method.method.name,
                method.decompile_error()
            );
            let Some(root) = method.root() else { continue };
            let key = format!("{} {}", method.method.name, method.method.descriptor);
            let count = format!(
                "{},{}",
                method.counters.get_counter(STATEMENT_COUNTER),
                method.counters.get_counter(EXPRESSION_COUNTER)
            );
            let mut result = with_method_for_writing(&mut cx, node, index, |cx| {
                let mut buffer = body::statement(cx, root, 1)?;
                let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
                    unreachable!()
                };
                if let StatementKind::DummyExit {
                    bytecode: Some(ref bytecode),
                } = cx.ir[dummy_exit].kind
                {
                    for offset in bytecode.iter() {
                        buffer.add_bytecode_mapping(offset as i32);
                    }
                }
                let mut result = TextBuffer::new(cx);
                result.append_buffer_for(&buffer, Some(&class_name), Some(&key));
                Ok(result)
            })?;
            result.reformat();
            let mapping: BTreeMap<i32, i32> = result
                .get_tracers()
                .values()
                .flat_map(|tracer| tracer.get_mapping().iter())
                .map(|(&offset, &line)| (offset, line))
                .collect();
            let mapping = mapping
                .into_iter()
                .map(|(offset, line)| format!("{offset}={line}"))
                .collect::<Vec<_>>()
                .join(", ");
            source.insert(
                format!("{class_name} {key}"),
                (
                    count,
                    result.convert_to_string_and_allow_data_discard(),
                    format!("{{{mapping}}}"),
                ),
            );
        }
    }
    Ok(source)
}
