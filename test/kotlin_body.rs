// SPDX-License-Identifier: Apache-2.0

use std::{
    collections::BTreeMap,
    env, fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use vineflower_rs::{
    decompiler::stats::StatementKind,
    engine::{
        Cx, Options,
        class_nodes::{ClassKind, load_classes},
        class_processor::process_class,
        class_writer::with_method_for_writing,
        context_source::RuntimeImage,
        counter_container::{EXPRESSION_COUNTER, STATEMENT_COUNTER},
    },
    kotlin::{body, imports},
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

#[allow(
    dead_code,
    reason = "the Kotlin tests compile their own class fixtures"
)]
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
    compile_kotlin(workspace, &jdk, &stdlib, &classes, "BodySubject.kt", None);

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
        let expected =
            decode_reference(&corpus.run_with_kotlin("KotlinBodyReference", &[], &request));
        let actual = native_bodies(&classes, &stdlib, &jdk, collapse, None).unwrap();
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

#[test]
#[ignore = "requires an upstream build, a modular JDK, KOTLINC or KOTLIN_COMPILER_CLASSPATH and KOTLIN_STDLIB"]
fn kotlin_lambda_sources_tokens_and_archive_mappings_match_plugin() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"));
    let scratch = tempfile::tempdir().unwrap();
    let stdlib = PathBuf::from(env::var_os("KOTLIN_STDLIB").expect("set KOTLIN_STDLIB"));
    let jdk = upstream_reference::jdk_home();
    let corpus = upstream_reference::Corpus::discover();
    let mode_cases = [
        ("indy", "IndySubject.kt", &["indy/IndySubject.kt"][..]),
        (
            "class",
            "ClassSubject.kt",
            &[
                "classlambda/ClassSubject.kt",
                "classlambda/CompanionRead.kt",
                "classlambda/References.kt",
            ][..],
        ),
    ];
    for (mode, fixture, mapped_entries) in mode_cases {
        let root = scratch.path().join(mode);
        let classes = root.join("classes");
        compile_kotlin(workspace, &jdk, &stdlib, &classes, fixture, Some(mode));
        let input = root.join("classes.jar");
        archive_classes(&classes, &input);
        let common = [
            "--file".to_owned(),
            "--thread-count=1".to_owned(),
            "--kt-enable=1".to_owned(),
            "--log=warn".to_owned(),
            "--dump-exception-on-error=0".to_owned(),
            "--dump-bytecode-on-error=0".to_owned(),
            "--bytecode-source-mapping=1".to_owned(),
            "--dump-code-lines=1".to_owned(),
            "--dump-text-tokens=1".to_owned(),
            format!("--include-runtime={}", jdk.display()),
            format!("-e={}", stdlib.display()),
            input.display().to_string(),
        ];
        let expected = root.join("expected.jar");
        let request = root.join("request.txt");
        fs::write(
            &request,
            format!("{}\n{}\n", common.join("\n"), expected.display()),
        )
        .unwrap();
        corpus.run("KotlinLambdaReference", &[], &request);
        let actual = root.join("actual.jar");
        let native = Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
            .args(&common)
            .arg(&actual)
            .output()
            .unwrap();
        assert!(
            native.status.success(),
            "{}",
            String::from_utf8_lossy(&native.stderr)
        );
        let mut expected = zip::ZipArchive::new(fs::File::open(expected).unwrap()).unwrap();
        let mut actual = zip::ZipArchive::new(fs::File::open(actual).unwrap()).unwrap();
        let entries = kotlin_entry_names(&expected);
        assert_eq!(
            entries,
            kotlin_entry_names(&actual),
            "{mode} Kotlin sources"
        );
        for entry in &entries {
            let mut expected = expected.by_name(entry).unwrap();
            let mut actual = actual.by_name(entry).unwrap();
            let mut source = String::new();
            expected.read_to_string(&mut source).unwrap();
            let mut rendered = String::new();
            actual.read_to_string(&mut rendered).unwrap();
            assert_eq!(source, rendered, "{entry}");
            assert_eq!(
                expected.extra_data(),
                actual.extra_data(),
                "{entry} ZIP extra data"
            );
            if entry == "indy/IndySubject.kt" {
                assert!(source.contains("return@lambda_"));
            }
        }
        for &entry in mapped_entries {
            let mapped = expected.by_name(entry).unwrap();
            assert!(
                has_mapping_field(mapped.extra_data().unwrap_or_default()),
                "{entry} missing mapping"
            );
        }
        if mode == "class" {
            assert!(
                entries
                    .iter()
                    .any(|entry| entry == "classlambda/EnumDefaults.kt"),
                "the plugin archive omitted the annotation fixture"
            );
            let selected = "classlambda/References";
            fs::write(
                &request,
                format!(
                    "{}\n{}\n{}\n1\n{selected}\n",
                    classes.display(),
                    stdlib.display(),
                    jdk.display()
                ),
            )
            .unwrap();
            let expected =
                decode_reference(&corpus.run_with_kotlin("KotlinBodyReference", &[], &request));
            let actual = native_bodies(&classes, &stdlib, &jdk, true, Some(selected)).unwrap();
            for reference in ["target::plus", "Target::plus", "::Target", "::twice"] {
                assert!(
                    expected
                        .values()
                        .any(|(_, body, _)| body.contains(reference)),
                    "{reference}"
                );
            }
            assert_eq!(expected.len(), actual.len());
            for (method, expected) in expected {
                assert_eq!(&expected, actual.get(&method).unwrap(), "{method}");
            }
        }
    }
}

fn kotlin_entry_names(archive: &zip::ZipArchive<fs::File>) -> Vec<String> {
    let mut names: Vec<_> = archive
        .file_names()
        .filter(|name| name.ends_with(".kt"))
        .map(str::to_owned)
        .collect();
    names.sort_unstable();
    names
}

fn has_mapping_field(mut bytes: &[u8]) -> bool {
    while let [id_lo, id_hi, size_lo, size_hi, rest @ ..] = bytes {
        if u16::from_le_bytes([*id_lo, *id_hi]) == 0x4646 {
            return true;
        }
        let size = u16::from_le_bytes([*size_lo, *size_hi]) as usize;
        let Some(next) = rest.get(size..) else { break };
        bytes = next;
    }
    false
}

fn archive_classes(classes: &Path, destination: &Path) {
    fn append(zip: &mut zip::ZipWriter<fs::File>, root: &Path, folder: &Path) {
        let mut entries = fs::read_dir(folder)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect::<Vec<_>>();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                append(zip, root, &path);
            } else if path
                .extension()
                .is_some_and(|extension| extension == "class")
            {
                let name = path
                    .strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .replace('\\', "/");
                zip.start_file(name, zip::write::SimpleFileOptions::default())
                    .unwrap();
                zip.write_all(&fs::read(path).unwrap()).unwrap();
            }
        }
    }
    let mut zip = zip::ZipWriter::new(fs::File::create(destination).unwrap());
    append(&mut zip, classes, classes);
    zip.finish().unwrap();
}

fn compile_kotlin(
    workspace: &Path,
    jdk: &Path,
    stdlib: &Path,
    classes: &Path,
    fixture: &str,
    lambdas: Option<&str>,
) {
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
        .args(lambdas.map(|mode| format!("-Xlambdas={mode}")))
        .args([
            "-no-stdlib",
            "-no-reflect",
            "-jvm-target",
            "17",
            "-classpath",
        ])
        .arg(stdlib)
        .arg("-d")
        .arg(classes)
        .arg(workspace.join("test/fixtures/kotlin_body").join(fixture))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "kotlinc: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

type Snapshots = BTreeMap<String, (String, String, String)>;

fn decode_reference(expected_source: &str) -> Snapshots {
    expected_source
        .lines()
        .map(|line| {
            let fields: Vec<_> = line.split('\t').collect();
            let [class, key, counts, text, mapping] = fields[..] else {
                panic!("Kotlin body oracle: {line}")
            };
            let text = text
                .as_bytes()
                .chunks_exact(2)
                .map(|bytes| u8::from_str_radix(std::str::from_utf8(bytes).unwrap(), 16).unwrap())
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
        .collect::<BTreeMap<_, _>>()
}

fn native_bodies(
    classes: &Path,
    stdlib: &Path,
    jdk: &Path,
    collapse: bool,
    selected: Option<&str>,
) -> io::Result<Snapshots> {
    let mut options = Options::default();
    options.include_runtime = jdk.display().to_string();
    options.thread_count = 1;
    options.decompile_kotlin = true;
    options.decompile_inner = selected.is_none();
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
    let mut selected_imports = None;
    if let Some(selected) = selected {
        for (name, &node) in &roots {
            process_class(&mut cx, node)?;
            if *name == selected {
                selected_imports = Some(cx.imports.clone());
            }
        }
    }
    let mut source = BTreeMap::new();
    for (class_name, node) in roots {
        if let Some(selected) = selected {
            if class_name != selected {
                continue;
            }
        } else {
            process_class(&mut cx, node)?;
        }
        cx.imports = imports::from_parent(selected_imports.as_ref().unwrap_or(&cx.imports));
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
