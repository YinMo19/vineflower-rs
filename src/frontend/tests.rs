use super::*;
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{Cursor, Read};

use tempfile::tempdir;
use zip::write::SimpleFileOptions;
use zip::{CompressionMethod, ZipArchive, ZipWriter};

// ClassFile for: package pkg; public class Example { public static int value() { return 4; } }
// No compiler or Java runtime is required to run the CLI tests.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\x00\x00\x00\x34\x00\x08\
    \x01\x00\x0bpkg/Example\x07\x00\x01\
    \x01\x00\x10java/lang/Object\x07\x00\x03\
    \x01\x00\x05value\x01\x00\x03()I\x01\x00\x04Code\
    \x00\x21\x00\x02\x00\x04\x00\x00\x00\x00\x00\x01\
    \x00\x09\x00\x05\x00\x06\x00\x01\x00\x07\x00\x00\x00\x0e\
    \x00\x01\x00\x00\x00\x00\x00\x02\x07\xac\x00\x00\x00\x00\
    \x00\x00";

// package pkg; public class Client { public Parent.Child member; }
// Deliberately omits InnerClasses: the source must resolve the type via classpath metadata.
const CLIENT: &[u8] = b"\xca\xfe\xba\xbe\x00\x00\x00\x34\x00\x07\
    \x01\x00\x0apkg/Client\x07\x00\x01\
    \x01\x00\x10java/lang/Object\x07\x00\x03\
    \x01\x00\x06member\x01\x00\x12Lpkg/Parent$Child;\
    \x00\x21\x00\x02\x00\x04\x00\x00\x00\x01\
    \x00\x01\x00\x05\x00\x06\x00\x00\x00\x00\x00\x00";

fn nested_class(child: bool) -> Vec<u8> {
    // Both binaries describe public class Parent { public static class Child {} }.
    let mut bytes = b"\xca\xfe\xba\xbe\x00\x00\x00\x34\x00\x09".to_vec();
    let utf8 = |bytes: &mut Vec<u8>, value: &str| {
        bytes.push(1);
        bytes.extend_from_slice(&(value.len() as u16).to_be_bytes());
        bytes.extend_from_slice(value.as_bytes());
    };
    for (i, name) in ["pkg/Parent", "pkg/Parent$Child", "java/lang/Object"]
        .into_iter()
        .enumerate()
    {
        utf8(&mut bytes, name);
        bytes.extend_from_slice(&[7, 0, (i * 2 + 1) as u8]);
    }
    utf8(&mut bytes, "Child");
    utf8(&mut bytes, "InnerClasses");
    bytes.extend_from_slice(&[0, 0x21, 0, if child { 4 } else { 2 }, 0, 6]);
    bytes.extend_from_slice(b"\x00\x00\x00\x00\x00\x00\x00\x01");
    bytes.extend_from_slice(b"\x00\x08\x00\x00\x00\x0a\x00\x01\x00\x04\x00\x02\x00\x07\x00\x09");
    bytes
}
const MANIFEST: &[u8] = b"Manifest-Version: 1.0\r\nMain-Class: pkg.Example\r\n\r\n";
const RESOURCE: &[u8] = b"\0test data\xff";
const FIXTURE: [(&str, &[u8]); 3] = [
    ("pkg/Example.class", CLASS),
    ("pkg/res/data.bin", RESOURCE),
    ("META-INF/MANIFEST.MF", MANIFEST),
];

fn write_zip(path: &Path, entries: &[(&str, &[u8])]) {
    let mut writer = ZipWriter::new(File::create(path).unwrap());
    let settings = SimpleFileOptions::default().compression_method(CompressionMethod::Deflated);
    for &(name, data) in entries {
        writer.start_file(name, settings).unwrap();
        writer.write_all(data).unwrap();
    }
    writer.add_directory("empty/", settings).unwrap();
    writer.finish().unwrap();
}

fn run_paths(source: &Path, destination: &Path) -> Result<(), Box<dyn Error>> {
    run([source, destination].map(|path| path.as_os_str().to_owned()))
}

fn read_zip(bytes: &[u8]) -> BTreeMap<String, Vec<u8>> {
    let mut zip = ZipArchive::new(Cursor::new(bytes)).unwrap();
    assert_eq!(zip.name_for_index(0), Some("META-INF/MANIFEST.MF"));
    assert!(zip.by_name("empty/").is_err());
    (0..zip.len())
        .filter_map(|index| {
            let mut file = zip.by_index(index).unwrap();
            if file.is_dir() {
                return None;
            }
            let mut content = Vec::new();
            file.read_to_end(&mut content).unwrap();
            Some((file.name().to_owned(), content))
        })
        .collect()
}

fn read_directory(root: &Path) -> BTreeMap<String, Vec<u8>> {
    fn read_tree(root: &Path, dir: &Path, result: &mut BTreeMap<String, Vec<u8>>) {
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if entry.file_type().unwrap().is_dir() {
                read_tree(root, &path, result);
            } else {
                let name = path
                    .strip_prefix(root)
                    .unwrap()
                    .iter()
                    .map(|part| part.to_str().unwrap())
                    .collect::<Vec<_>>()
                    .join("/");
                result.insert(name, fs::read(path).unwrap());
            }
        }
    }
    assert!(root.join("empty").is_dir());
    let mut result = BTreeMap::new();
    read_tree(root, root, &mut result);
    result
}

#[test]
fn jar_zip_and_directory_inputs_to_both_output_types() {
    let work = tempdir().unwrap();
    let directory = work.path().join("classes");
    fs::create_dir_all(directory.join("empty")).unwrap();
    for (name, data) in FIXTURE {
        let path = directory.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, data).unwrap();
    }
    let jar = work.path().join("input.jar");
    let zip = work.path().join("input.zip");
    write_zip(&jar, &FIXTURE);
    write_zip(&zip, &[FIXTURE[2], FIXTURE[0], FIXTURE[1]]);

    let expected_java = crate::decompile(CLASS, &Options::default()).unwrap().text;
    assert!(expected_java.contains("package pkg;"));
    assert!(expected_java.contains("return 4;"));
    let expected = BTreeMap::from([
        ("META-INF/MANIFEST.MF".to_owned(), MANIFEST.to_vec()),
        ("pkg/res/data.bin".to_owned(), RESOURCE.to_vec()),
        ("pkg/Example.java".to_owned(), expected_java.into_bytes()),
    ]);
    let mut first_archive = None;
    for (index, source) in [directory, jar, zip].iter().enumerate() {
        let output_dir = work.path().join(format!("output-{index}"));
        run_paths(source, &output_dir).unwrap();
        assert_eq!(read_directory(&output_dir), expected);

        let output_jar = work.path().join(format!("output-{index}.jar"));
        run_paths(source, &output_jar).unwrap();
        let bytes = fs::read(output_jar).unwrap();
        assert_eq!(read_zip(&bytes), expected);
        if index == 1 {
            first_archive = Some(bytes);
        } else if index == 2 {
            // Reordering input members must not affect the generated archive.
            assert_eq!(Some(bytes), first_archive);
        }
    }

    let output_zip = work.path().join("output.ZIP");
    run_paths(&work.path().join("input.jar"), &output_zip).unwrap();
    assert_eq!(read_zip(&fs::read(output_zip).unwrap()), expected);
}

#[test]
fn standalone_class_defaults_to_stdout_and_supports_output_overrides() {
    let work = tempdir().unwrap();
    let input = work.path().join("different-filename.class");
    fs::write(&input, CLASS).unwrap();
    let mut stdout = Vec::new();
    run_with_output(
        [OsString::from("-ind=\t"), input.as_os_str().to_owned()],
        &mut stdout,
    )
    .unwrap();
    let text = String::from_utf8(stdout).unwrap();
    assert!(text.starts_with("==== Example.java ====\n"));
    assert!(text.contains("\tpublic static int value()"));

    let archive = work.path().join("output.data");
    run([
        "--file".into(),
        input.as_os_str().to_owned(),
        archive.as_os_str().to_owned(),
    ])
    .unwrap();
    let mut zip = ZipArchive::new(File::open(archive).unwrap()).unwrap();
    assert!(zip.by_name("Example.java").is_ok());

    let directory = work.path().join("output.zip");
    run([
        "--folder".into(),
        input.as_os_str().to_owned(),
        "-o".into(),
        directory.as_os_str().to_owned(),
    ])
    .unwrap();
    let text = fs::read_to_string(directory.join("Example.java")).unwrap();
    assert!(text.contains("\n   public static int value()"));
}

#[test]
fn supported_flags_feed_shared_options_and_unsupported_flags_error() {
    let cli = Cli::try_parse_from(
        std::iter::once("vineflower-rs".into()).chain(normalize_args([
            "--ascii-strings".into(),
            "--use-lvt-names=0".into(),
            "--no-remove-synthetic".into(),
            "-rbr=0".into(),
            "--decompile-generics=false".into(),
            "--no-hide-default-constructor".into(),
            "--bytecode-source-mapping".into(),
            "--__dump_original_lines__=1".into(),
            "--no-use-method-parameters".into(),
            "-mcs=1".into(),
            "-hes=0".into(),
            "--__unit_test_mode__".into(),
            "-nls=0".into(),
            "--remove-imports".into(),
            "--banner=/* generated */".into(),
            "-e=one.jar,two.jar".into(),
            "--add-external=three".into(),
            "-only=pkg/One,pkg/Two".into(),
            "--only=pkg/Three".into(),
            "-din=FALSE".into(),
            "--kt-enable".into(),
            "--".into(),
            "-example.class".into(),
        ])),
    )
    .unwrap();
    assert_eq!(cli.paths, [PathBuf::from("-example.class")]);
    assert_eq!(
        cli.add_external,
        ["one.jar", "two.jar", "three"].map(PathBuf::from)
    );
    assert_eq!(cli.only, ["pkg/One", "pkg/Two", "pkg/Three"]);
    let options = cli.options().unwrap();
    assert!(options.ascii_strings);
    assert!(!options.use_debug_names);
    assert!(!options.remove_synthetic);
    assert!(!options.remove_bridge);
    assert!(!options.decompile_generics);
    assert!(!options.hide_default_constructor);
    assert!(options.include_line_mappings);
    assert!(options.dump_original_lines);
    assert!(options.mark_corresponding_synthetics);
    assert!(!options.use_method_parameters);
    assert!(!options.hide_empty_super);
    assert!(options.unit_test_mode);
    assert!(options.crlf);
    assert!(options.remove_imports);
    assert_eq!(options.banner, "/* generated */");
    assert!(!options.decompile_inner);
    assert!(options.decompile_kotlin);

    for flag in [
        "--add-external",
        "--future-option",
        "--ascii-strings=invalid",
    ] {
        let error =
            run_with_output([flag.into(), "input.class".into()], &mut Vec::new()).unwrap_err();
        assert!(
            error
                .to_string()
                .contains(flag.split('=').next().unwrap().trim_start_matches('-'))
        );
    }
}

#[test]
fn invalid_archive_entries_do_not_escape_output() {
    let work = tempdir().unwrap();
    let input = work.path().join("input.zip");
    write_zip(&input, &[("../escape.txt", b"wrong destination")]);
    let out = work.path().join("output");
    assert!(
        run_paths(&input, &out)
            .unwrap_err()
            .to_string()
            .contains("invalid entry path")
    );
    assert!(!work.path().join("escape.txt").exists());
    assert!(!out.exists());
}

#[cfg(unix)]
#[test]
fn directory_output_does_not_follow_existing_entry_symlinks() {
    let work = tempdir().unwrap();
    let input = work.path().join("input.zip");
    write_zip(&input, &FIXTURE);
    let out = work.path().join("output");
    let external = work.path().join("external");
    fs::create_dir(&out).unwrap();
    fs::create_dir(&external).unwrap();
    std::os::unix::fs::symlink(&external, out.join("pkg")).unwrap();
    assert!(
        run_paths(&input, &out)
            .unwrap_err()
            .to_string()
            .contains("not a real directory")
    );
    assert_eq!(fs::read_dir(&external).unwrap().count(), 0);
}

#[test]
fn failures_are_explicit_and_do_not_replace_existing_archive() {
    let work = tempdir().unwrap();
    let missing = work.path().join("missing.class");
    let input = work.path().join("input.zip");
    let out = work.path().join("output.jar");
    fs::write(&out, b"existing destination").unwrap();
    assert!(
        run_paths(&missing, &out)
            .unwrap_err()
            .to_string()
            .contains("missing.class")
    );
    write_zip(&input, &[("pkg/Example.class", b"not a class")]);
    assert!(
        run_paths(&input, &out)
            .unwrap_err()
            .to_string()
            .contains("pkg/Example.class")
    );
    assert_eq!(fs::read(&out).unwrap(), b"existing destination");
    assert!(
        run_paths(&input, &input)
            .unwrap_err()
            .to_string()
            .contains("own destination")
    );

    write_zip(
        &input,
        &[
            ("pkg/Example.class", CLASS),
            ("pkg/Example.java", b"already there"),
        ],
    );
    assert!(
        run_paths(&input, &out)
            .unwrap_err()
            .to_string()
            .contains("duplicate output entry")
    );
    assert_eq!(fs::read(&out).unwrap(), b"existing destination");
}

#[test]
fn nested_class_group_writes_only_root_units_for_directory_and_archive() {
    let work = tempdir().unwrap();
    let parent = nested_class(false);
    let child = nested_class(true);
    let fixtures = [
        ("pkg/Parent$Child.class", child.as_slice()),
        ("pkg/Parent.class", parent.as_slice()),
        ("pkg/data.bin", RESOURCE),
        ("META-INF/MANIFEST.MF", MANIFEST),
    ];
    let directory = work.path().join("classes");
    fs::create_dir_all(directory.join("empty")).unwrap();
    for (name, bytes) in fixtures {
        let path = directory.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }
    let archive = work.path().join("classes.jar");
    write_zip(&archive, &fixtures);

    let out = work.path().join("classes-out.jar");
    run_paths(&directory, &out).unwrap();
    let contents = read_zip(&fs::read(out).unwrap());
    let source = std::str::from_utf8(&contents["pkg/Parent.java"]).unwrap();
    assert!(source.contains("public static class Child"));
    assert!(!contents.contains_key("pkg/Parent$Child.java"));
    assert_eq!(contents["pkg/data.bin"], RESOURCE);

    let out = work.path().join("classes-out");
    run_paths(&archive, &out).unwrap();
    assert_eq!(read_directory(&out), contents);

    let out = work.path().join("separate");
    run([
        "--no-decompile-inner".into(),
        archive.as_os_str().to_owned(),
        out.as_os_str().to_owned(),
    ])
    .unwrap();
    assert!(out.join("pkg/Parent$Child.java").is_file());

    let parent_file = work.path().join("unrelated-one.class");
    let child_file = work.path().join("unrelated-two.class");
    fs::write(&parent_file, &parent).unwrap();
    fs::write(&child_file, &child).unwrap();
    let out = work.path().join("standalone");
    run([
        child_file.into_os_string(),
        parent_file.into_os_string(),
        "-o".into(),
        out.as_os_str().to_owned(),
    ])
    .unwrap();
    assert_eq!(
        fs::read(out.join("Parent.java")).unwrap(),
        contents["pkg/Parent.java"]
    );
    assert_eq!(fs::read_dir(out).unwrap().count(), 1);
}

#[test]
fn classpath_inputs_resolve_names_without_writing_library_files() {
    let work = tempdir().unwrap();
    let source = work.path().join("input.class");
    fs::write(&source, CLIENT).unwrap();
    let parent = nested_class(false);
    let child = nested_class(true);
    let library_dir = work.path().join("library");
    fs::create_dir_all(library_dir.join("pkg")).unwrap();
    fs::write(library_dir.join("pkg/Parent$Child.class"), child).unwrap();
    fs::write(library_dir.join("library.txt"), RESOURCE).unwrap();
    let library_jar = work.path().join("library.jar");
    write_zip(
        &library_jar,
        &[("pkg/Parent.class", &parent), ("archive.txt", RESOURCE)],
    );
    let out = work.path().join("out");
    let config = work.path().join("vf.cfg");
    fs::write(
        &config,
        format!(
            "-e={}\n--add-external={}\n",
            library_jar.display(),
            library_dir.display()
        ),
    )
    .unwrap();
    run([
        "-cfg".into(),
        config.into_os_string(),
        source.as_os_str().to_owned(),
        out.as_os_str().to_owned(),
    ])
    .unwrap();
    let result = fs::read_to_string(out.join("Client.java")).unwrap();
    assert!(result.contains("public Parent.Child member;"));
    assert_eq!(fs::read_dir(&out).unwrap().count(), 1);

    let mut stdout = Vec::new();
    run_with_output([source.into_os_string()], &mut stdout).unwrap();
    assert!(
        String::from_utf8(stdout)
            .unwrap()
            .contains("public Parent$Child member;")
    );
}

#[test]
fn legacy_nested_archive_preserves_origin_and_prefix_selection_separates_child() {
    let work = tempdir().unwrap();
    let source = work.path().join("inputs");
    let out = work.path().join("out");
    fs::create_dir_all(source.join("child")).unwrap();
    let archive = source.join("child/input.jar");
    write_zip(
        &archive,
        &[
            ("pkg/Parent.class", &nested_class(false)),
            ("pkg/Parent$Child.class", &nested_class(true)),
            ("pkg/data.bin", RESOURCE),
        ],
    );
    run([
        "--legacy-saving".into(),
        "-only=pkg/Parent$Child".into(),
        source.into_os_string(),
        out.as_os_str().to_owned(),
    ])
    .unwrap();
    let mut output = ZipArchive::new(File::open(out.join("child/input.jar")).unwrap()).unwrap();
    assert!(output.by_name("pkg/Parent.java").is_err());
    assert!(output.by_name("pkg/Parent$Child.java").is_ok());
    assert!(output.by_name("pkg/data.bin").is_ok());
    assert!(!out.join("pkg").exists());
}

#[test]
fn multi_release_classes_do_not_shadow_base_and_resources_keep_physical_names() {
    const VERSIONED_RESOURCE: &str = "META-INF/versions/11/pkg/variant.bin";
    let work = tempdir().unwrap();
    let source = work.path().join("versioned.jar");
    write_zip(
        &source,
        &[
            (
                "META-INF/versions/11/pkg/Example.class",
                b"not the base class",
            ),
            (
                "META-INF/versions/11/pkg/VersionOnly.class",
                b"not a base class",
            ),
            ("pkg/Example.class", CLASS),
            (VERSIONED_RESOURCE, RESOURCE),
            (
                "META-INF/MANIFEST.MF",
                b"Manifest-Version: 1.0\r\nMulti-Release: true\r\n\r\n",
            ),
        ],
    );
    let out = work.path().join("out.jar");
    run_paths(&source, &out).unwrap();
    let contents = read_zip(&fs::read(out).unwrap());
    assert!(
        std::str::from_utf8(&contents["pkg/Example.java"])
            .unwrap()
            .contains("return 4;")
    );
    assert_eq!(contents[VERSIONED_RESOURCE], RESOURCE);
    assert_eq!(contents.len(), 3);
}

#[test]
fn log_level_filters_missing_library_diagnostics_without_losing_output() {
    let work = tempdir().unwrap();
    let input = work.path().join("Example.class");
    let missing = work.path().join("missing.jar");
    fs::write(&input, CLASS).unwrap();
    for (args, warns) in [
        (&["-log=WaRn"][..], true),
        (&["--log-level=ERROR"][..], false),
        (&["--log-level=trace", "--silent"][..], false),
    ] {
        let mut output = Vec::new();
        run_with_output(
            args.iter().map(OsString::from)
                .chain([format!("-e={}", missing.display()).into(), input.as_os_str().to_owned()]),
            &mut output,
        ).unwrap();
        let output = std::str::from_utf8(&output).unwrap();
        assert_eq!(output.contains("warn: missing"), warns, "{output}");
        assert!(output.contains("return 4;"), "{output}");
    }
}

#[test]
fn skip_extra_files_keeps_source_files_without_copying_resources() {
    let work = tempdir().unwrap();
    let source = work.path().join("with-resource.jar");
    let out = work.path().join("without-resource");
    write_zip(&source, &FIXTURE);
    run([
        "-sef=1".into(),
        source.into_os_string(),
        out.as_os_str().to_owned(),
    ])
    .unwrap();
    let files = read_directory(&out);
    assert_eq!(
        files.keys().map(String::as_str).collect::<Vec<_>>(),
        ["pkg/Example.java"]
    );
}
