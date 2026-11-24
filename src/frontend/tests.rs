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
            "-hes=0".into(),
            "--__unit_test_mode__".into(),
            "-nls=0".into(),
            "--remove-imports".into(),
            "--banner=/* generated */".into(),
            "--".into(),
            "-example.class".into(),
        ])),
    )
    .unwrap();
    assert_eq!(cli.paths, [PathBuf::from("-example.class")]);
    let options = cli.options().unwrap();
    assert!(options.ascii_strings);
    assert!(!options.use_debug_names);
    assert!(!options.remove_synthetic);
    assert!(!options.remove_bridge);
    assert!(!options.decompile_generics);
    assert!(!options.hide_default_constructor);
    assert!(options.include_line_mappings);
    assert!(options.dump_original_lines);
    assert!(!options.use_method_parameters);
    assert!(!options.hide_empty_super);
    assert!(options.unit_test_mode);
    assert!(options.crlf);
    assert!(options.remove_imports);
    assert_eq!(options.banner, "/* generated */");

    for flag in [
        "--add-external=lib.jar",
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
