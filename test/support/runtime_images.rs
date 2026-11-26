// SPDX-License-Identifier: Apache-2.0

use std::{
    borrow::Cow,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use jimage_rs::JImage;
use vineflower_rs::engine::context_source::{ContextSource, RuntimeImage};

use super::upstream_reference;

#[test]
#[ignore = "requires a JDK 17 with jmods and jlink"]
fn jlink_runtime_images_match_jimage_and_load_through_the_cli() {
    let java_home = env::var_os("VINEFLOWER_JDK_17")
        .map(PathBuf::from)
        .unwrap_or_else(upstream_reference::jdk_home);
    let java_tool = |name| {
        java_home
            .join("bin")
            .join(format!("{name}{}", env::consts::EXE_SUFFIX))
    };
    let scratch = tempfile::tempdir().unwrap();
    let source = scratch.path().join("RuntimeUser.java");
    fs::write(
        &source,
        "public class RuntimeUser implements Runnable { @Override public void run() {} }",
    )
    .unwrap();
    run(Command::new(java_tool("javac")).arg(&source));

    // A supplementary character in the name and a lone surrogate and NUL in
    // the constant pool exercise both uses of the image's Modified UTF-8 table.
    let descriptor = scratch.path().join("module-info.java");
    let unusual = scratch.path().join("𐐀.java");
    fs::write(&descriptor, "module image.probe { exports sample; }").unwrap();
    fs::write(
        &unusual,
        r#"package sample;
public class 𐐀 {
    public static final String TEXT = "a\0\uD800\uD83D\uDD2C";
    public 𐐀[] around(𐐀 value) { return new 𐐀[] {value}; }
}"#,
    )
    .unwrap();
    let classes = scratch.path().join("classes");
    run(Command::new(java_tool("javac"))
        .args(["-encoding", "UTF-8", "-d"])
        .arg(&classes)
        .args([descriptor, unusual]));
    let expected_class = fs::read(classes.join("sample/𐐀.class")).unwrap();
    // A small resource can contain the layer magic without being another header.
    fs::write(
        classes.join("sample/header.bin"),
        0xcafe_fafau32.to_ne_bytes(),
    )
    .unwrap();
    let module_path = env::join_paths([java_home.join("jmods"), classes]).unwrap();

    let (native, opposite) = if cfg!(target_endian = "little") {
        ("little", "big")
    } else {
        ("big", "little")
    };
    for (image, compression, endianness) in [
        ("plain", &["--compress=0"][..], native),
        ("compact", &["--compress=1"][..], native),
        ("zip", &["--compress=2"][..], native),
        ("layered", &["--compress=1", "--compress=2"][..], native),
        ("compact-opposite", &["--compress=1"][..], opposite),
    ] {
        let home = scratch.path().join(image);
        run(Command::new(java_tool("jlink"))
            .arg("--module-path")
            .arg(&module_path)
            .args(["--add-modules", "image.probe", "--endian", endianness])
            .args(compression)
            .args(["--no-header-files", "--no-man-pages", "--output"])
            .arg(&home));

        // The JDK tool reads the host's byte order. The opposite-endian
        // image should expand to the same bytes as the native compact image.
        let extracted = if endianness == native {
            let extracted = scratch.path().join(format!("extracted-{image}"));
            run(Command::new(java_tool("jimage"))
                .args(["extract", "--dir"])
                .arg(&extracted)
                .arg(home.join("lib/modules")));
            extracted
        } else {
            scratch.path().join("extracted-compact")
        };

        let runtime = RuntimeImage::open(&home).unwrap();
        let entries = runtime.get_entries();
        assert_eq!(entries.child_contexts.len(), 2);
        let jimage = JImage::open(home.join("lib/modules")).unwrap();
        let compared: usize = entries
            .child_contexts
            .iter()
            .map(|module| {
                let name = module.get_name();
                let name = name
                    .strip_prefix("module ")
                    .unwrap()
                    .split('@')
                    .next()
                    .unwrap();
                compare_resources(module.as_ref(), &extracted.join(name), "")
            })
            .sum();
        assert_eq!(compared, jimage.resource_names().unwrap().len());
        let class = jimage
            .find_resource("/image.probe/sample/𐐀.class")
            .unwrap()
            .unwrap();
        assert_eq!(class.as_ref(), expected_class);
        assert_eq!(matches!(class, Cow::Borrowed(_)), image == "plain");

        let output = scratch.path().join(format!("decompiled-{image}"));
        fs::create_dir(&output).unwrap();
        run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
            .args(["--folder", "--log-level=ERROR"])
            .arg(format!("--include-runtime={}", home.display()))
            .arg(scratch.path().join("RuntimeUser.class"))
            .arg(&output));
        // javac omitted the source-only annotation. The CLI has to read
        // java.lang.Runnable from this image to discover the override.
        assert!(
            fs::read_to_string(output.join("RuntimeUser.java"))
                .unwrap()
                .contains("@Override")
        );
    }
}

fn run(command: &mut Command) {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("{command:?}: {error}"));
    assert!(
        output.status.success(),
        "{command:?}\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn compare_resources(module: &dyn ContextSource, root: &Path, parent: &str) -> usize {
    fs::read_dir(root.join(parent))
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            let name = entry.file_name().into_string().unwrap();
            let name = if parent.is_empty() {
                name
            } else {
                format!("{parent}/{name}")
            };
            if entry.file_type().unwrap().is_dir() {
                compare_resources(module, root, &name)
            } else {
                let actual = module
                    .get_input_stream(&name)
                    .unwrap_or_else(|error| panic!("Decoding {name}: {error}"))
                    .unwrap_or_else(|| panic!("Missing {name}"));
                assert!(
                    actual == fs::read(entry.path()).unwrap(),
                    "Resource bytes differ for {name}"
                );
                1
            }
        })
        .sum()
}
