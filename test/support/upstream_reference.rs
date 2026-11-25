// SPDX-License-Identifier: Apache-2.0

use std::fs::File;
use std::io::{Read, Seek};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::{env, fs, io};

pub struct Corpus {
    pub classes: Vec<PathBuf>,
    jar: PathBuf,
}

impl Corpus {
    pub fn discover() -> Self {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"));
        let upstream = env::var_os("VINEFLOWER_UPSTREAM")
            .map(PathBuf::from)
            .unwrap_or_else(|| workspace.join("../vineflower"));
        let mut root = env::var_os("VINEFLOWER_RS_CLASS_ROOT")
            .map(PathBuf::from)
            .unwrap_or_else(|| upstream.join("testData/classes"));
        if root.join("testData/classes").is_dir() {
            root = root.join("testData/classes");
        }
        let mut classes = Vec::new();
        collect_class_paths(&root, &mut classes)
            .unwrap_or_else(|error| panic!("reading {}: {error}", root.display()));
        classes.sort_unstable();
        assert!(!classes.is_empty(), "no classes in {}", root.display());
        let libs = upstream.join("build/libs");
        let jar = fs::read_dir(&libs)
            .unwrap_or_else(|error| panic!("reading {}: {error}", libs.display()))
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.file_name()
                    .is_some_and(|name| name.to_string_lossy().ends_with("+local.jar"))
            })
            .min()
            .unwrap_or_else(|| panic!("no *+local.jar in {}", libs.display()));
        Self { classes, jar }
    }

    #[allow(
        dead_code,
        reason = "only the smaller parity tests read all snapshots at once"
    )]
    pub fn run(&self, main: &str, helpers: &[&str], input: &Path) -> String {
        let mut output = tempfile::tempfile().unwrap();
        self.run_to(main, helpers, input, &output);
        output.rewind().unwrap();
        let mut text = String::new();
        output.read_to_string(&mut text).unwrap();
        text
    }

    pub fn run_to(&self, main: &str, helpers: &[&str], input: &Path, output: &File) {
        let classes = tempfile::tempdir().unwrap();
        let sources = Path::new(env!("CARGO_MANIFEST_DIR")).join("test/support");
        let mut compiler = Command::new(jdk_tool("javac"));
        compiler
            .arg("-encoding")
            .arg("UTF-8")
            .arg("-classpath")
            .arg(&self.jar)
            .arg("-d")
            .arg(classes.path());
        for name in std::iter::once(&main).chain(helpers) {
            compiler.arg(sources.join(format!("{name}.java")));
        }
        run(&mut compiler);
        let classpath = env::join_paths([classes.path(), self.jar.as_path()]).unwrap();
        run(Command::new(jdk_tool("java"))
            .arg("-classpath")
            .arg(classpath)
            .arg(main)
            .arg(input)
            .stdout(Stdio::from(output.try_clone().unwrap())));
    }
}

fn jdk_tool(name: &str) -> PathBuf {
    let name = format!("{name}{}", env::consts::EXE_SUFFIX);
    env::var_os("JAVA_HOME")
        .map(PathBuf::from)
        .map(|home| home.join("bin").join(&name))
        .unwrap_or_else(|| PathBuf::from(name))
}

fn run(command: &mut Command) -> Output {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("starting {command:?}: {error}"));
    assert!(
        output.status.success(),
        "{command:?} exited {}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn collect_class_paths(root: &Path, paths: &mut Vec<PathBuf>) -> io::Result<()> {
    if root.is_dir() {
        for entry in fs::read_dir(root)? {
            let entry = entry?;
            if !entry.file_type()?.is_symlink() {
                collect_class_paths(&entry.path(), paths)?;
            }
        }
    } else if root
        .extension()
        .is_some_and(|extension| extension == "class")
    {
        paths.push(root.canonicalize()?);
    }
    Ok(())
}
