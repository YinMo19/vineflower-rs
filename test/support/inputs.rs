use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::Failure;
use crate::manifest::{Case, Version};

pub fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("test/upstream")
}

pub struct Inputs {
    fixtures: PathBuf,
    prebuilt: Option<PathBuf>,
    compiled: PathBuf,
    groups: HashMap<(&'static str, &'static str), Result<PathBuf, Failure>>,
    jdks: HashMap<&'static str, Result<PathBuf, Failure>>,
}

impl Inputs {
    pub fn new(compiled: PathBuf) -> Self {
        Self {
            fixtures: fixture_root(),
            prebuilt: env::var_os("VINEFLOWER_RS_CLASS_ROOT").map(PathBuf::from),
            compiled,
            groups: HashMap::new(),
            jdks: HashMap::new(),
        }
    }

    pub fn data(&self, suite: &str) -> PathBuf {
        suite_data(&self.fixtures, suite)
    }

    pub fn sources(&mut self, case: &Case) -> Result<(PathBuf, Vec<PathBuf>), Failure> {
        let primary = self.class_file(case.suite, case.version, case.class)?;
        let mut companions = nested_classes(&primary)?;
        for name in &case.companions {
            let companion = self.class_file(case.suite, case.version, name)?;
            companions.extend(nested_classes(&companion)?);
            companions.push(companion);
        }
        companions.sort_unstable();
        companions.dedup();
        companions.retain(|path| *path != primary);
        Ok((primary, companions))
    }

    pub fn class_file(
        &mut self,
        suite: &'static str,
        version: Version,
        name: &str,
    ) -> Result<PathBuf, Failure> {
        let fixture_group = self.data(suite).join("classes").join(version.dir);
        let checked_in = class_path(&fixture_group, suite, name);
        if checked_in.is_file() {
            return Ok(checked_in);
        }
        if version.dir == "custom" {
            return Err(Failure::fixture(&checked_in, "checked-in class"));
        }
        if let Some(prebuilt) = &self.prebuilt {
            let group = suite_data(prebuilt, suite)
                .join("classes")
                .join(version.dir);
            if group.is_dir() {
                let class = class_path(&group, suite, name);
                return require_file(class, "prebuilt class");
            }
        }
        if version.jdk.is_none() {
            return Err(Failure::MissingFixture(format!(
                "{} (provide the upstream-compiled {} group through VINEFLOWER_RS_CLASS_ROOT)",
                checked_in.display(),
                version.dir
            )));
        }
        let key = (suite, version.dir);
        if !self.groups.contains_key(&key) {
            let result = self.compile_group(suite, version);
            self.groups.insert(key, result);
        }
        let group = self.groups[&key].as_ref().map_err(Clone::clone)?;
        require_file(class_path(group, suite, name), "compiled class")
    }

    pub fn jdk(&mut self, major: &'static str) -> Result<PathBuf, Failure> {
        self.jdks
            .entry(major)
            .or_insert_with(|| exact_jdk(major))
            .clone()
    }

    fn compile_group(&mut self, suite: &'static str, version: Version) -> Result<PathBuf, Failure> {
        let source = self.data(suite).join("src").join(version.dir);
        if !source.is_dir() {
            return Err(Failure::fixture(&source, "Java source group"));
        }
        let major = version.jdk.expect("Java group without a compiler version");
        let jdk = self.jdk(major)?;
        let output = self.compiled.join(suite).join(version.dir);
        fs::create_dir_all(&output).map_err(|e| Failure::io(&output, e))?;
        let mut sources = Vec::new();
        collect_java_sources(&source, &mut sources)?;
        sources.sort_unstable();
        if sources.is_empty() {
            return Err(Failure::fixture(&source, "no Java source files"));
        }

        let mut javac = Command::new(jdk.join("bin").join(executable("javac")));
        javac.args(["-encoding", "UTF-8", "-source", major, "-target", major]);
        javac.arg(if version.dir.ends_with("nodebug") {
            "-g:none"
        } else {
            "-g"
        });
        if version.dir.ends_with("preview") {
            javac.arg("--enable-preview");
        }
        javac.arg("-d").arg(&output).args(sources);
        let result = javac.output().map_err(|e| Failure::io(&source, e))?;
        if !result.status.success() {
            return Err(Failure::Execution(format!(
                "javac {} exited {} while compiling {}:\n{}",
                major,
                result.status,
                source.display(),
                String::from_utf8_lossy(&result.stderr)
            )));
        }
        Ok(output)
    }
}

pub fn suite_data(root: &Path, suite: &str) -> PathBuf {
    if suite == "core" {
        root.join("testData")
    } else {
        root.join("plugins").join(suite).join("testData")
    }
}

fn executable(name: &str) -> String {
    format!("{name}{}", env::consts::EXE_SUFFIX)
}

fn exact_jdk(major: &str) -> Result<PathBuf, Failure> {
    let key = format!("VINEFLOWER_JDK_{major}");
    let home = env::var_os(&key).map(PathBuf::from).ok_or_else(|| {
        Failure::MissingJdk(format!("set {key} to the home of an exact JDK {major}"))
    })?;
    let release = fs::read_to_string(home.join("release")).ok();
    let version = release.as_deref().and_then(|text| {
        text.lines().find_map(|line| {
            line.strip_prefix("JAVA_VERSION=")
                .map(|s| s.trim_matches('"'))
        })
    });
    let actual_major = version
        .map(|v| v.strip_prefix("1.").unwrap_or(v))
        .and_then(|v| v.split(|c: char| !c.is_ascii_digit()).next());
    if actual_major != Some(major) || !home.join("bin").join(executable("javac")).is_file() {
        return Err(Failure::MissingJdk(format!(
            "{key}={} is not a JDK {major} home (JAVA_VERSION={})",
            home.display(),
            version.unwrap_or("missing")
        )));
    }
    Ok(home)
}

pub fn require_file(path: PathBuf, description: &str) -> Result<PathBuf, Failure> {
    if path.is_file() {
        Ok(path)
    } else {
        Err(Failure::fixture(&path, description))
    }
}

fn class_path(group: &Path, suite: &str, name: &str) -> PathBuf {
    let plain = group.join(format!("{name}.class"));
    // The Kotlin plugin accepts file facades named <test>Kt without changing golden names.
    if suite == "kotlin" && !plain.is_file() {
        group.join(format!("{name}Kt.class"))
    } else {
        plain
    }
}

fn nested_classes(class: &Path) -> Result<Vec<PathBuf>, Failure> {
    let parent = class.parent().expect("class path without directory");
    let name = class
        .file_stem()
        .and_then(|s| s.to_str())
        .expect("non-UTF-8 fixture name");
    let mut classes = Vec::new();
    for entry in fs::read_dir(parent).map_err(|e| Failure::io(parent, e))? {
        let entry = entry.map_err(|e| Failure::io(parent, e))?;
        if entry
            .file_name()
            .to_str()
            .and_then(|other| other.strip_prefix(name))
            .is_some_and(|tail| tail.starts_with('$') && tail.ends_with(".class"))
            && entry.path().is_file()
        {
            classes.push(entry.path());
        }
    }
    Ok(classes)
}

fn collect_java_sources(dir: &Path, paths: &mut Vec<PathBuf>) -> Result<(), Failure> {
    for entry in fs::read_dir(dir).map_err(|e| Failure::io(dir, e))? {
        let entry = entry.map_err(|e| Failure::io(dir, e))?;
        let path = entry.path();
        let kind = entry.file_type().map_err(|e| Failure::io(&path, e))?;
        if kind.is_dir() {
            collect_java_sources(&path, paths)?;
        } else if kind.is_file() && path.extension().is_some_and(|e| e == "java") {
            paths.push(path);
        }
    }
    Ok(())
}
