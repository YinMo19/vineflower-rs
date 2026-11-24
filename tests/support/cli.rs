// Based on Vineflower's BulkDecompilationTest and CommandLineTest.
// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{self, Read};
use std::path::Path;
use std::process::Command;
use zip::ZipArchive;

use crate::inputs::require_file;
use crate::{Failure, difference, normalized};

#[derive(Clone, Copy)]
enum Source {
    Jar,
    Zip,
    Directory,
    UnpackedJar,
}

#[derive(Clone, Copy)]
enum Destination {
    Directory,
    Archive,
    UnpackedArchive,
}

pub struct CliCase {
    pub id: &'static str,
    source: Source,
    destination: Destination,
    fixture_options: bool,
}

pub const CASES: &[CliCase] = &[
    CliCase::new(
        "bulk/testDirectory",
        Source::UnpackedJar,
        Destination::Directory,
        true,
    ),
    CliCase::new(
        "bulk/testJar",
        Source::Jar,
        Destination::UnpackedArchive,
        true,
    ),
    CliCase::new("cli/testJarToJar", Source::Jar, Destination::Archive, false),
    CliCase::new(
        "cli/testJarToDir",
        Source::Jar,
        Destination::Directory,
        false,
    ),
    CliCase::new("cli/testZipToJar", Source::Zip, Destination::Archive, false),
    CliCase::new(
        "cli/testZipToDir",
        Source::Zip,
        Destination::Directory,
        false,
    ),
    CliCase::new(
        "cli/testDirToJar",
        Source::Directory,
        Destination::Archive,
        false,
    ),
    CliCase::new(
        "cli/testDirToDir",
        Source::Directory,
        Destination::Directory,
        false,
    ),
];

impl CliCase {
    const fn new(
        id: &'static str,
        source: Source,
        destination: Destination,
        fixture_options: bool,
    ) -> Self {
        Self {
            id,
            source,
            destination,
            fixture_options,
        }
    }

    pub fn run(&self, data: &Path, scratch: &Path) -> Result<(), Failure> {
        let expected = match self.destination {
            Destination::Archive => {
                let path = require_file(data.join("bulk_decomp.jar"), "archive golden")?;
                archive_snapshot(&path)?
            }
            Destination::Directory | Destination::UnpackedArchive => {
                let path = data.join("bulk");
                if !path.is_dir() {
                    return Err(Failure::fixture(&path, "directory golden"));
                }
                tree_snapshot(&path)?
            }
        };
        let workspace = tempfile::tempdir_in(scratch).map_err(|e| Failure::io(scratch, e))?;
        let input = match self.source {
            Source::Jar => require_file(data.join("bulk.jar"), "archive input")?,
            Source::Zip => require_file(data.join("bulk.zip"), "archive input")?,
            Source::Directory => {
                let path = data.join("classes/bulk");
                if !path.is_dir() {
                    return Err(Failure::fixture(&path, "directory input"));
                }
                path
            }
            Source::UnpackedJar => {
                let archive = require_file(data.join("bulk.jar"), "archive input")?;
                let path = workspace.path().join("classes");
                unpack(&archive, &path)?;
                path
            }
        };
        let output = workspace.path().join(match self.destination {
            Destination::Directory => "bulk_out",
            Destination::Archive | Destination::UnpackedArchive => "bulk_out.jar",
        });
        let mut command = Command::new(env!("CARGO_BIN_EXE_vineflower-rs"));
        if self.fixture_options {
            // The bulk corpus has no special literals or errors. The fixture's other
            // non-default settings affect diagnostics or are inert without source maps.
            command.args([
                "--decompile-generics=1",
                "--remove-synthetic=1",
                "--remove-bridge=1",
            ]);
        }
        let run = command
            .arg(&input)
            .arg(&output)
            .output()
            .map_err(|e| Failure::io(&input, e))?;
        if !run.status.success() {
            let stderr = String::from_utf8_lossy(&run.stderr);
            let message = format!("native CLI exited {}: {}", run.status, stderr.trim_end());
            return Err(
                if stderr.contains(": unsupported Java recovery:")
                    || stderr.contains(": cannot recover ")
                {
                    Failure::Unsupported(message)
                } else {
                    Failure::Execution(message)
                },
            );
        }
        if !output.exists() {
            return Err(Failure::Mismatch(format!(
                "missing CLI output {}",
                output.display()
            )));
        }
        let actual = match self.destination {
            Destination::Directory => tree_snapshot(&output)?,
            Destination::Archive => archive_snapshot(&output)?,
            Destination::UnpackedArchive => {
                let path = workspace.path().join("unpacked");
                unpack(&output, &path)?;
                tree_snapshot(&path)?
            }
        };
        compare(
            &expected,
            &actual,
            matches!(self.destination, Destination::Archive),
        )
    }
}

// None marks a directory entry. Archive order and physical metadata are not golden data.
type Snapshot = BTreeMap<String, Option<Vec<u8>>>;

fn compare(expected: &Snapshot, actual: &Snapshot, archive: bool) -> Result<(), Failure> {
    let missing: Vec<_> = expected
        .keys()
        .filter(|key| !actual.contains_key(*key))
        .collect();
    let extra: Vec<_> = actual
        .keys()
        .filter(|key| !expected.contains_key(*key))
        .collect();
    if !missing.is_empty() || !extra.is_empty() {
        return Err(Failure::Mismatch(format!(
            "missing entries {missing:?}; extra entries {extra:?}"
        )));
    }
    for (path, expected_file) in expected {
        match (expected_file, &actual[path]) {
            (None, None) => {}
            (Some(expected_bytes), Some(actual_bytes)) => {
                let expected = normalized(expected_bytes, archive);
                let actual = normalized(actual_bytes, archive);
                if expected != actual {
                    return Err(Failure::Mismatch(format!(
                        "{path}: {}",
                        difference(&expected, &actual)
                    )));
                }
            }
            _ => return Err(Failure::Mismatch(format!("different entry type at {path}"))),
        }
    }
    Ok(())
}

fn tree_snapshot(root: &Path) -> Result<Snapshot, Failure> {
    let mut entries = Snapshot::new();
    read_tree(root, root, &mut entries)?;
    Ok(entries)
}

fn read_tree(root: &Path, dir: &Path, entries: &mut Snapshot) -> Result<(), Failure> {
    for entry in fs::read_dir(dir).map_err(|e| Failure::io(dir, e))? {
        let entry = entry.map_err(|e| Failure::io(dir, e))?;
        let path = entry.path();
        let relative = path.strip_prefix(root).expect("walk escaped its own root");
        let name = relative
            .components()
            .map(|c| c.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/");
        let kind = entry.file_type().map_err(|e| Failure::io(&path, e))?;
        if kind.is_dir() {
            entries.insert(format!("{name}/"), None);
            read_tree(root, &path, entries)?;
        } else {
            entries.insert(
                name,
                Some(fs::read(&path).map_err(|e| Failure::io(&path, e))?),
            );
        }
    }
    Ok(())
}

fn open_archive(path: &Path) -> Result<ZipArchive<File>, Failure> {
    let file = File::open(path).map_err(|e| Failure::io(path, e))?;
    ZipArchive::new(file).map_err(|e| Failure::io(path, e))
}

fn archive_snapshot(path: &Path) -> Result<Snapshot, Failure> {
    let mut archive = open_archive(path)?;
    let mut entries = Snapshot::new();
    for index in 0..archive.len() {
        let mut entry = archive.by_index(index).map_err(|e| Failure::io(path, e))?;
        let name = entry.name().to_owned();
        let bytes = if entry.is_dir() {
            None
        } else {
            let mut bytes = Vec::new();
            entry
                .read_to_end(&mut bytes)
                .map_err(|e| Failure::io(path, e))?;
            Some(bytes)
        };
        if entries.insert(name.clone(), bytes).is_some() {
            return Err(Failure::Mismatch(format!(
                "duplicate archive entry {name:?}"
            )));
        }
    }
    Ok(entries)
}

fn unpack(path: &Path, destination: &Path) -> Result<(), Failure> {
    let mut archive = open_archive(path)?;
    for index in 0..archive.len() {
        let mut entry = archive.by_index(index).map_err(|e| Failure::io(path, e))?;
        if entry.is_dir() {
            continue;
        }
        let name = entry.enclosed_name().ok_or_else(|| {
            Failure::Execution(format!(
                "invalid archive path {:?} in {}",
                entry.name(),
                path.display()
            ))
        })?;
        let output = destination.join(name);
        let parent = output.parent().expect("archive output without a parent");
        fs::create_dir_all(parent).map_err(|e| Failure::io(parent, e))?;
        let mut file = File::create(&output).map_err(|e| Failure::io(&output, e))?;
        io::copy(&mut entry, &mut file).map_err(|e| Failure::io(&output, e))?;
    }
    Ok(())
}
