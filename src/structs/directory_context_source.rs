// Copyright 2000-2022 JetBrains s.r.o. and the ForgeFlower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Recursively discover classes, resources and nested archives in a folder.

use std::fs;
use std::io;
use std::path::{MAIN_SEPARATOR, Path, PathBuf, is_separator};
use std::sync::Arc;

use super::jar_context_source::{JarContextSource, has_archive_extension};
use crate::engine::context_source::{CLASS_SUFFIX, ContextSource, Entries, Entry};

pub struct DirectoryContextSource {
    base: PathBuf,
}

impl DirectoryContextSource {
    pub fn open(base: &Path) -> io::Result<Self> {
        Ok(Self {
            base: std::path::absolute(base)?.components().collect(),
        })
    }

    fn collect_entries(&self, current: &Path, entries: &mut Entries) -> io::Result<()> {
        let relative = current
            .strip_prefix(&self.base)
            .expect("Directory entries must be within their base");
        let relative = relative.to_string_lossy();
        if current.is_dir() {
            entries.directories.push(relative.into_owned());
            for child in fs::read_dir(current)? {
                self.collect_entries(&child?.path(), entries)?;
            }
        } else if let Some(class) = relative.strip_suffix(CLASS_SUFFIX) {
            entries
                .classes
                .push(Entry::at_base(&class.replace(MAIN_SEPARATOR, "/")));
        } else if has_archive_extension(current) {
            let base = self.base.to_string_lossy();
            let parent = current.parent().expect("Nested archive has no directory");
            let parent = parent.to_string_lossy();
            let relative_path = parent
                .strip_prefix(base.as_ref())
                .expect("Archive parent is outside its base");
            let source = JarContextSource::open_nested(current, relative_path.to_owned())?;
            entries.child_contexts.push(Arc::new(source));
        } else {
            entries
                .others
                .push(Entry::at_base(&relative.replace(MAIN_SEPARATOR, "/")));
        }
        Ok(())
    }
}

impl ContextSource for DirectoryContextSource {
    fn get_name(&self) -> String {
        format!("directory {}", self.base.display())
    }

    fn get_entries(&self) -> Entries {
        self.try_get_entries()
            .expect("Could not list directory entries")
    }

    fn try_get_entries(&self) -> io::Result<Entries> {
        let mut entries = Entries::default();
        self.collect_entries(&self.base, &mut entries)?;
        Ok(entries)
    }

    fn get_input_stream(&self, resource: &str) -> io::Result<Option<Vec<u8>>> {
        let path = self.base.join(resource.trim_start_matches(is_separator));
        match path.metadata() {
            Ok(metadata) if !metadata.is_file() => Ok(None),
            Ok(_) => fs::read(path).map(Some),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }
}
