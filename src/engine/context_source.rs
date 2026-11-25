// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `main.extern.IContextSource`: a place classes are read from — a
//! directory, an archive, a single file, a runtime image.

use std::io;
use std::sync::Arc;

/// The file extension for class files.
pub const CLASS_SUFFIX: &str = ".class";

/// A specific type of context unit.
///
/// Implementations do not need to cache the results of any provided methods.
pub trait ContextSource: Send + Sync {
    /// A human-readable name to identify this context source.
    fn get_name(&self) -> String;

    /// A listing of all entries in this context unit.
    fn get_entries(&self) -> Entries;

    /// Whether this context source is lazy. A lazy context source may return
    /// no entries from [`get_entries`](Self::get_entries) in case listing
    /// them would be too slow. This may come at a small runtime cost.
    ///
    /// Only libraries can be lazy. This method has no effect on sources.
    fn is_lazy(&self) -> bool {
        false
    }

    /// Whether a class exists in this source. `class_name` has no trailing `/`.
    fn has_class(&self, class_name: &str) -> io::Result<bool> {
        Ok(self.get_class_bytes(class_name)?.is_some())
    }

    /// The full bytes of a class's contents, or `None` if no class with
    /// that name is present.
    fn get_class_bytes(&self, class_name: &str) -> io::Result<Option<Vec<u8>>> {
        self.get_input_stream(&format!("{class_name}{CLASS_SUFFIX}"))
    }

    /// The contents of a specific resource, or `None` if there is none or a
    /// directory is requested.
    fn get_input_stream(&self, resource: &str) -> io::Result<Option<Vec<u8>>>;
}

/// All entries in the context unit.
#[derive(Clone, Default)]
pub struct Entries {
    /// Class names, with no `.class` suffix.
    pub classes: Vec<Entry>,
    /// Directories, with no trailing `/`.
    pub directories: Vec<String>,
    pub others: Vec<Entry>,
    /// Contexts discovered within this context.
    pub child_contexts: Vec<Arc<dyn ContextSource>>,
}

/// An entry in a context unit, which may be a multirelease variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// The path of the entry, with any multirelease variant stripped.
    pub base_path: String,
    /// The multirelease target version, or [`Entry::BASE_VERSION`] to
    /// indicate this entry is not part of a multirelease variant.
    pub multirelease: i32,
}

impl Entry {
    pub const BASE_VERSION: i32 = -1;
    const MULTIRELEASE_PREFIX: &'static str = "META-INF/versions/";

    /// Parse an entry from a raw jar path; it may indicate a multirelease resource.
    pub fn parse(path: &str) -> Entry {
        let versioned = path
            .strip_prefix(Self::MULTIRELEASE_PREFIX)
            .and_then(|rest| rest.split_once('/'))
            .and_then(|(version, _)| {
                let multirelease = parse_java_int(version)?;
                let next_slash = Self::MULTIRELEASE_PREFIX.len() + version.len();
                Some(Entry::new(&path[next_slash..], multirelease))
            });
        // unversioned
        versioned.unwrap_or_else(|| Entry::at_base(path))
    }

    /// An entry at the base version, without attempting to parse any
    /// multirelease information.
    pub fn at_base(path: &str) -> Entry {
        Entry::new(path, Self::BASE_VERSION)
    }

    pub fn new(base_path: &str, multirelease: i32) -> Entry {
        if multirelease != -1 && multirelease < 9 {
            panic!("A multirelease variant must target a Java runtime >= 9");
        }
        Entry {
            base_path: base_path.to_owned(),
            multirelease,
        }
    }

    pub fn path(&self) -> String {
        if self.multirelease == Self::BASE_VERSION {
            self.base_path.clone()
        } else {
            format!(
                "{}{}/{}",
                Self::MULTIRELEASE_PREFIX,
                self.multirelease,
                self.base_path
            )
        }
    }
}

/// `Integer.parseInt`, which accepts a sign but no surrounding text.
fn parse_java_int(text: &str) -> Option<i32> {
    text.parse().ok()
}
