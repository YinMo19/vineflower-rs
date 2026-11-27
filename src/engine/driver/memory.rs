use std::io;

use indexmap::{IndexMap, IndexSet};

use crate::engine::context_source::{CLASS_SUFFIX, ContextSource, Entries, Entry};

/// Class files already read by an embedding application. Keys are the
/// JVM's slash-separated internal names without the `.class` suffix.
pub struct MemorySource {
    name: String,
    classes: IndexMap<String, Vec<u8>>,
}

impl MemorySource {
    pub fn new(
        name: impl Into<String>,
        classes: impl IntoIterator<Item = (String, Vec<u8>)>,
    ) -> Self {
        Self {
            name: name.into(),
            classes: classes.into_iter().collect(),
        }
    }
}

impl ContextSource for MemorySource {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn get_entries(&self) -> Entries {
        let mut entries = Entries::default();
        let mut directories = IndexSet::new();
        for name in self.classes.keys() {
            entries.classes.push(Entry::at_base(name));
            for (index, _) in name.match_indices('/') {
                directories.insert(name[..index].to_owned());
            }
        }
        entries.directories = directories.into_iter().collect();
        entries
    }

    fn has_class(&self, name: &str) -> io::Result<bool> {
        Ok(self.classes.contains_key(name))
    }

    fn get_class_bytes(&self, name: &str) -> io::Result<Option<Vec<u8>>> {
        Ok(self.classes.get(name).cloned())
    }

    fn get_input_stream(&self, resource: &str) -> io::Result<Option<Vec<u8>>> {
        Ok(resource
            .strip_suffix(CLASS_SUFFIX)
            .and_then(|name| self.classes.get(name))
            .cloned())
    }
}
