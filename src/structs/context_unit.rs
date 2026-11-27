//! `struct.ContextUnit`: a context source with the role it plays in the
//! decompilation — decompiled itself, or only a library.
//!
//! Upstream lists the entries of a unit on first use; here they are listed
//! when the unit is created, which is when the struct context scans it.

use std::io;
use std::sync::Arc;

use super::struct_class::StructClass;
use crate::engine::Options;
use crate::engine::context_source::{ContextSource, Entry};
use crate::engine::counter_container::ExpressionIds;
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::util::data_input::DataInputFullStream;

pub struct ContextUnit {
    pub source: Arc<dyn ContextSource>,
    pub own: bool,
    pub root: bool,
    /// class file or jar/zip entry
    pub class_entries: Vec<String>,
    pub dir_entries: Vec<String>,
    pub other_entries: Vec<Entry>,
    pub child_contexts: Vec<Arc<dyn ContextSource>>,
    /// The contents of each `fernflower_abstract_parameter_names.txt` in the unit.
    pub abstract_metadata: Vec<String>,
}

impl ContextUnit {
    pub fn new(source: Arc<dyn ContextSource>, own: bool, root: bool, options: &Options) -> Self {
        Self::try_new(source, own, root, options).expect("Could not list context entries")
    }

    pub(super) fn try_new(
        source: Arc<dyn ContextSource>,
        own: bool,
        root: bool,
        options: &Options,
    ) -> io::Result<Self> {
        let mut unit = ContextUnit {
            source,
            own,
            root,
            class_entries: Vec::new(),
            dir_entries: Vec::new(),
            other_entries: Vec::new(),
            child_contexts: Vec::new(),
            abstract_metadata: Vec::new(),
        };
        if unit.is_lazy() {
            return Ok(unit);
        }

        let entries = unit.source.try_get_entries()?;
        // TODO: more proper handling of multirelease jars, rather than just stripping them
        unit.class_entries = entries
            .classes
            .into_iter()
            .filter(|entry| entry.multirelease == Entry::BASE_VERSION)
            .map(|entry| entry.base_path)
            .collect();
        unit.dir_entries = entries.directories;

        let include_extras = !options.skip_extra_files;
        for entry in entries.others {
            if entry.base_path == "fernflower_abstract_parameter_names.txt" {
                match unit.source.get_input_stream(&entry.path()) {
                    Ok(data) => unit
                        .abstract_metadata
                        .push(String::from_utf8_lossy(&data.unwrap_or_default()).into_owned()),
                    Err(error) => {
                        log::error!("Failed to load abstract parameter names file: {error}");
                    }
                }
            } else if include_extras {
                unit.other_entries.push(entry);
            }
        }
        unit.child_contexts = entries.child_contexts;

        Ok(unit)
    }

    pub fn has_class(&self, class_name: &str) -> io::Result<bool> {
        self.source.has_class(class_name)
    }

    pub fn get_class_bytes(&self, class_name: &str) -> io::Result<Option<Vec<u8>>> {
        self.source.get_class_bytes(class_name)
    }

    pub fn try_load_class(
        &self,
        class_name: &str,
        options: &Options,
        interceptor: Option<Arc<PoolInterceptor>>,
    ) -> io::Result<Option<StructClass>> {
        self.try_load_class_with_ids(class_name, options, interceptor, &ExpressionIds::default())
    }

    pub(crate) fn try_load_class_with_ids(
        &self,
        class_name: &str,
        options: &Options,
        interceptor: Option<Arc<PoolInterceptor>>,
        ids: &ExpressionIds,
    ) -> io::Result<Option<StructClass>> {
        let Some(data) = self.get_class_bytes(class_name)? else {
            return Ok(None);
        };
        StructClass::create_with_ids(
            &mut DataInputFullStream::new(&data),
            self.own,
            options,
            interceptor,
            ids,
        )
        .map(Some)
    }

    pub fn get_name(&self) -> String {
        self.source.get_name()
    }

    pub fn is_lazy(&self) -> bool {
        !self.own && self.source.is_lazy()
    }
}
