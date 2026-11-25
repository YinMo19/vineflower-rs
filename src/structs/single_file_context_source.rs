// Copyright 2000-2022 JetBrains s.r.o. and the ForgeFlower contributors.
// SPDX-License-Identifier: Apache-2.0

//! SingleFileContextSource registers a class by its internal name, regardless
//! of the name of the file supplied on the command line.

use std::{
    fs, io,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::engine::{
    Options,
    context_source::{CLASS_SUFFIX, ContextSource, Entries, Entry},
};
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::structs::StructClass;
use crate::util::data_input::DataInputFullStream;
use arcstr::ArcStr;

pub struct SingleFileContextSource {
    path: PathBuf,
    contents: Option<Vec<u8>>,
    qualified_name: Option<ArcStr>,
}

impl SingleFileContextSource {
    pub fn open(
        path: &Path,
        options: &Options,
        interceptor: Option<Arc<PoolInterceptor>>,
    ) -> io::Result<Self> {
        let contents = path.is_file().then(|| fs::read(path)).transpose()?;
        let qualified_name = match &contents {
            Some(bytes)
                if path
                    .as_os_str()
                    .as_encoded_bytes()
                    .ends_with(CLASS_SUFFIX.as_bytes()) =>
            {
                Some(
                    StructClass::create(
                        &mut DataInputFullStream::new(bytes),
                        false,
                        options,
                        interceptor,
                    )?
                    .qualified_name,
                )
            }
            _ => None,
        };
        Ok(Self {
            path: path.into(),
            contents,
            qualified_name,
        })
    }
}

impl ContextSource for SingleFileContextSource {
    fn get_name(&self) -> String {
        format!("file {}", self.path.display())
    }

    fn get_entries(&self) -> Entries {
        let mut entries = Entries::default();
        if let Some(name) = &self.qualified_name {
            entries.classes.push(Entry::at_base(name));
        } else if self.contents.is_some()
            && let Some(name) = self.path.file_name()
        {
            entries.others.push(Entry::at_base(&name.to_string_lossy()));
        }
        entries
    }

    fn get_input_stream(&self, _resource: &str) -> io::Result<Option<Vec<u8>>> {
        Ok(self.contents.clone())
    }
}
