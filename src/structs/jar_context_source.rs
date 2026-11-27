//! The input side of `JarContextSource`, including other ZIP-based archives.

use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};

use flate2::read::DeflateDecoder;
use indexmap::IndexSet;
use rawzip::{CompressionMethod, FileReader, ZipArchive, ZipArchiveEntryWayfinder};
use rustc_hash::FxHashMap;

use super::struct_context::invalid_source;
use crate::engine::context_source::{CLASS_SUFFIX, ContextSource, Entries, Entry, OutputLayout};

pub struct JarContextSource {
    path: PathBuf,
    relative_path: String,
    entries: Entries,
    archive: ZipArchive<FileReader>,
    files: FxHashMap<String, (ZipArchiveEntryWayfinder, CompressionMethod)>,
}

impl JarContextSource {
    pub fn open(path: &Path) -> io::Result<Self> {
        Self::open_nested(path, String::new())
    }

    pub(super) fn open_nested(path: &Path, relative_path: String) -> io::Result<Self> {
        Self::open_archive(path, relative_path)
            .map_err(|error| invalid_source("archive", path, error))
    }

    fn open_archive(path: &Path, relative_path: String) -> io::Result<Self> {
        let absolute_path: PathBuf = std::path::absolute(path)?.components().collect();
        let file = File::open(&absolute_path)?;
        let mut buffer = vec![0; rawzip::MAX_CENTRAL_DIRECTORY_RECORD_SIZE];
        let archive = ZipArchive::from_file(file, &mut buffer).map_err(zip_error)?;
        let mut central = archive.entries(&mut buffer);
        let mut entries = Entries::default();
        let mut directories = IndexSet::new();
        let mut files = FxHashMap::default();
        while let Some(entry) = central.next_entry().map_err(zip_error)? {
            let method = entry.compression_method();
            if entry.flags().is_encrypted()
                || !matches!(
                    method,
                    CompressionMethod::STORE | CompressionMethod::DEFLATE
                )
            {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "Java ZipFile requires unencrypted stored or deflated ZIP entries",
                ));
            }
            let name = std::str::from_utf8(entry.file_path().as_bytes())
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
            for (offset, _) in name.match_indices('/') {
                directories.insert(name[..offset].to_owned());
            }
            if name.ends_with('/') {
                directories.insert(name.to_owned());
                continue;
            }
            if let Some(class) = name.strip_suffix(CLASS_SUFFIX) {
                entries.classes.push(Entry::try_parse(class)?);
            } else {
                entries.others.push(Entry::try_parse(name)?);
            }
            // ZipFile enumerates every entry but resolves a name to its last occurrence.
            files.insert(name.to_owned(), (entry.wayfinder(), method));
        }
        entries.directories = directories.into_iter().collect();

        Ok(Self {
            path: absolute_path,
            relative_path,
            entries,
            archive,
            files,
        })
    }

    /// The archive's containing directory relative to the output base.
    pub fn relative_path(&self) -> &str {
        &self.relative_path
    }
}

impl ContextSource for JarContextSource {
    fn get_name(&self) -> String {
        format!("archive {}", self.path.display())
    }

    fn get_entries(&self) -> Entries {
        self.entries.clone()
    }

    fn output_layout(&self) -> OutputLayout {
        OutputLayout::Archive {
            name: self
                .path
                .file_name()
                .unwrap()
                .to_string_lossy()
                .into_owned(),
            directory: self
                .relative_path
                .trim_start_matches(std::path::is_separator)
                .to_owned(),
        }
    }

    fn get_input_stream(&self, resource: &str) -> io::Result<Option<Vec<u8>>> {
        let Some(&(location, method)) = self.files.get(resource) else {
            return Ok(None);
        };
        let entry = self.archive.get_entry(location).map_err(zip_error)?;
        let mut bytes = Vec::new();
        if method == CompressionMethod::DEFLATE {
            DeflateDecoder::new(entry.reader()).read_to_end(&mut bytes)?;
        } else {
            entry.reader().read_to_end(&mut bytes)?;
        }
        Ok(Some(bytes))
    }
}

fn zip_error(error: rawzip::Error) -> io::Error {
    let kind = match error.kind() {
        rawzip::ErrorKind::IO(cause) => cause.kind(),
        rawzip::ErrorKind::Eof => io::ErrorKind::UnexpectedEof,
        _ => io::ErrorKind::InvalidData,
    };
    io::Error::new(kind, error)
}

pub(super) fn has_archive_extension(path: &Path) -> bool {
    let name = path.as_os_str().as_encoded_bytes();
    name.ends_with(b".jar") || name.ends_with(b".zip")
}

pub(super) fn is_jar_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    if has_archive_extension(path) {
        return true;
    }
    if path
        .as_os_str()
        .as_encoded_bytes()
        .ends_with(CLASS_SUFFIX.as_bytes())
    {
        return false;
    }
    match zip_end_record(path) {
        Ok(found) => found,
        Err(error) => {
            log::warn!(
                "Could not determine if {} contains a JAR file: {error}",
                path.display()
            );
            false
        }
    }
}

fn zip_end_record(path: &Path) -> io::Result<bool> {
    const EOCD: [u8; 4] = *b"PK\x05\x06";
    const MINIMUM_LENGTH: usize = 22;
    const MAXIMUM_SEARCH: usize = 1024;
    let mut file = File::open(path)?;
    let size = file.metadata()?.len();
    if size < MINIMUM_LENGTH as u64 {
        return Ok(false);
    }
    let length = (size & !3).min(MAXIMUM_SEARCH as u64);
    let mut buffer = [0; MAXIMUM_SEARCH];
    let tail = &mut buffer[..length as usize];
    file.seek(SeekFrom::Start(size - length))?;
    file.read_exact(tail)?;
    Ok(tail
        .windows(EOCD.len())
        .take(tail.len().saturating_sub(MINIMUM_LENGTH - 1))
        .any(|bytes| bytes == EOCD))
}
