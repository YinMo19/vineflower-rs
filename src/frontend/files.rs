// Based on Vineflower's context sources and console result savers.
// Copyright 2000-2022 JetBrains s.r.o. and ForgeFlower contributors.
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet, btree_map::Entry as MapEntry};
use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::ops::Bound::{Included, Unbounded};
use std::path::{Path, PathBuf};

use tempfile::NamedTempFile;
use thiserror::Error;
use zip::result::ZipError;
use zip::write::SimpleFileOptions;
use zip::{CompressionMethod, DateTime, ZipArchive, ZipWriter};

use super::{Destination, is_archive};
use crate::{
    ClassGroup, ClassGroupBuilder, DecompileError, LogLevel, Options, classfile::ClassError,
    naming::MemberRenames,
};

const MANIFEST: &str = "META-INF/MANIFEST.MF";

#[derive(Debug, Error)]
pub(super) enum FrontendError {
    #[error("--file, --folder and --legacy-saving require a destination path other than stdout")]
    MissingDestination,
    #[error("-cfg requires a config file path")]
    MissingConfig,
    #[error("unsupported symbolic link or special entry '{0}'")]
    UnsupportedEntry(String),
    #[error("invalid entry path {name:?} in '{input}'")]
    InvalidEntry { name: String, input: PathBuf },
    #[error("entry '{0}' is not a Unicode path")]
    NonUnicodeEntry(PathBuf),
    #[error("duplicate output entry '{0}'")]
    DuplicateEntry(String),
    #[error("output entry '{0}' is both a file and a directory")]
    EntryTypeConflict(String),
    #[error("output path '{0}' is not a real directory")]
    OutputDirectoryConflict(PathBuf),
    #[error("cannot use input archive '{0}' as its own destination")]
    SameArchive(PathBuf),
    #[error("cannot {action} '{location}': {source}")]
    Io {
        action: &'static str,
        location: String,
        #[source]
        source: io::Error,
    },
    #[error("cannot {action} archive '{location}': {source}")]
    Archive {
        action: &'static str,
        location: String,
        #[source]
        source: ZipError,
    },
    #[error("cannot decompile '{input}': {source}")]
    Decompile {
        input: String,
        #[source]
        source: DecompileError,
    },
    #[error("cannot build class group: {0}")]
    ClassGroup(#[source] ClassError),
}

type Result<T, E = FrontendError> = std::result::Result<T, E>;

pub(super) fn io_error(action: &'static str, path: &Path, source: io::Error) -> FrontendError {
    FrontendError::Io {
        action,
        location: path.display().to_string(),
        source,
    }
}

fn archive_location(path: &Path, entry: &str) -> String {
    format!("{}!{entry}", path.display())
}

fn archive_error(action: &'static str, location: String, source: ZipError) -> FrontendError {
    FrontendError::Archive {
        action,
        location,
        source,
    }
}

struct ArchiveInput {
    path: PathBuf,
    reader: ZipArchive<BufReader<File>>,
}

enum Input {
    File {
        path: PathBuf,
        size: u64,
    },
    Archive {
        archive: usize,
        index: usize,
        size: u64,
    },
}

impl Input {
    fn archive(&self) -> Option<usize> {
        match self {
            Self::File { .. } => None,
            Self::Archive { archive, .. } => Some(*archive),
        }
    }

    fn size(&self) -> u64 {
        match self {
            Self::File { size, .. } | Self::Archive { size, .. } => *size,
        }
    }

    fn identify(&self, archives: &[ArchiveInput]) -> String {
        match self {
            Self::File { path, .. } => path.display().to_string(),
            Self::Archive { archive, index, .. } => {
                let archive = &archives[*archive];
                let name = archive
                    .reader
                    .name_for_index(*index)
                    .expect("indexed entry");
                archive_location(&archive.path, name)
            }
        }
    }

    fn read<T>(
        &self,
        archives: &mut [ArchiveInput],
        action: &'static str,
        consume: impl FnOnce(&mut dyn Read) -> io::Result<T>,
    ) -> Result<T> {
        match self {
            Self::File { path, .. } => {
                let mut file = File::open(path).map_err(|error| io_error("open", path, error))?;
                consume(&mut file).map_err(|error| io_error(action, path, error))
            }
            Self::Archive { archive, index, .. } => {
                let ArchiveInput { path, reader } = &mut archives[*archive];
                let mut file = reader.by_index(*index).map_err(|error| {
                    archive_error(
                        "open entry from",
                        format!("{} (entry #{index})", path.display()),
                        error,
                    )
                })?;
                consume(&mut file).map_err(|source| FrontendError::Io {
                    action,
                    location: archive_location(path, file.name()),
                    source,
                })
            }
        }
    }
}

enum Entry {
    Directory,
    Resource(Input),
    Class { name: String, input: Input },
    GeneratedArchive(usize),
}

impl Entry {
    fn is_directory(&self) -> bool {
        matches!(self, Self::Directory)
    }

    fn is_class(&self) -> bool {
        matches!(self, Self::Class { .. })
    }
}

type Entries = BTreeMap<String, Entry>;

struct ClassInput {
    entry_name: Option<String>,
    input: Input,
    own: bool,
}

pub(super) struct Selection {
    pub libraries: Vec<PathBuf>,
    pub only: Vec<String>,
    pub skip_extra_files: bool,
}

struct Inputs {
    entries: Entries,
    archives: Vec<ArchiveInput>,
    archive_outputs: BTreeMap<usize, Entries>,
    classes: Vec<ClassInput>,
    renames: MemberRenames,
    legacy: bool,
    archive_output: bool,
    skip_extra_files: bool,
}

impl Inputs {
    fn new(destination: &Destination, skip_extra_files: bool) -> Self {
        Self {
            entries: Entries::new(),
            archives: Vec::new(),
            archive_outputs: BTreeMap::new(),
            classes: Vec::new(),
            renames: MemberRenames::default(),
            legacy: matches!(destination, Destination::Legacy(_)),
            archive_output: matches!(
                destination,
                Destination::Archive(_) | Destination::Legacy(_)
            ),
            skip_extra_files,
        }
    }

    fn add(&mut self, path: PathBuf, metadata: fs::Metadata, own: bool) -> Result<()> {
        if metadata.is_dir() {
            return self.add_directory(&path, &path, own);
        }
        if !metadata.is_file() {
            return Err(FrontendError::UnsupportedEntry(path.display().to_string()));
        }
        if path.extension().is_some_and(|ext| ext == "class") {
            self.classes.push(ClassInput {
                entry_name: None,
                input: Input::File {
                    path,
                    size: metadata.len(),
                },
                own,
            });
            return Ok(());
        }

        let file = File::open(&path).map_err(|error| io_error("open", &path, error))?;
        let archive = match ZipArchive::new(BufReader::new(file)) {
            Ok(reader) => Some(reader),
            Err(ZipError::InvalidArchive(_)) if !is_archive(&path) => None,
            Err(error) => return Err(archive_error("read", path.display().to_string(), error)),
        };
        if let Some(reader) = archive {
            let name = if self.legacy && own {
                Some(basename(&path)?.to_owned())
            } else {
                None
            };
            self.add_archive(path, reader, name, own)
        } else if own && !self.skip_extra_files {
            let name = basename(&path)?.to_owned();
            insert(
                &mut self.entries,
                name,
                Entry::Resource(Input::File {
                    path,
                    size: metadata.len(),
                }),
            )
        } else {
            Ok(())
        }
    }

    fn add_directory(&mut self, root: &Path, path: &Path, own: bool) -> Result<()> {
        let mut children: Vec<_> = fs::read_dir(path)
            .map_err(|error| io_error("list directory", path, error))?
            .map(|entry| entry.map(|entry| (entry.path(), entry)))
            .collect::<io::Result<_>>()
            .map_err(|error| io_error("list directory", path, error))?;
        children.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        for (path, child) in children {
            let relative = path.strip_prefix(root).expect("entry under input root");
            let name = relative_name(relative, root)?;
            let file_type = child
                .file_type()
                .map_err(|error| io_error("inspect", &path, error))?;
            if file_type.is_dir() {
                if own {
                    insert(&mut self.entries, name, Entry::Directory)?;
                }
                self.add_directory(root, &path, own)?;
            } else if file_type.is_file() {
                if is_archive(&path) {
                    let file = File::open(&path).map_err(|error| io_error("open", &path, error))?;
                    let reader = ZipArchive::new(BufReader::new(file)).map_err(|error| {
                        archive_error("read", path.display().to_string(), error)
                    })?;
                    let legacy_name = (self.legacy && own).then_some(name);
                    self.add_archive(path, reader, legacy_name, own)?;
                    continue;
                }
                if !name.ends_with(".class") && (!own || self.skip_extra_files) {
                    continue;
                }
                let size = child
                    .metadata()
                    .map_err(|error| io_error("read metadata for", &path, error))?
                    .len();
                let input = Input::File { path, size };
                self.add_entry(name, input, own)?;
            } else {
                return Err(FrontendError::UnsupportedEntry(path.display().to_string()));
            }
        }
        Ok(())
    }

    fn add_archive(
        &mut self,
        path: PathBuf,
        mut reader: ZipArchive<BufReader<File>>,
        legacy_name: Option<String>,
        own: bool,
    ) -> Result<()> {
        let archive = self.archives.len();
        if let Some(name) = legacy_name {
            insert(&mut self.entries, name, Entry::GeneratedArchive(archive))?;
            self.archive_outputs.insert(archive, Entries::new());
        }
        for index in 0..reader.len() {
            let file = reader.by_index_raw(index).map_err(|error| {
                archive_error(
                    "inspect entry from",
                    format!("{} (entry #{index})", path.display()),
                    error,
                )
            })?;
            let name = file.name();
            if !own && !name.ends_with(".class") {
                continue;
            }
            if file.is_symlink() {
                return Err(FrontendError::UnsupportedEntry(archive_location(
                    &path, name,
                )));
            }
            if file.is_dir() {
                if own {
                    let name = name.strip_suffix('/').unwrap_or(name);
                    validate_entry_name(name, &path)?;
                    insert(
                        self.output_entries(Some(archive)),
                        name.to_owned(),
                        Entry::Directory,
                    )?;
                }
            } else {
                validate_entry_name(name, &path)?;
                if own && let Some((parent, _)) = name.rsplit_once('/') {
                    let entries = self.output_entries(Some(archive));
                    if !entries.get(parent).is_some_and(Entry::is_directory) {
                        insert(entries, parent.to_owned(), Entry::Directory)?;
                    }
                }
                self.add_entry(
                    name.to_owned(),
                    Input::Archive {
                        archive,
                        index,
                        size: file.size(),
                    },
                    own,
                )?;
            }
        }
        self.archives.push(ArchiveInput { path, reader });
        Ok(())
    }

    fn add_entry(&mut self, name: String, input: Input, own: bool) -> Result<()> {
        if name.ends_with(".class") {
            // Vineflower currently loads only the base archive view. Versioned
            // resources still retain their original physical input names.
            if !is_versioned(&name) {
                self.classes.push(ClassInput {
                    entry_name: Some(name),
                    input,
                    own,
                });
            }
        } else if own
            && (!self.skip_extra_files
                || self.archive_output && input.archive().is_some() && name == MANIFEST)
        {
            insert(
                self.output_entries(input.archive()),
                name,
                Entry::Resource(input),
            )?;
        }
        Ok(())
    }

    fn output_entries(&mut self, archive: Option<usize>) -> &mut Entries {
        if let Some(entries) = archive.and_then(|archive| self.archive_outputs.get_mut(&archive)) {
            entries
        } else {
            &mut self.entries
        }
    }

    fn prepare_sources<'a>(
        &mut self,
        classes: Vec<ClassInput>,
        bytes: &'a [Vec<u8>],
        options: &Options,
        only: &[String],
    ) -> Result<ClassGroup<'a>> {
        let selected =
            |name: &str| only.is_empty() || only.iter().any(|prefix| name.starts_with(prefix));
        let mut builder = ClassGroupBuilder::new();
        let mut sources = BTreeMap::new();
        for (class, bytes) in classes.into_iter().zip(bytes) {
            let name = if !class.own {
                builder.add_library(bytes)
            } else if only.is_empty() {
                builder.add(bytes)
            } else {
                builder.add_with_source_filter(bytes, selected)
            }
            .map_err(|source| self.class_error(&class.input, source.into()))?;
            if class.own && selected(&name) {
                sources.entry(name).or_insert(class);
            }
        }
        let group = builder.build().map_err(FrontendError::ClassGroup)?;
        self.renames = MemberRenames::build(&group, options).map_err(FrontendError::ClassGroup)?;
        for (
            name,
            ClassInput {
                entry_name, input, ..
            },
        ) in sources
        {
            if options.decompile_inner && !group.is_root(&name) {
                continue;
            }
            let (extension, source_basename) = group
                .output_file_parts(&name, options)
                .map_err(|error| self.class_error(&input, error))?;
            let actual = self.renames.class_name(&name);
            let basename = source_basename.unwrap_or_else(|| actual.rsplit('/').next().expect("class name"));
            let output_name = if let Some(mut entry_name) = entry_name {
                if actual == name && source_basename.is_none() {
                    entry_name.truncate(entry_name.len() - "class".len());
                } else {
                    let prefix_len = entry_name.rfind('/').map_or(0, |slash| slash + 1);
                    entry_name.truncate(prefix_len);
                    entry_name.push_str(basename);
                    entry_name.push('.');
                }
                entry_name.push_str(extension);
                entry_name
            } else {
                // Standalone inputs are written at the output root. Kotlin
                // file facades retain their original basename for recompilation.
                let Input::File { path, .. } = &input else {
                    unreachable!()
                };
                validate_entry_name(basename, path)?;
                format!("{basename}.{extension}")
            };
            insert(
                self.output_entries(input.archive()),
                output_name,
                Entry::Class { name, input },
            )?;
        }
        Ok(group)
    }

    fn class_error(&self, input: &Input, source: DecompileError) -> FrontendError {
        FrontendError::Decompile {
            input: input.identify(&self.archives),
            source,
        }
    }

    fn retain_directories(&mut self, only: &[String]) {
        if only.is_empty() {
            return;
        }
        for entries in std::iter::once(&mut self.entries).chain(self.archive_outputs.values_mut()) {
            let discarded: Vec<_> = entries
                .iter()
                .filter(|(name, entry)| {
                    entry.is_directory()
                        && !only.iter().any(|prefix| name.starts_with(prefix))
                        && !entries
                            .range::<str, _>((Included(name.as_str()), Unbounded))
                            .take_while(|(path, _)| path.starts_with(name.as_str()))
                            .any(|(_, entry)| {
                                matches!(entry, Entry::Resource(_) | Entry::GeneratedArchive(_))
                            })
                })
                .map(|(name, _)| name.clone())
                .collect();
            for name in discarded {
                entries.remove(&name);
            }
        }
    }

    fn write_directory(
        mut self,
        root: &Path,
        group: &ClassGroup<'_>,
        options: &Options,
    ) -> Result<()> {
        let directories = directories(&self.entries)?;
        fs::create_dir_all(root)
            .map_err(|error| io_error("create output directory", root, error))?;
        for name in directories {
            let path = root.join(name);
            match fs::create_dir(&path) {
                Ok(()) => {}
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    let metadata = fs::symlink_metadata(&path)
                        .map_err(|error| io_error("inspect output directory", &path, error))?;
                    if !metadata.is_dir() {
                        return Err(FrontendError::OutputDirectoryConflict(path));
                    }
                }
                Err(error) => return Err(io_error("create output directory", &path, error)),
            }
        }
        for (name, entry) in std::mem::take(&mut self.entries) {
            if entry.is_directory() {
                continue;
            }
            let path = root.join(name);
            if let Entry::GeneratedArchive(archive) = entry {
                let entries = self
                    .archive_outputs
                    .remove(&archive)
                    .expect("indexed archive");
                self.write_archive(entries, &path, group, options)?;
                continue;
            }
            let mut temp = create_output(&path)?;
            self.write_contents(&entry, &mut temp, group, options, &path)?;
            persist(temp, &path)?;
        }
        Ok(())
    }

    fn write_archive(
        &mut self,
        entries: Entries,
        path: &Path,
        group: &ClassGroup<'_>,
        options: &Options,
    ) -> Result<()> {
        if let Ok(target) = fs::canonicalize(path)
            && self
                .archives
                .iter()
                .any(|archive| fs::canonicalize(&archive.path).is_ok_and(|source| source == target))
        {
            return Err(FrontendError::SameArchive(path.to_owned()));
        }
        let directories = directories(&entries)?;
        let parent = output_parent(path);
        fs::create_dir_all(parent)
            .map_err(|error| io_error("create output directory", parent, error))?;
        let mut temp = create_output(path)?;
        let mut writer = ZipWriter::new(BufWriter::new(temp.as_file_mut()));
        let settings = SimpleFileOptions::default()
            .compression_method(CompressionMethod::Deflated)
            .last_modified_time(DateTime::default());
        // JarInputStream only recognizes a manifest at the start of an archive.
        let manifest = entries.get_key_value(MANIFEST);
        let files = entries.iter().filter(|(name, _)| name.as_str() != MANIFEST);
        for (name, entry) in manifest.into_iter().chain(files) {
            if entry.is_directory() {
                continue;
            }
            let large =
                matches!(&entry, Entry::Resource(input) if input.size() >= u64::from(u32::MAX));
            writer
                .start_file(name, settings.large_file(large))
                .map_err(|error| {
                    archive_error("create entry in", archive_location(path, name), error)
                })?;
            self.write_contents(entry, &mut writer, group, options, path)?;
        }
        if self.legacy {
            for name in directories {
                writer.add_directory(name, settings).map_err(|error| {
                    archive_error("create directory in", archive_location(path, name), error)
                })?;
            }
        }
        writer
            .finish()
            .map_err(|error| archive_error("finish", path.display().to_string(), error))?
            .flush()
            .map_err(|error| io_error("flush archive", path, error))?;
        persist(temp, path)
    }

    fn write_stdout(
        mut self,
        stdout: &mut impl Write,
        group: &ClassGroup<'_>,
        options: &Options,
    ) -> Result<()> {
        directories(&self.entries)?;
        let path = Path::new("<stdout>");
        for (name, entry) in std::mem::take(&mut self.entries) {
            if !entry.is_class() {
                continue;
            }
            writeln!(stdout, "==== {name} ====").map_err(|error| io_error("write", path, error))?;
            self.write_contents(&entry, stdout, group, options, path)?;
            writeln!(stdout).map_err(|error| io_error("write", path, error))?;
        }
        stdout
            .flush()
            .map_err(|error| io_error("flush", path, error))
    }

    fn write_contents(
        &mut self,
        entry: &Entry,
        out: &mut impl Write,
        group: &ClassGroup<'_>,
        options: &Options,
        path: &Path,
    ) -> Result<()> {
        match entry {
            Entry::Class { name, input } => {
                let source = group
                    .decompile_with_renames(name, options, &self.renames)
                    .map_err(|error| self.class_error(input, error))?;
                out.write_all(source.text.as_bytes())
                    .map_err(|error| io_error("write", path, error))
            }
            Entry::Resource(input) => input
                .read(&mut self.archives, "copy resource", |file| {
                    io::copy(file, out)
                })
                .map(|_| ()),
            Entry::Directory | Entry::GeneratedArchive(_) => unreachable!("not a streamed file"),
        }
    }
}

fn insert(entries: &mut Entries, name: String, entry: Entry) -> Result<()> {
    match entries.entry(name) {
        MapEntry::Vacant(slot) => {
            slot.insert(entry);
            Ok(())
        }
        MapEntry::Occupied(slot) if slot.get().is_directory() && entry.is_directory() => Ok(()),
        MapEntry::Occupied(slot) if slot.get().is_directory() || entry.is_directory() => {
            Err(FrontendError::EntryTypeConflict(slot.key().clone()))
        }
        MapEntry::Occupied(slot) => Err(FrontendError::DuplicateEntry(slot.key().clone())),
    }
}

fn directories(entries: &Entries) -> Result<BTreeSet<&str>> {
    let mut directories = BTreeSet::new();
    for (name, entry) in entries {
        if entry.is_directory() {
            directories.insert(name.as_str());
        }
        let mut current = name.as_str();
        while let Some((parent, _)) = current.rsplit_once('/') {
            if !directories.insert(parent) {
                break;
            }
            if entries
                .get(parent)
                .is_some_and(|entry| !entry.is_directory())
            {
                return Err(FrontendError::EntryTypeConflict(parent.to_owned()));
            }
            current = parent;
        }
    }
    Ok(directories)
}

fn basename(path: &Path) -> Result<&str> {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| FrontendError::NonUnicodeEntry(path.to_owned()))?;
    validate_entry_name(name, path)?;
    Ok(name)
}

fn is_versioned(name: &str) -> bool {
    name.strip_prefix("META-INF/versions/")
        .and_then(|name| name.split_once('/'))
        .is_some_and(|(version, _)| version.parse::<i32>().is_ok_and(|version| version >= 9))
}

fn relative_name(relative: &Path, root: &Path) -> Result<String> {
    let mut name = String::new();
    for part in relative {
        let part = part
            .to_str()
            .ok_or_else(|| FrontendError::NonUnicodeEntry(root.join(relative)))?;
        if !name.is_empty() {
            name.push('/');
        }
        name.push_str(part);
    }
    validate_entry_name(&name, root)?;
    Ok(name)
}

fn validate_entry_name(name: &str, input: &Path) -> Result<()> {
    if name.contains(['\\', '\0', ':']) || name.split('/').any(unsafe_component) {
        return Err(FrontendError::InvalidEntry {
            name: name.to_owned(),
            input: input.to_owned(),
        });
    }
    Ok(())
}

fn unsafe_component(part: &str) -> bool {
    if matches!(part, "" | "." | "..") {
        return true;
    }
    #[cfg(windows)]
    {
        if part.ends_with(['.', ' '])
            || part.contains(['<', '>', '"', '|', '?', '*'])
            || part.bytes().any(|byte| byte.is_ascii_control())
        {
            return true;
        }
        let stem = part.split('.').next().unwrap_or(part).trim_end_matches(' ');
        if ["CON", "PRN", "AUX", "NUL", "CONIN$", "CONOUT$"]
            .iter()
            .any(|name| stem.eq_ignore_ascii_case(name))
        {
            return true;
        }
        if let (Some(base), Some(digit)) = (stem.get(..3), stem.get(3..))
            && (base.eq_ignore_ascii_case("COM") || base.eq_ignore_ascii_case("LPT"))
            && matches!(
                digit,
                "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" | "¹" | "²" | "³"
            )
        {
            return true;
        }
    }
    false
}

fn output_parent(path: &Path) -> &Path {
    path.parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
}

fn create_output(path: &Path) -> Result<NamedTempFile> {
    NamedTempFile::new_in(output_parent(path))
        .map_err(|error| io_error("create output for", path, error))
}

fn persist(temp: NamedTempFile, path: &Path) -> Result<()> {
    temp.persist(path)
        .map_err(|error| io_error("save output to", path, error.error))?;
    Ok(())
}

pub(super) fn decompile_paths(
    paths: Vec<PathBuf>,
    destination: Destination,
    options: &Options,
    selection: Selection,
    stdout: &mut impl Write,
) -> Result<()> {
    if let Destination::Archive(path) = &destination
        && let Ok(target) = fs::canonicalize(path)
        && paths
            .iter()
            .chain(&selection.libraries)
            .any(|source| fs::canonicalize(source).is_ok_and(|path| path == target))
    {
        return Err(FrontendError::SameArchive(path.clone()));
    }
    let mut inputs = Inputs::new(&destination, selection.skip_extra_files);
    for path in selection.libraries {
        match fs::metadata(&path) {
            Ok(metadata) => inputs.add(path, metadata, false)?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                if options.log_level <= LogLevel::Warn {
                    writeln!(stdout, "warn: missing '{}', ignored", path.display())
                        .map_err(|error| io_error("write", Path::new("<stdout>"), error))?;
                }
            }
            Err(error) => return Err(io_error("read metadata for", &path, error)),
        }
    }
    for path in paths {
        let metadata =
            fs::metadata(&path).map_err(|error| io_error("read metadata for", &path, error))?;
        inputs.add(path, metadata, true)?;
    }
    let classes = std::mem::take(&mut inputs.classes);
    let mut class_bytes = Vec::with_capacity(classes.len());
    for class in &classes {
        let mut bytes = Vec::with_capacity(class.input.size().min(64 * 1024) as usize);
        class
            .input
            .read(&mut inputs.archives, "read class", |file| {
                file.read_to_end(&mut bytes)
            })?;
        class_bytes.push(bytes);
    }
    let group = inputs.prepare_sources(classes, &class_bytes, options, &selection.only)?;
    inputs.retain_directories(&selection.only);
    match destination {
        Destination::Stdout => inputs.write_stdout(stdout, &group, options),
        Destination::Directory(path) | Destination::Legacy(path) => {
            inputs.write_directory(&path, &group, options)
        }
        Destination::Archive(path) => {
            let entries = std::mem::take(&mut inputs.entries);
            inputs.write_archive(entries, &path, &group, options)
        }
    }
}
