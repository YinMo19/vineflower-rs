use std::collections::{BTreeMap, BTreeSet, btree_map::Entry as MapEntry};
use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

use tempfile::NamedTempFile;
use thiserror::Error;
use zip::result::ZipError;
use zip::write::SimpleFileOptions;
use zip::{CompressionMethod, DateTime, ZipArchive, ZipWriter};

use super::{Destination, is_archive};
use crate::{DecompileError, Options, Source, decompile};

const MANIFEST: &str = "META-INF/MANIFEST.MF";

#[derive(Debug, Error)]
pub(super) enum FrontendError {
    #[error("--file and --folder require a destination path other than stdout")]
    MissingDestination,
    #[error("unsupported input '{0}'; expected a .class file, archive, or directory")]
    UnsupportedInput(PathBuf),
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
}

type Result<T, E = FrontendError> = std::result::Result<T, E>;

fn io_error(action: &'static str, path: &Path, source: io::Error) -> FrontendError {
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
    Class(Input),
    Source(Source),
}

impl Entry {
    fn from_input(mut name: String, input: Input) -> (String, Self) {
        if let Some(stem) = name.strip_suffix(".class") {
            name.truncate(stem.len());
            name.push_str(".java");
            (name, Self::Class(input))
        } else {
            (name, Self::Resource(input))
        }
    }

    fn is_directory(&self) -> bool {
        matches!(self, Self::Directory)
    }
}

#[derive(Default)]
struct Inputs {
    entries: BTreeMap<String, Entry>,
    archives: Vec<ArchiveInput>,
    class_bytes: Vec<u8>,
}

impl Inputs {
    fn add(&mut self, path: PathBuf, options: &Options) -> Result<()> {
        let metadata =
            fs::metadata(&path).map_err(|error| io_error("read metadata for", &path, error))?;
        if metadata.is_dir() {
            self.add_directory(&path, &path)
        } else if metadata.is_file() && path.extension().is_some_and(|ext| ext == "class") {
            let input = Input::File {
                path,
                size: metadata.len(),
            };
            let source = self.decompile(&input, options)?;
            // The console saver writes a standalone class at the output root.
            let basename = source.class_name.rsplit('/').next().expect("class name");
            let name = format!("{basename}.java");
            let Input::File { path, .. } = input else {
                unreachable!()
            };
            validate_entry_name(basename, &path)?;
            self.insert(name, Entry::Source(source))
        } else if metadata.is_file() && is_archive(&path) {
            self.add_archive(path)
        } else {
            Err(FrontendError::UnsupportedInput(path))
        }
    }

    fn add_directory(&mut self, root: &Path, path: &Path) -> Result<()> {
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
                self.insert(name, Entry::Directory)?;
                self.add_directory(root, &path)?;
            } else if file_type.is_file() {
                let size = child
                    .metadata()
                    .map_err(|error| io_error("read metadata for", &path, error))?
                    .len();
                let (name, entry) = Entry::from_input(name, Input::File { path, size });
                self.insert(name, entry)?;
            } else {
                return Err(FrontendError::UnsupportedEntry(path.display().to_string()));
            }
        }
        Ok(())
    }

    fn add_archive(&mut self, path: PathBuf) -> Result<()> {
        let file = File::open(&path).map_err(|error| io_error("open", &path, error))?;
        let mut reader = ZipArchive::new(BufReader::new(file))
            .map_err(|error| archive_error("read", path.display().to_string(), error))?;
        let archive = self.archives.len();
        for index in 0..reader.len() {
            let file = reader.by_index_raw(index).map_err(|error| {
                archive_error(
                    "inspect entry from",
                    format!("{} (entry #{index})", path.display()),
                    error,
                )
            })?;
            let name = file.name();
            if file.is_symlink() {
                return Err(FrontendError::UnsupportedEntry(archive_location(
                    &path, name,
                )));
            }
            if file.is_dir() {
                let name = name.strip_suffix('/').unwrap_or(name);
                validate_entry_name(name, &path)?;
                self.insert(name.to_owned(), Entry::Directory)?;
            } else {
                validate_entry_name(name, &path)?;
                let input = Input::Archive {
                    archive,
                    index,
                    size: file.size(),
                };
                let (name, entry) = Entry::from_input(name.to_owned(), input);
                self.insert(name, entry)?;
            }
        }
        self.archives.push(ArchiveInput { path, reader });
        Ok(())
    }

    fn insert(&mut self, name: String, entry: Entry) -> Result<()> {
        match self.entries.entry(name) {
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

    fn decompile(&mut self, input: &Input, options: &Options) -> Result<Source> {
        self.class_bytes.clear();
        input.read(&mut self.archives, "read class", |file| {
            file.read_to_end(&mut self.class_bytes)
        })?;
        decompile(&self.class_bytes, options).map_err(|source| FrontendError::Decompile {
            input: input.identify(&self.archives),
            source,
        })
    }

    fn directories(&self) -> Result<BTreeSet<&str>> {
        let mut directories = BTreeSet::new();
        for (name, entry) in &self.entries {
            if entry.is_directory() {
                directories.insert(name.as_str());
            }
            let mut current = name.as_str();
            while let Some((parent, _)) = current.rsplit_once('/') {
                if !directories.insert(parent) {
                    break;
                }
                if self
                    .entries
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

    fn write_directory(mut self, root: &Path, options: &Options) -> Result<()> {
        let directories = self.directories()?;
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
            let mut temp = create_output(&path)?;
            self.write_contents(&entry, &mut temp, options, &path)?;
            persist(temp, &path)?;
        }
        Ok(())
    }

    fn write_archive(mut self, path: &Path, options: &Options) -> Result<()> {
        self.directories()?;
        let parent = output_parent(path);
        fs::create_dir_all(parent)
            .map_err(|error| io_error("create output directory", parent, error))?;
        let mut temp = create_output(path)?;
        let mut writer = ZipWriter::new(BufWriter::new(temp.as_file_mut()));
        let settings = SimpleFileOptions::default()
            .compression_method(CompressionMethod::Deflated)
            .last_modified_time(DateTime::default());
        let mut entries = std::mem::take(&mut self.entries);
        // JarInputStream only recognizes a manifest at the start of an archive.
        let manifest = entries.remove_entry(MANIFEST);
        for (name, entry) in manifest.into_iter().chain(entries) {
            if entry.is_directory() {
                continue;
            }
            let large =
                matches!(&entry, Entry::Resource(input) if input.size() >= u64::from(u32::MAX));
            writer
                .start_file(&name, settings.large_file(large))
                .map_err(|error| {
                    archive_error("create entry in", archive_location(path, &name), error)
                })?;
            self.write_contents(&entry, &mut writer, options, path)?;
        }
        writer
            .finish()
            .map_err(|error| archive_error("finish", path.display().to_string(), error))?
            .flush()
            .map_err(|error| io_error("flush archive", path, error))?;
        persist(temp, path)
    }

    fn write_stdout(mut self, stdout: &mut impl Write, options: &Options) -> Result<()> {
        self.directories()?;
        let path = Path::new("<stdout>");
        for (name, entry) in std::mem::take(&mut self.entries) {
            if !matches!(entry, Entry::Class(_) | Entry::Source(_)) {
                continue;
            }
            writeln!(stdout, "==== {name} ====").map_err(|error| io_error("write", path, error))?;
            self.write_contents(&entry, stdout, options, path)?;
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
        options: &Options,
        path: &Path,
    ) -> Result<()> {
        let source;
        let content = match entry {
            Entry::Source(source) => &source.text,
            Entry::Class(input) => {
                source = self.decompile(input, options)?;
                &source.text
            }
            Entry::Resource(input) => {
                return input
                    .read(&mut self.archives, "copy resource", |file| {
                        io::copy(file, out)
                    })
                    .map(|_| ());
            }
            Entry::Directory => unreachable!("only files have contents"),
        };
        out.write_all(content.as_bytes())
            .map_err(|error| io_error("write", path, error))
    }
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
    stdout: &mut impl Write,
) -> Result<()> {
    if let Destination::Archive(path) = &destination
        && let Ok(target) = fs::canonicalize(path)
        && paths
            .iter()
            .any(|source| fs::canonicalize(source).is_ok_and(|path| path == target))
    {
        return Err(FrontendError::SameArchive(path.clone()));
    }
    let mut inputs = Inputs::default();
    for path in paths {
        inputs.add(path, options)?;
    }
    match destination {
        Destination::Stdout => inputs.write_stdout(stdout, options),
        Destination::Directory(path) => inputs.write_directory(&path, options),
        Destination::Archive(path) => inputs.write_archive(&path, options),
    }
}
