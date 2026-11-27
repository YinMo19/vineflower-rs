//! Standard output sinks for folder, archive and console output.

use std::{
    fs, io,
    io::Write,
    path::{Component, Path, PathBuf},
};

use flate2::{Compression, write::DeflateEncoder};
use rawzip::{CompressionMethod, Header, ZipArchiveWriter, extra_fields::ExtraFieldId};
use rustc_hash::FxHashSet;
use tempfile::{Builder, NamedTempFile};

use super::{DecompiledClass, manifest, whitelisted};
use crate::engine::context_source::OutputLayout;
use crate::structs::context_unit::ContextUnit;
use crate::util::jhash::JHashSet;

const MANIFEST: &str = "META-INF/MANIFEST.MF";

#[derive(Clone, Debug)]
pub enum Output {
    /// Print class source with its entry name. Non-class files are omitted.
    Stdout,
    /// Unpack outputs into this directory.
    Folder(PathBuf),
    /// Write a ZIP file, recreated for each archive or directory input unit.
    File(PathBuf),
    /// Keep archive inputs archived under their original file names.
    Legacy(PathBuf),
}

pub(super) enum UnitSink {
    Stdout,
    Folder { root: PathBuf, legacy: bool },
    Archive(Box<ArchiveSink>),
    MissingArchive,
}

impl UnitSink {
    pub(super) fn begin(
        output: &Output,
        unit: &ContextUnit,
        layout: &OutputLayout,
        whitelist: &[String],
    ) -> io::Result<Self> {
        let archive_source = matches!(layout, OutputLayout::Archive { .. });
        let mut sink = match output {
            Output::Stdout => Self::Stdout,
            Output::Folder(root) => {
                if let OutputLayout::Archive { directory, .. } = layout {
                    fs::create_dir_all(output_path(root, directory)?)?;
                }
                Self::Folder {
                    root: root.clone(),
                    legacy: false,
                }
            }
            Output::File(_) if matches!(layout, OutputLayout::SingleFile) => Self::MissingArchive,
            Output::File(path) => {
                Self::Archive(Box::new(ArchiveSink::begin(path, false, archive_source)?))
            }
            Output::Legacy(root) => match layout {
                OutputLayout::Archive { name, directory } => {
                    let parent = output_path(root, directory)?;
                    fs::create_dir_all(&parent)?;
                    let path = output_path(&parent, name)?;
                    Self::Archive(Box::new(ArchiveSink::begin(&path, true, true)?))
                }
                _ => Self::Folder {
                    root: root.clone(),
                    legacy: true,
                },
            },
        };
        if matches!(sink, Self::Stdout) {
            return Ok(sink);
        }

        if let Self::Archive(archive) = &mut sink
            && archive_source
        {
            let manifest = unit
                .source
                .get_input_stream(MANIFEST)
                .and_then(|bytes| bytes.as_deref().map(manifest::rewrite).transpose());
            match manifest {
                Ok(Some(manifest)) => archive.manifest(&manifest)?,
                Ok(None) => {}
                Err(error) => {
                    log::error!("Failed to read manifest from {}: {error}", unit.get_name())
                }
            }
        }

        let mut resources = JHashSet::new();
        resources.extend(unit.other_entries.iter().map(|entry| entry.path()));
        for directory in &unit.dir_entries {
            if whitelisted(whitelist, directory)
                || resources
                    .iter()
                    .any(|resource| resource.starts_with(directory))
            {
                sink.directory(directory)?;
            }
        }
        for name in resources.iter() {
            if name == MANIFEST
                && let Self::Archive(archive) = &sink
                && archive.entries.contains(name)
            {
                continue;
            }
            match unit.source.get_input_stream(name) {
                Ok(Some(content)) => {
                    if matches!(sink, Self::MissingArchive) {
                        return Err(missing_archive());
                    }
                    if let Err(error) = sink.file(name, &content, None) {
                        log::error!("Cannot copy entry {name} from {}: {error}", unit.get_name());
                    }
                }
                Ok(None) => {}
                Err(error) => {
                    log::error!("Cannot read entry {name} from {}: {error}", unit.get_name());
                }
            }
        }
        Ok(sink)
    }

    fn directory(&mut self, name: &str) -> io::Result<()> {
        match self {
            Self::Folder { root, .. } => fs::create_dir_all(output_path(root, name)?),
            Self::Archive(archive) if archive.keep_directories && !name.is_empty() => {
                archive.directory(name)
            }
            _ => Ok(()),
        }
    }

    pub(super) fn class(
        &mut self,
        class: &DecompiledClass,
        dump_code_lines: bool,
    ) -> io::Result<()> {
        if matches!(self, Self::Stdout) {
            let mut stdout = io::stdout().lock();
            writeln!(stdout, "==== {} ====", class.entry_name)?;
            writeln!(stdout, "{}", class.source)?;
        } else {
            let mapping = dump_code_lines
                .then_some(class.mapping.as_deref())
                .flatten();
            let saved = self.file(&class.entry_name, class.source.as_bytes(), mapping);
            if matches!(self, Self::Folder { legacy: true, .. }) {
                if let Err(error) = saved {
                    log::error!("Cannot write class file {}: {error}", class.entry_name);
                }
            } else {
                saved?;
            }
        }
        Ok(())
    }

    fn file(&mut self, name: &str, bytes: &[u8], mapping: Option<&[i32]>) -> io::Result<()> {
        match self {
            Self::Folder { root, .. } => fs::write(output_path(root, name)?, bytes),
            Self::Archive(archive) => archive.file(name, bytes, mapping, false),
            Self::MissingArchive => Err(missing_archive()),
            Self::Stdout => Ok(()),
        }
    }

    pub(super) fn finish(self) -> io::Result<()> {
        if let Self::Archive(archive) = self {
            archive.finish()?;
        }
        Ok(())
    }
}

pub(super) struct ArchiveSink {
    writer: ZipArchiveWriter<NamedTempFile>,
    path: PathBuf,
    entries: FxHashSet<String>,
    keep_directories: bool,
    class_zip_extras: bool,
}

impl ArchiveSink {
    fn begin(path: &Path, keep_directories: bool, class_zip_extras: bool) -> io::Result<Self> {
        if path.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::IsADirectory,
                format!(
                    "Trying to save {} as a file but there's a directory there already",
                    path.display()
                ),
            ));
        }
        let base = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let temp = Builder::new().prefix(".vineflower-").tempfile_in(base)?;
        Ok(Self {
            writer: ZipArchiveWriter::new(temp),
            path: path.to_owned(),
            entries: FxHashSet::default(),
            keep_directories,
            class_zip_extras,
        })
    }

    fn directory(&mut self, name: &str) -> io::Result<()> {
        let name = format!("{}/", name.trim_end_matches('/'));
        checked_relative(&name)?;
        if self.add_entry(&name) {
            self.writer
                .new_dir(name.as_str())
                .create()
                .map_err(zip_error)?;
        }
        Ok(())
    }

    fn manifest(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.file(MANIFEST, bytes, None, true)
    }

    fn file(
        &mut self,
        name: &str,
        bytes: &[u8],
        mapping: Option<&[i32]>,
        jar_magic: bool,
    ) -> io::Result<()> {
        checked_relative(name)?;
        if !self.add_entry(name) {
            return Ok(());
        }
        let mut builder = self
            .writer
            .new_file(name)
            .compression_method(CompressionMethod::DEFLATE);
        if jar_magic {
            builder = builder
                .extra_field(ExtraFieldId::JAVA_JAR, &[], Header::default())
                .map_err(zip_error)?;
        }
        if self.class_zip_extras
            && let Some(lines) = mapping.filter(|lines| !lines.is_empty())
        {
            // IResultSaver.getCodeLineData: ForgeFlower's extra-field format.
            let mut payload = vec![1];
            for &line in lines {
                payload.extend_from_slice(&(line as u16).to_le_bytes());
            }
            let id = ExtraFieldId::new(0x4646);
            builder = builder
                .extra_field(id, &payload, Header::default())
                .map_err(zip_error)?;
        }
        let (mut entry, configuration) = builder.start().map_err(zip_error)?;
        let compressor = DeflateEncoder::new(&mut entry, Compression::default());
        let mut data = configuration.wrap(compressor);
        data.write_all(bytes)?;
        let (compressor, descriptor) = data.finish().map_err(zip_error)?;
        compressor.finish()?;
        entry.finish(descriptor).map_err(zip_error)?;
        Ok(())
    }

    fn add_entry(&mut self, name: &str) -> bool {
        if !self.entries.insert(name.to_owned()) {
            log::warn!("Zip entry {name} already exists in {}", self.path.display());
            return false;
        }
        true
    }

    fn finish(self) -> io::Result<()> {
        let temp = self.writer.finish().map_err(zip_error)?;
        temp.persist(self.path).map_err(|error| error.error)?;
        Ok(())
    }
}

fn missing_archive() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "A standalone file cannot initialize archive output; supply its containing directory",
    )
}

fn checked_relative(name: &str) -> io::Result<&Path> {
    let path = Path::new(name);
    if path
        .components()
        .any(|component| !matches!(component, Component::Normal(_) | Component::CurDir))
        || name.contains('\0')
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Invalid output entry {name:?}"),
        ));
    }
    Ok(path)
}

/// A resource may declare arbitrary paths. Keep it under the selected output
/// directory, including when an existing child is a symlink.
fn output_path(root: &Path, relative: &str) -> io::Result<PathBuf> {
    let mut path = root.to_owned();
    for component in checked_relative(relative)?.components() {
        path.push(component.as_os_str());
        match fs::symlink_metadata(&path) {
            Ok(file) if file.is_symlink() => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Output path crosses a symbolic link: {}", path.display()),
                ));
            }
            Err(error) if error.kind() != io::ErrorKind::NotFound => return Err(error),
            _ => {}
        }
    }
    Ok(path)
}

fn zip_error(error: rawzip::Error) -> io::Error {
    let kind = match error.kind() {
        rawzip::ErrorKind::IO(cause) => cause.kind(),
        _ => io::ErrorKind::InvalidData,
    };
    io::Error::new(kind, error)
}
