use std::borrow::Cow;
use std::fs::{self, File};
use std::io::{self, BufReader, Read};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use zip::{ZipArchive, result::ZipError};

use super::{ClassDataProvider, ClassPathError, image::Image, optional_stat};

pub(super) const JMOD_PREFIX: &str = "classes/";
const JMOD_MAGIC: [u8; 4] = [b'J', b'M', 1, 0];

pub(super) enum Source {
    File(FileSource),
    Provider(Box<dyn ClassDataProvider>),
}

impl Source {
    pub(super) fn location(&self) -> String {
        match self {
            Self::File(file) => format!("{:?}", file.path),
            Self::Provider(_) => "a class data provider".into(),
        }
    }
}

pub(super) enum Content<'a> {
    File(Cow<'a, [u8]>),
    Shared(Arc<[u8]>),
}

impl Content<'_> {
    pub(super) fn as_ref(&self) -> &[u8] {
        match self {
            Self::File(bytes) => bytes,
            Self::Shared(bytes) => bytes,
        }
    }

    pub(super) fn into_shared(self) -> Arc<[u8]> {
        match self {
            Self::File(bytes) => Arc::from(bytes.as_ref()),
            Self::Shared(bytes) => bytes,
        }
    }
}

pub(super) struct FileSource {
    path: PathBuf,
    reader: Reader,
}

enum Reader {
    Image(Image),
    Archive {
        archive: Mutex<ZipArchive<BufReader<File>>>,
        jmod: bool,
    },
    Directory,
}

impl FileSource {
    pub(super) fn open(path: &Path) -> Result<Self, ClassPathError> {
        let stat = fs::metadata(path).map_err(|e| ClassPathError::io(path, e))?;
        if stat.is_dir() {
            let path = fs::canonicalize(path).map_err(|e| ClassPathError::io(path, e))?;
            return Ok(Self {
                path,
                reader: Reader::Directory,
            });
        }
        if !stat.is_file() {
            return Err(ClassPathError::InvalidSource { path: path.into() });
        }
        let file = File::open(path).map_err(|e| ClassPathError::io(path, e))?;
        let mut reader = BufReader::new(file);
        let jmod = path
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("jmod"));
        if jmod {
            let mut magic = [0; 4];
            match reader.read_exact(&mut magic) {
                Ok(()) if magic == JMOD_MAGIC => {}
                Ok(()) => return Err(ClassPathError::InvalidJmod { path: path.into() }),
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => {
                    return Err(ClassPathError::InvalidJmod { path: path.into() });
                }
                Err(e) => return Err(ClassPathError::io(path, e)),
            }
        }
        let archive = ZipArchive::new(reader).map_err(|source| ClassPathError::Archive {
            path: path.into(),
            source,
        })?;
        Ok(Self {
            path: path.into(),
            reader: Reader::Archive {
                archive: Mutex::new(archive),
                jmod,
            },
        })
    }

    pub(super) fn image(path: PathBuf) -> Result<Self, ClassPathError> {
        let reader = Reader::Image(Image::open(&path)?);
        Ok(Self { path, reader })
    }

    pub(super) fn load(
        &self,
        name: &str,
        jmod_resource: &str,
    ) -> Result<Option<Cow<'_, [u8]>>, ClassPathError> {
        let resource = &jmod_resource[JMOD_PREFIX.len()..];
        match &self.reader {
            Reader::Image(image) => image.load(&self.path, name, resource),
            Reader::Directory => self
                .load_directory(resource)
                .map(|bytes| bytes.map(Cow::Owned)),
            Reader::Archive { archive, jmod } => {
                if name.starts_with("META-INF/versions/") {
                    return Ok(None);
                }
                let mut archive = archive.lock().unwrap_or_else(PoisonError::into_inner);
                let archive_name = if *jmod { jmod_resource } else { resource };
                let mut entry = match archive.by_name(archive_name) {
                    Ok(entry) => entry,
                    Err(ZipError::FileNotFound) => return Ok(None),
                    Err(source) => {
                        return Err(ClassPathError::Archive {
                            path: self.path.clone(),
                            source,
                        });
                    }
                };
                if !entry.is_file()
                    || entry.is_symlink()
                    || entry.name_raw() != archive_name.as_bytes()
                {
                    return Ok(None);
                }
                let mut bytes = Vec::new();
                entry
                    .read_to_end(&mut bytes)
                    .map_err(|e| ClassPathError::io(&self.path, e))?;
                Ok(Some(Cow::Owned(bytes)))
            }
        }
    }

    fn load_directory(&self, resource: &str) -> Result<Option<Vec<u8>>, ClassPathError> {
        let path = self.path.join(resource);
        let resolved = match fs::canonicalize(&path) {
            Ok(resolved) => resolved,
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                ) =>
            {
                return Ok(None);
            }
            Err(e) => return Err(ClassPathError::io(&path, e)),
        };
        if !resolved.starts_with(&self.path) {
            return Err(ClassPathError::OutsideDirectory {
                path,
                root: self.path.clone(),
            });
        }
        if !optional_stat(&resolved)?.is_some_and(|stat| stat.is_file()) {
            return Ok(None);
        }
        fs::read(&resolved)
            .map(Some)
            .map_err(|e| ClassPathError::io(&path, e))
    }
}
