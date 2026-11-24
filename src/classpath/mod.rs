//! Lazy lookup of library classes from selected filesystem paths and providers.
//!
//! Sources are searched in insertion order and should not be changed while the
//! classpath is in use. In particular, the JDK image reader memory-maps `lib/modules`.

mod image;
mod metadata;
mod source;

pub use metadata::{ClassMetadata, MemberMetadata};

use std::collections::HashMap;
use std::fmt;
use std::fs::{self, Metadata};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use crate::classfile::ClassError;
use source::{Content, FileSource, JMOD_PREFIX, Source};

/// On-demand byte source. Returned names and bytes should be stable for the
/// lifetime of the classpath, and lookup need not support enumeration.
pub trait ClassDataProvider: fmt::Debug + Send + Sync {
    fn load(&self, internal_name: &str) -> io::Result<Option<Arc<[u8]>>>;
}

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ClassPathError {
    #[error("no Java runtime image, rt.jar, or JMODs found in {path:?}")]
    RuntimeNotFound { path: PathBuf },
    #[error("invalid JVM internal class name {name:?}")]
    InvalidName { name: String },
    #[error("expected a regular archive or a class directory at {path:?}")]
    InvalidSource { path: PathBuf },
    #[error("invalid or unsupported JMOD header at {path:?}")]
    InvalidJmod { path: PathBuf },
    #[error("I/O error at {path:?}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    #[error("could not read ZIP archive {path:?}: {source}")]
    Archive {
        path: PathBuf,
        #[source]
        source: zip::result::ZipError,
    },
    #[error("could not read runtime image {path:?}: {source}")]
    Image {
        path: PathBuf,
        #[source]
        source: jimage_rs::error::JImageError,
    },
    #[error("invalid runtime image {path:?}")]
    InvalidImage { path: PathBuf },
    #[error("runtime image {path:?} uses unsupported compression {algorithm:?} for {name}")]
    UnsupportedImageCompression {
        path: PathBuf,
        name: String,
        algorithm: String,
    },
    #[error("class data provider could not read {name}: {source}")]
    Provider {
        name: String,
        #[source]
        source: io::Error,
    },
    #[error("class entry {path:?} resolves outside its classpath root {root:?}")]
    OutsideDirectory { path: PathBuf, root: PathBuf },
    #[error("invalid class {name} from {location}: {source}")]
    InvalidClass {
        location: String,
        name: String,
        #[source]
        source: ClassError,
    },
    #[error("class {requested} from {location} declares a different class name, {declared}")]
    WrongClassName {
        location: String,
        requested: String,
        declared: String,
    },
}

impl ClassPathError {
    fn io(path: &Path, source: io::Error) -> Self {
        Self::Io {
            path: path.into(),
            source,
        }
    }
}

/// An ordered classpath for reading class files without class loading or a JVM.
#[derive(Default)]
pub struct ClassPath {
    sources: Vec<Source>,
    metadata: Mutex<HashMap<String, Arc<ClassMetadata>>>,
}

impl fmt::Debug for ClassPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClassPath")
            .field("source_count", &self.sources.len())
            .finish_non_exhaustive()
    }
}

impl ClassPath {
    pub fn new() -> Self {
        Self::default()
    }

    /// Select a runtime from a caller-provided Java home. Modular runtime images
    /// take precedence over standalone JMODs; for Java 8, `rt.jar` takes
    /// precedence over its sibling JARs. No Java programs are run.
    pub fn for_java_home(home: impl AsRef<Path>) -> Result<Self, ClassPathError> {
        let home = home.as_ref();
        let mut classpath = Self::new();
        let modules = home.join("lib/modules");
        if let Some(stat) = optional_stat(&modules)? {
            if !stat.is_file() {
                return Err(ClassPathError::InvalidImage { path: modules });
            }
            classpath
                .sources
                .push(Source::File(FileSource::image(modules)?));
            return Ok(classpath);
        }

        let lib_dirs = [home.join("jre/lib"), home.join("lib")];
        for lib in &lib_dirs {
            let rt = lib.join("rt.jar");
            if let Some(stat) = optional_stat(&rt)? {
                if !stat.is_file() {
                    return Err(ClassPathError::InvalidSource { path: rt });
                }
                classpath.add(rt)?;
                for lib in &lib_dirs {
                    for jar in archives_in(lib, "jar")? {
                        if !jar.file_name().is_some_and(|name| name == "rt.jar") {
                            classpath.add(jar)?;
                        }
                    }
                }
                return Ok(classpath);
            }
        }

        for jmod in archives_in(&home.join("jmods"), "jmod")? {
            classpath.add(jmod)?;
        }
        if classpath.sources.is_empty() {
            return Err(ClassPathError::RuntimeNotFound { path: home.into() });
        }
        Ok(classpath)
    }

    /// Append a class directory, JAR/ZIP, or JMOD. Archives use their base class
    /// entries; this API does not select multi-release JAR versions. The first
    /// source with the requested name wins, including when it cannot be read.
    pub fn add(&mut self, path: impl AsRef<Path>) -> Result<(), ClassPathError> {
        self.sources
            .push(Source::File(FileSource::open(path.as_ref())?));
        Ok(())
    }

    /// Append an on-demand source without enumerating it.
    pub fn add_provider(&mut self, provider: impl ClassDataProvider + 'static) {
        self.sources.push(Source::Provider(Box::new(provider)));
    }

    /// Load the class file with this exact JVM internal name (e.g. `java/lang/String`).
    /// An absent class is `Ok(None)`; an unreadable or invalid entry is an error.
    /// Class bytes are not retained by the classpath.
    pub fn load(&self, name: &str) -> Result<Option<Arc<[u8]>>, ClassPathError> {
        validate_lookup_name(name)?;
        let Some((source, bytes)) = self.find(name)? else {
            return Ok(None);
        };
        if self.cached_metadata(name).is_none() {
            self.cache_metadata(name, source, bytes.as_ref())?;
        }
        Ok(Some(bytes.into_shared()))
    }

    /// Read and cache owned class metadata on first use, without decoding method code.
    pub fn metadata(&self, name: &str) -> Result<Option<Arc<ClassMetadata>>, ClassPathError> {
        validate_lookup_name(name)?;
        if let Some(metadata) = self.cached_metadata(name) {
            return Ok(Some(metadata));
        }
        let Some((source, bytes)) = self.find(name)? else {
            return Ok(None);
        };
        self.cache_metadata(name, source, bytes.as_ref()).map(Some)
    }

    fn find(&self, name: &str) -> Result<Option<(&Source, Content<'_>)>, ClassPathError> {
        let mut resource = None;
        for source in &self.sources {
            let bytes = match source {
                Source::File(file) => {
                    let resource = resource.get_or_insert_with(|| {
                        let mut resource =
                            String::with_capacity(JMOD_PREFIX.len() + name.len() + ".class".len());
                        resource.push_str(JMOD_PREFIX);
                        resource.push_str(name);
                        resource.push_str(".class");
                        resource
                    });
                    file.load(name, resource)?.map(Content::File)
                }
                Source::Provider(provider) => provider
                    .load(name)
                    .map_err(|source| ClassPathError::Provider {
                        name: name.into(),
                        source,
                    })?
                    .map(Content::Shared),
            };
            if let Some(bytes) = bytes {
                return Ok(Some((source, bytes)));
            }
        }
        Ok(None)
    }

    fn cached_metadata(&self, name: &str) -> Option<Arc<ClassMetadata>> {
        self.metadata
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(name)
            .cloned()
    }

    fn cache_metadata(
        &self,
        name: &str,
        source: &Source,
        bytes: &[u8],
    ) -> Result<Arc<ClassMetadata>, ClassPathError> {
        let metadata = Arc::new(ClassMetadata::read(name, source, bytes)?);
        let mut cache = self.metadata.lock().unwrap_or_else(PoisonError::into_inner);
        Ok(cache.entry(name.into()).or_insert(metadata).clone())
    }
}

fn valid_name(name: &str) -> bool {
    !name.contains(['.', ';', '[', '\\', ':', '\0']) && name.split('/').all(|part| !part.is_empty())
}

fn validate_lookup_name(name: &str) -> Result<(), ClassPathError> {
    if valid_name(name) {
        Ok(())
    } else {
        Err(ClassPathError::InvalidName { name: name.into() })
    }
}

fn optional_stat(path: &Path) -> Result<Option<Metadata>, ClassPathError> {
    match fs::metadata(path) {
        Ok(metadata) => Ok(Some(metadata)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(ClassPathError::io(path, e)),
    }
}

fn archives_in(directory: &Path, extension: &str) -> Result<Vec<PathBuf>, ClassPathError> {
    let entries = match fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(ClassPathError::io(directory, e)),
    };
    let mut archives = Vec::new();
    for entry in entries {
        let path = entry.map_err(|e| ClassPathError::io(directory, e))?.path();
        if path
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case(extension))
            && optional_stat(&path)?.is_some_and(|stat| stat.is_file())
        {
            archives.push(path);
        }
    }
    archives.sort_unstable();
    Ok(archives)
}
