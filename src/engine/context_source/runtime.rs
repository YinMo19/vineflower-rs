//! Java 9+ runtime libraries from the modular `lib/modules` image.

use std::cmp::Ordering;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use jimage_rs::{JImage, error::JImageError};
use rustc_hash::{FxHashMap, FxHashSet};

use super::{CLASS_SUFFIX, ContextSource, Entries, Entry};
use crate::code::bytecode_version::BytecodeVersion;
mod boot_modules;
use crate::engine::Options;
use crate::structs::StructClass;
use crate::util::data_input::DataInputFullStream;

const MODULE_INFO: &str = "module-info.class";
const MAJOR_26: i32 = 70;

/// `JrtFinder.JavaRuntimeContextSource`. Resources are exposed by module.
pub struct RuntimeImage {
    home: PathBuf,
    modules: Vec<Arc<RuntimeModule>>,
}

impl RuntimeImage {
    /// Open a modular image at `java_home/lib/modules` using the native JImage reader.
    /// Resources may use ZIP compression or a shared constant pool.
    pub fn open(java_home: &Path) -> io::Result<Self> {
        let home = if java_home.is_absolute() {
            java_home.to_owned()
        } else {
            std::env::current_dir()?.join(java_home)
        };
        let image = Arc::new(JImage::open(home.join("lib/modules")).map_err(image_error)?);
        let mut paths_by_module = FxHashMap::<String, Vec<String>>::default();
        for resource in image.resource_names_iter() {
            let (module, path) = resource.map_err(image_error)?.get_full_name();
            paths_by_module.entry(module).or_default().push(path);
        }

        let mut paths_by_module: Vec<_> = paths_by_module.into_iter().collect();
        paths_by_module.sort_unstable_by(|(left, _), (right, _)| {
            left.encode_utf16().cmp(right.encode_utf16())
        });
        let options = Options::default();
        let mut base = module_name(&image, "java.base", &options)?;
        let runtime_major = base.as_ref().map(|&(_, major)| major);
        let mut modules = Vec::with_capacity(paths_by_module.len());
        for (module, paths) in paths_by_module {
            let descriptor = if module == "java.base" {
                base.take()
            } else {
                module_name(&image, &module, &options)?
            };
            if let Some((name, major)) = descriptor {
                modules.push(Arc::new(RuntimeModule {
                    image: Arc::clone(&image),
                    module,
                    name,
                    entries: module_entries(paths, runtime_major.unwrap_or(major)),
                }));
            }
        }

        Ok(Self { home, modules })
    }

    pub(crate) fn bootstrap_sources(&self) -> impl Iterator<Item = Arc<dyn ContextSource>> + '_ {
        let modules = self
            .modules
            .iter()
            .find(|module| module.module == "java.base")
            .and_then(|base| boot_modules::read(base));
        self.modules
            .iter()
            .filter(move |module| {
                module.module == "java.base"
                    || modules
                        .as_ref()
                        .is_some_and(|names| names.contains(&module.module))
            })
            .map(|module| Arc::clone(module) as Arc<dyn ContextSource>)
    }
}

impl ContextSource for RuntimeImage {
    fn get_name(&self) -> String {
        format!("Java runtime {}", self.home.display())
    }

    fn get_entries(&self) -> Entries {
        Entries {
            child_contexts: self
                .modules
                .iter()
                .map(|module| Arc::clone(module) as Arc<dyn ContextSource>)
                .collect(),
            ..Entries::default()
        }
    }

    fn get_input_stream(&self, _resource: &str) -> io::Result<Option<Vec<u8>>> {
        Ok(None)
    }
}

struct RuntimeModule {
    image: Arc<JImage>,
    module: String,
    name: String,
    entries: Entries,
}

impl ContextSource for RuntimeModule {
    fn get_name(&self) -> String {
        format!("module {}", self.name)
    }

    fn get_entries(&self) -> Entries {
        self.entries.clone()
    }

    fn get_input_stream(&self, resource: &str) -> io::Result<Option<Vec<u8>>> {
        self.image
            .find_resource(&format!("/{}/{resource}", self.module))
            .map(|bytes| bytes.map(|bytes| bytes.into_owned()))
            .map_err(image_error)
    }
}

fn module_name(
    image: &JImage,
    module: &str,
    options: &Options,
) -> io::Result<Option<(String, i32)>> {
    let bytes = match image.find_resource(&format!("/{module}/{MODULE_INFO}")) {
        Ok(Some(bytes)) => bytes,
        Err(error @ JImageError::UnsupportedDecompressor { .. }) => return Err(image_error(error)),
        // JrtFinder.getEntries skips a module whose descriptor cannot be read.
        Ok(None) | Err(_) => return Ok(None),
    };
    let Ok(class) =
        StructClass::create(&mut DataInputFullStream::new(&bytes), false, options, None)
    else {
        return Ok(None);
    };
    let Some(descriptor) = class.attributes.module else {
        return Ok(None);
    };
    let name = match descriptor.module_version {
        Some(version) => format!("{}@{version}", descriptor.module_name),
        None => descriptor.module_name.to_string(),
    };
    Ok(Some((name, class.version.major)))
}

fn module_entries(mut paths: Vec<String>, major: i32) -> Entries {
    // JRT walks the module tree in depth-first order, with siblings sorted
    // as Java strings. The image index itself is in hash-table order.
    paths.sort_unstable_by(|left, right| compare_paths(left, right));
    let mut entries = Entries::default();
    let mut seen_directories = FxHashSet::default();
    add_entry(&mut entries, "");
    // Opening the descriptor before the walk inserted it as the first
    // child until the JRT directory refactor in JDK 26 (JDK-8360037).
    // JDK 19 fixed its duplicate appearance in tree order (JDK-8247407).
    let prepend_descriptor = major < MAJOR_26;
    if prepend_descriptor {
        add_entry(&mut entries, MODULE_INFO);
    }
    for path in &paths {
        if path == MODULE_INFO && prepend_descriptor && major >= BytecodeVersion::MAJOR_19 {
            continue;
        }
        for (index, _) in path.match_indices('/') {
            let directory = &path[..index];
            if seen_directories.insert(directory) {
                // Files.walk(...).relativize(...).toString() has no trailing slash.
                add_entry(&mut entries, directory);
            }
        }
        add_entry(&mut entries, path);
    }
    entries
}

fn compare_paths(left: &str, right: &str) -> Ordering {
    left.split('/')
        .zip(right.split('/'))
        .map(|(left, right)| left.encode_utf16().cmp(right.encode_utf16()))
        .find(|order| *order != Ordering::Equal)
        .unwrap_or_else(|| left.len().cmp(&right.len()))
}

fn add_entry(entries: &mut Entries, path: &str) {
    if let Some(directory) = path.strip_suffix('/') {
        entries.directories.push(directory.to_owned());
    } else if let Some(class) = path.strip_suffix(CLASS_SUFFIX) {
        entries.classes.push(Entry::at_base(class));
    } else {
        entries.others.push(Entry::at_base(path));
    }
}

fn image_error(error: JImageError) -> io::Error {
    let kind = match &error {
        JImageError::Io { source, .. } => source.kind(),
        JImageError::UnsupportedDecompressor { .. } => io::ErrorKind::Unsupported,
        _ => io::ErrorKind::InvalidData,
    };
    io::Error::new(kind, error)
}
