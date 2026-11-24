use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::panic::catch_unwind;
use std::path::Path;
use std::sync::Arc;

use jimage_rs::{JImage, error::JImageError};

use super::{ClassPathError, valid_name};

pub(super) struct Image {
    image: JImage,
    // Most resources share one of a few dozen module names.
    modules: HashMap<Box<str>, Arc<str>>,
}

impl Image {
    pub(super) fn open(path: &Path) -> Result<Self, ClassPathError> {
        let image = JImage::open(path).map_err(|source| match source {
            JImageError::Io { source, .. } => ClassPathError::io(path, source),
            source => ClassPathError::Image { path: path.into(), source },
        })?;
        // jimage-rs's layout reader uses unchecked slice indexing in a few places.
        // Turn a malformed image offset into a lookup error rather than unwinding
        // through the classpath API. No resource bodies are read by the iterator.
        let modules = catch_unwind(|| module_index(&image))
            .map_err(|_| ClassPathError::InvalidImage { path: path.into() })?
            .map_err(|source| ClassPathError::Image { path: path.into(), source })?;
        Ok(Self { image, modules })
    }

    pub(super) fn load(
        &self,
        path: &Path,
        name: &str,
        resource: &str,
    ) -> Result<Option<Cow<'_, [u8]>>, ClassPathError> {
        let Some(module) = self.modules.get(name) else {
            return Ok(None);
        };
        let mut full_name = String::with_capacity(module.len() + resource.len() + 2);
        full_name.push('/');
        full_name.push_str(module);
        full_name.push('/');
        full_name.push_str(resource);
        let data = catch_unwind(|| self.image.find_resource(&full_name))
            .map_err(|_| ClassPathError::InvalidImage { path: path.into() })?
            .map_err(|source| match source {
                JImageError::UnsupportedDecompressor { decompressor_name } => {
                    unsupported(path, name, decompressor_name)
                }
                source => ClassPathError::Image { path: path.into(), source },
            })?;
        match data {
            // A name in the location table must also be in the hash table.
            None => Err(ClassPathError::InvalidImage { path: path.into() }),
            Some(Cow::Owned(bytes))
                if matches!(
                    bytes.get(..4),
                    Some([0xCA, 0xFE, 0xFA, 0xFA] | [0xFA, 0xFA, 0xFE, 0xCA])
                ) =>
            {
                Err(unsupported(path, name, "chained jimage compression".into()))
            }
            Some(data) => Ok(Some(data)),
        }
    }
}

fn module_index(image: &JImage) -> Result<HashMap<Box<str>, Arc<str>>, JImageError> {
    let mut classes = HashMap::<Box<str>, Arc<str>>::new();
    let mut modules = HashSet::<Arc<str>>::new();
    for resource in image.resource_names_iter() {
        let resource = resource?;
        if resource.extension != "class"
            || resource.base.contains('/')
            || resource.parent.starts_with("META-INF/preview/")
        {
            continue;
        }
        let mut name = String::with_capacity(
            resource.parent.len() + resource.base.len() + usize::from(!resource.parent.is_empty()),
        );
        if !resource.parent.is_empty() {
            name.push_str(&resource.parent);
            name.push('/');
        }
        name.push_str(&resource.base);
        if !valid_name(&name) {
            continue;
        }
        let module = if let Some(module) = modules.get(resource.module.as_ref()) {
            module.clone()
        } else {
            let module: Arc<str> = Arc::from(resource.module.as_ref());
            modules.insert(module.clone());
            module
        };
        // An unqualified internal name can appear in more than one module
        // (notably module-info). Prefer java.base, then lexical module order.
        match classes.entry(name.into_boxed_str()) {
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                let old: &str = entry.get();
                if old != "java.base" && (module.as_ref() == "java.base" || module.as_ref() < old) {
                    entry.insert(module);
                }
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(module);
            }
        }
    }
    Ok(classes)
}

fn unsupported(path: &Path, name: &str, algorithm: String) -> ClassPathError {
    ClassPathError::UnsupportedImageCompression { path: path.into(), name: name.into(), algorithm }
}
