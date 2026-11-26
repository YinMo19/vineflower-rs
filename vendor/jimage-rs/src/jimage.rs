use crate::bytes_utils::read_integer;
use crate::decompression;
use crate::error::{internal, IoSnafu, JImageError, Result};
use crate::header::Header;
use crate::raw_jimage::RawJImage;
use crate::resource_name::{ResourceName, ResourceNamesIter};
use crate::strings::{hash, StringTable, HASH_SEED};
use memmap2::Mmap;
use snafu::ResultExt;
use std::borrow::Cow;
use std::fs::File;
use std::path::Path;
/* JImage File Structure

    /------------------------------\
    |          Header              | (Fixed size: 28 bytes)
    |------------------------------|
    |       Index Tables:          |
    |  - Redirect Table            | (table_length * 4 bytes)
    |  - Offsets Table             | (table_length * 4 bytes)
    |  - Location Attributes Table | locations_bytes
    |------------------------------|
    |         String Table         | strings_bytes
    |------------------------------|
    |                              |
    |       Resource Data Blob     |
    |                              |
    \------------------------------/

*/

/// Represents a Java Image (JImage) file, which contains resources used by the Java Virtual Machine (JVM).
#[derive(Debug)]
pub struct JImage {
    mmap: Mmap,
    header: Header,
}

/// Represents the kinds of attributes that can be associated with resources in a JImage file.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AttributeKind {
    END,
    MODULE,
    PARENT,
    BASE,
    EXTENSION,
    OFFSET,
    COMPRESSED,
    UNCOMPRESSED,
    /// Preview mode flags of a location (jimage 1.1+). Only preview mode, which is not supported,
    /// needs them: the regular, non-preview resources are found under their usual names.
    #[allow(dead_code)] // only ever produced by `TryFrom<u8>` while parsing
    PREVIEW,
    COUNT,
}

/// Values of all attributes of a location, indexed by [`AttributeKind`].
type Attributes = [u64; AttributeKind::COUNT as usize];

impl TryFrom<u8> for AttributeKind {
    type Error = JImageError;

    fn try_from(value: u8) -> Result<Self> {
        if value >= AttributeKind::COUNT as u8 {
            Err(JImageError::Internal {
                value: format!("Invalid attribute kind: {}", value),
            })
        } else {
            unsafe { Ok(std::mem::transmute(value)) }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Endianness {
    Big,
    Little,
}

impl JImage {
    /// Opens the specified file and memory-maps it to create a `JImage` instance.
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Self> {
        let file = File::open(path.as_ref()).context(IoSnafu {
            path: path.as_ref().to_path_buf(),
        })?;
        let mmap = unsafe {
            Mmap::map(&file).context(IoSnafu {
                path: path.as_ref().to_path_buf(),
            })?
        };
        let header = Header::from_bytes(&mmap)?;

        Ok(Self { mmap, header })
    }

    /// Finds a resource by name and returns its data.
    pub fn find_resource(&self, name: &str) -> Result<Option<Cow<'_, [u8]>>> {
        // Find offset index using the hash
        let Some(offset_index) = self.find_offset_index(name)? else {
            return Ok(None);
        };

        // Get the attributes for the location index.
        let attribute_index = self.offset_value(offset_index)?;
        let attribute = self.attributes(attribute_index)?;

        // Verify the full name matches the path reconstructed from attributes.
        if !self.verify(&attribute, name)? {
            return Ok(None); // Hash collision, the name doesn't actually match.
        }

        self.get_resource(&attribute).map(Some)
    }

    /// Returns an iterator over all resource names in the JImage file.
    pub fn resource_names_iter(&self) -> ResourceNamesIter<'_> {
        ResourceNamesIter::new(self)
    }

    /// Returns a vector of all resource names in the JImage file.
    pub fn resource_names(&self) -> Result<Vec<ResourceName<'_>>> {
        self.resource_names_iter().collect()
    }

    /// Returns a low-level view of the raw mapped data.
    pub fn raw(&self) -> RawJImage<'_> {
        RawJImage::new(&self.mmap)
    }

    /// Retrieves the resource name at the specified index.
    pub(crate) fn resource_at_index(&self, idx: usize) -> Result<Option<ResourceName<'_>>> {
        let offset_index = self.offset_value(idx)?;
        let attribute = self.attributes(offset_index)?;
        let module = self.get_str_for_attribute(attribute, AttributeKind::MODULE)?;
        if matches!(module.as_ref(), "" | "modules" | "packages") {
            return Ok(None);
        }
        let parent = self.get_str_for_attribute(attribute, AttributeKind::PARENT)?;
        let base = self.get_str_for_attribute(attribute, AttributeKind::BASE)?;
        let extension = self.get_str_for_attribute(attribute, AttributeKind::EXTENSION)?;
        Ok(Some(ResourceName {
            module,
            parent,
            base,
            extension,
        }))
    }

    /// Returns the total number of items (resources) in the JImage file.
    pub(crate) fn items_count(&self) -> usize {
        self.header.items_count() as usize
    }

    fn get_str_for_attribute(
        &self,
        attributes: Attributes,
        kind: AttributeKind,
    ) -> Result<Cow<'_, str>> {
        self.string_table()
            .name(address(attributes[kind as usize])?)
    }

    fn string_table(&self) -> StringTable<'_> {
        StringTable(&self.mmap[self.header.strings(0)..self.header.data(0)])
    }

    fn find_offset_index(&self, name: &str) -> Result<Option<usize>> {
        let items = self.items_count();
        if items == 0 {
            return Ok(None);
        }
        let redirect = self.header.redirect(hash(name, HASH_SEED) % items);
        let value: i32 = read_integer(&self.mmap, redirect, self.header.endianness())?;
        match value {
            ..=-1 => Ok(Some((-1 - value) as usize)),
            0 => Ok(None),
            _ => Ok(Some(hash(name, value) % items)),
        }
    }

    fn offset_value(&self, index: usize) -> Result<u32> {
        if index >= self.items_count() {
            return Err(internal("JImage offset index outside offset table"));
        }
        read_integer(
            &self.mmap,
            self.header.offset(index),
            self.header.endianness(),
        )
    }

    fn attributes(&self, index: u32) -> Result<Attributes> {
        let table = &self.mmap[self.header.attributes(0)..self.header.strings(0)];
        let mut input = table
            .get(index as usize..)
            .ok_or_else(|| internal("JImage location offset outside location table"))?;
        let mut attributes = [0; AttributeKind::COUNT as usize];
        while let Some((&entry, rest)) = input.split_first() {
            let kind = AttributeKind::try_from(entry >> 3)?;
            if kind == AttributeKind::END {
                return Ok(attributes);
            }
            let width = usize::from(entry & 7) + 1;
            if rest.len() < width {
                return Err(internal("Truncated JImage location attribute"));
            }
            let (value, next) = rest.split_at(width);
            attributes[kind as usize] = value
                .iter()
                .fold(0, |number, &byte| (number << 8) | u64::from(byte));
            input = next;
        }
        Err(internal("Unterminated JImage location attributes"))
    }

    fn get_resource(&self, attributes: &Attributes) -> Result<Cow<'_, [u8]>> {
        let offset = address(attributes[AttributeKind::OFFSET as usize])?;
        let compressed_size = address(attributes[AttributeKind::COMPRESSED as usize])?;
        let output_size = address(attributes[AttributeKind::UNCOMPRESSED as usize])?;
        let stored_size = if compressed_size == 0 {
            output_size
        } else {
            compressed_size
        };
        let contents = &self.mmap[self.header.data(0)..];
        let bytes = contents
            .get(offset..)
            .and_then(|remaining| remaining.get(..stored_size))
            .ok_or_else(|| internal("JImage resource range outside resource data"))?;
        if compressed_size == 0 {
            Ok(Cow::Borrowed(bytes))
        } else {
            decompression::resource(
                bytes,
                output_size,
                self.string_table(),
                self.header.endianness(),
            )
            .map(Cow::Owned)
        }
    }

    /// Verify the attributes of the resource.
    /// Full path format: /{module}/{parent}/{base}.{extension}
    fn verify(&self, attributes: &Attributes, full_name: &str) -> Result<bool> {
        let parts_to_check = [
            (AttributeKind::MODULE, "/"),
            (AttributeKind::PARENT, "/"),
            (AttributeKind::BASE, "/"),
            (AttributeKind::EXTENSION, "."),
        ];

        let mut remaining_name = full_name;
        for (kind, prefix) in &parts_to_check {
            let offset = address(attributes[*kind as usize])?;
            let part = self.string_table().name(offset)?;

            if !part.is_empty() {
                remaining_name = if let Some(stripped) = remaining_name.strip_prefix(prefix) {
                    stripped
                } else {
                    return Ok(false);
                };

                remaining_name = if let Some(stripped) = remaining_name.strip_prefix(part.as_ref())
                {
                    stripped
                } else {
                    return Ok(false);
                };
            }
        }

        Ok(remaining_name.is_empty())
    }
}

fn address(value: u64) -> Result<usize> {
    usize::try_from(value).map_err(|_| internal("JImage offset or length exceeds address space"))
}
