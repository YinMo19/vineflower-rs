// Based on Vineflower StructModuleAttribute and ClassWriter (Apache-2.0).
use std::fmt::Write;

use super::{DecompileError, Writer};
use crate::classfile::{Constant, ConstantPool, find_attribute};

impl Writer<'_, '_> {
    pub(super) fn module(&mut self) -> Result<(), DecompileError> {
        let pool = &self.class.pool;
        let data = find_attribute(&self.class.attributes, pool, "Module")?.ok_or(invalid())?;
        let mut reader = ModuleReader(data);
        let module = module_name(pool, reader.u16()?)?;
        let flags = reader.u16()?;
        reader.u16()?; // module version: not a Java source directive
        self.class_annotations(0)?;
        self.line(
            0,
            &format!(
                "{}module {module} {{",
                if flags & 0x0020 != 0 { "open " } else { "" }
            ),
        );
        let mut have_group = false;
        for _ in 0..reader.u16()? {
            let module = module_name(pool, reader.u16()?)?;
            let flags = reader.u16()?;
            reader.u16()?;
            if module == "java.base" && flags & 0x8000 != 0 {
                continue;
            }
            have_group = true;
            let transitive = if flags & 0x0020 != 0 {
                "transitive "
            } else {
                ""
            };
            let static_phase = if flags & 0x0040 != 0 { "static " } else { "" };
            self.line(1, &format!("requires {transitive}{static_phase}{module};"));
        }
        for kind in ["exports", "opens"] {
            let count = reader.u16()?;
            if count == 0 {
                continue;
            }
            if have_group {
                self.line(0, "");
            }
            have_group = true;
            for _ in 0..count {
                let package = package_name(pool, reader.u16()?)?;
                reader.u16()?; // synthetic/mandated bits have no source spelling
                let targets = reader.u16()?;
                if targets == 0 {
                    self.line(1, &format!("{kind} {package};"));
                } else {
                    self.line(1, &format!("{kind} {package} to"));
                    for index in 0..targets {
                        let module = module_name(pool, reader.u16()?)?;
                        self.line(2, &format!("{module}{}", separator(index, targets)));
                    }
                }
            }
        }
        let uses = reader.u16()?;
        if uses != 0 && have_group {
            self.line(0, "");
        }
        have_group |= uses != 0;
        for _ in 0..uses {
            let service = pool.class_name(reader.u16()?)?.replace('/', ".");
            self.line(1, &format!("uses {service};"));
        }
        let provides = reader.u16()?;
        if provides != 0 && have_group {
            self.line(0, "");
        }
        for _ in 0..provides {
            let service = pool.class_name(reader.u16()?)?.replace('/', ".");
            self.line(1, &format!("provides {service} with"));
            let implementations = reader.u16()?;
            if implementations == 0 {
                return Err(invalid());
            }
            let mut implementation = String::new();
            for index in 0..implementations {
                implementation.clear();
                let class = pool.class_name(reader.u16()?)?;
                for segment in class.split_inclusive('/') {
                    if let Some(segment) = segment.strip_suffix('/') {
                        implementation.push_str(segment);
                        implementation.push('.');
                    } else {
                        implementation.push_str(segment);
                    }
                }
                let _ = write!(implementation, "{}", separator(index, implementations));
                self.line(2, &implementation);
            }
        }
        if !reader.0.is_empty() {
            return Err(invalid());
        }
        self.line(0, "}");
        Ok(())
    }
}

fn separator(index: u16, count: u16) -> char {
    if index + 1 == count { ';' } else { ',' }
}
fn invalid() -> DecompileError {
    DecompileError::InvalidAttribute("Module")
}

fn module_name<'p>(pool: &'p ConstantPool<'_>, index: u16) -> Result<&'p str, DecompileError> {
    let Constant::Module(index) = pool.get(index)? else {
        return Err(invalid());
    };
    Ok(pool.utf8(*index)?)
}

fn package_name(pool: &ConstantPool<'_>, index: u16) -> Result<String, DecompileError> {
    let Constant::Package(index) = pool.get(index)? else {
        return Err(invalid());
    };
    Ok(pool.utf8(*index)?.replace('/', "."))
}

struct ModuleReader<'a>(&'a [u8]);
impl ModuleReader<'_> {
    fn u16(&mut self) -> Result<u16, DecompileError> {
        let (value, rest) = self.0.split_first_chunk().ok_or(invalid())?;
        self.0 = rest;
        Ok(u16::from_be_bytes(*value))
    }
}
