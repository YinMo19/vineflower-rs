use std::env;
use std::path::PathBuf;
use std::sync::Arc;

use thiserror::Error;

use crate::{classpath::{ClassPath, ClassPathError}, javadoc::JavadocProvider};

/// Settings controlling JVM names, source formatting and source maps.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Options {
    pub indent: String,
    pub use_debug_names: bool,
    pub use_method_parameters: bool,
    pub remove_synthetic: bool,
    pub remove_bridge: bool,
    pub decompile_generics: bool,
    pub ascii_strings: bool,
    pub hide_default_constructor: bool,
    pub hide_empty_super: bool,
    pub include_line_mappings: bool,
    pub dump_original_lines: bool,
    pub unit_test_mode: bool,
    pub crlf: bool,
    pub remove_imports: bool,
    pub banner: String,
    pub decompile_inner: bool,
    pub decompile_kotlin: bool,
    pub sourcefile_comments: bool,
    pub method_to_decompile: String,
    pub javadoc: Option<Arc<dyn JavadocProvider>>,
    pub idea_notnull: bool,
    pub force_jsr_inline: bool,
    pub keep_literals: bool,
    pub preferred_line_length: usize,
    pub variable_renaming: Option<String>,
    pub rename_parameters: bool,
    pub jad_style_variable_naming: bool,
    pub jad_style_parameter_naming: bool,
    pub rename_members: bool,
    pub library_classpath: Option<Arc<ClassPath>>,
    pub runtime_classpath: Option<Arc<ClassPath>>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            indent: "   ".into(),
            use_debug_names: true,
            use_method_parameters: true,
            remove_synthetic: true,
            remove_bridge: true,
            decompile_generics: true,
            ascii_strings: false,
            hide_default_constructor: true,
            hide_empty_super: true,
            include_line_mappings: false,
            dump_original_lines: false,
            unit_test_mode: false,
            crlf: false,
            remove_imports: false,
            banner: String::new(),
            decompile_inner: true,
            decompile_kotlin: false,
            sourcefile_comments: false,
            method_to_decompile: String::new(),
            javadoc: None,
            idea_notnull: true,
            force_jsr_inline: false,
            keep_literals: false,
            preferred_line_length: 160,
            variable_renaming: None,
            rename_parameters: false,
            jad_style_variable_naming: false,
            jad_style_parameter_naming: false,
            rename_members: false,
            library_classpath: None,
            runtime_classpath: None,
        }
    }
}

#[derive(Debug, Error)]
pub enum OptionError {
    #[error("unsupported decompiler option {0:?}")]
    Unsupported(String),
    #[error(transparent)]
    Classpath(#[from] ClassPathError),
    #[error("invalid value {value:?} for option {name:?}; expected {expected}")]
    Invalid {
        name: String,
        value: String,
        expected: &'static str,
    },
}

impl Options {
    /// Set a supported Vineflower option by its long name.
    pub fn set(&mut self, name: &str, value: &str) -> Result<(), OptionError> {
        let invalid = |expected| OptionError::Invalid {
            name: name.into(),
            value: value.into(),
            expected,
        };
        let flag = || match value {
            "1" | "true" => Ok(true),
            "0" | "false" => Ok(false),
            _ => Err(invalid("true, false, 1 or 0")),
        };
        match name {
            "indent-string" => {
                if !value.bytes().all(|b| matches!(b, b' ' | b'\t')) {
                    return Err(invalid("a string of spaces or tabs"));
                }
                self.indent = value.into();
            }
            "banner" => self.banner = value.into(),
            "use-lvt-names" => self.use_debug_names = flag()?,
            "use-method-parameters" => self.use_method_parameters = flag()?,
            "remove-synthetic" => self.remove_synthetic = flag()?,
            "remove-bridge" => self.remove_bridge = flag()?,
            "decompile-generics" => self.decompile_generics = flag()?,
            "ascii-strings" => self.ascii_strings = flag()?,
            "hide-default-constructor" => self.hide_default_constructor = flag()?,
            "hide-empty-super" => self.hide_empty_super = flag()?,
            "bytecode-source-mapping" => self.include_line_mappings = flag()?,
            "__dump_original_lines__" | "dump-original-lines" => self.dump_original_lines = flag()?,
            "__unit_test_mode__" | "unit-test-mode" => self.unit_test_mode = flag()?,
            "new-line-separator" => self.crlf = !flag()?,
            "remove-imports" => self.remove_imports = flag()?,
            "decompile-inner" => self.decompile_inner = flag()?,
            "decompile-kotlin" => self.decompile_kotlin = flag()?,
            "sourcefile-comments" => self.sourcefile_comments = flag()?,
            "method-to-decompile" => self.method_to_decompile = value.into(),
            "resugar-idea-notnull" => self.idea_notnull = flag()?,
            "force-jsr-inline" => self.force_jsr_inline = flag()?,
            "keep-literals" => self.keep_literals = flag()?,
            "rename-members" => self.rename_members = flag()?,
            "preferred-line-length" => {
                self.preferred_line_length = value.parse().ok().filter(|&width| width != 0)
                    .ok_or_else(|| invalid("a positive integer"))?;
            }
            "include-classpath" => {
                self.library_classpath = if flag()? {
                    let mut path = ClassPath::new();
                    if let Some(roots) = env::var_os("CLASSPATH") {
                        for root in env::split_paths(&roots) {
                            path.add(if root.as_os_str().is_empty() { PathBuf::from(".") } else { root })?;
                        }
                    } else {
                        path.add(".")?;
                    }
                    Some(Arc::new(path))
                } else {
                    None
                };
            }
            "include-runtime" => {
                self.runtime_classpath = match value {
                    "" | "0" => None,
                    "1" | "current" => {
                        let home = env::var_os("JAVA_HOME")
                            .ok_or_else(|| invalid("a JDK path, or JAVA_HOME for 1/current"))?;
                        Some(Arc::new(ClassPath::for_java_home(home)?))
                    }
                    home => Some(Arc::new(ClassPath::for_java_home(home)?)),
                };
            }
            "variable-renaming" => self.variable_renaming = Some(value.into()),
            "rename-parameters" => self.rename_parameters = flag()?,
            "jad-style-variable-naming" => self.jad_style_variable_naming = flag()?,
            "jad-style-parameter-naming" => self.jad_style_parameter_naming = flag()?,
            _ => return Err(OptionError::Unsupported(name.into())),
        }
        Ok(())
    }
}
