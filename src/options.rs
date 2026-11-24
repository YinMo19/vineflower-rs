use thiserror::Error;

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
        }
    }
}

#[derive(Debug, Error)]
pub enum OptionError {
    #[error("unsupported decompiler option {0:?}")]
    Unsupported(String),
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
            _ => return Err(OptionError::Unsupported(name.into())),
        }
        Ok(())
    }
}
