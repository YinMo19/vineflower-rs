// Based on Vineflower's ConsoleDecompiler.
// Copyright 2000-2018 JetBrains s.r.o. Licensed under the Apache License, Version 2.0.

use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clap::{Parser, error::ErrorKind};

use crate::Options;

mod files;
#[cfg(test)]
mod tests;

#[derive(Parser)]
#[command(
    version,
    about = "Decompile JVM class files without Java",
    after_help = "With one path, write Java sources to stdout. Otherwise the last path is the\
        \noutput unless -o is supplied. Resources are copied to directories and archives,\
        \nnot to stdout. Boolean settings accept =0, =1, or a --no- prefix. Use -- to pass\
        \npaths starting with a hyphen.",
    args_override_self = true
)]
struct Cli {
    /// Input .class, directory, .jar or .zip paths, optionally followed by the output path.
    #[arg(required = true, value_name = "PATH")]
    paths: Vec<PathBuf>,

    /// Explicit output directory or archive; use - for stdout.
    #[arg(short, long, value_name = "DEST")]
    output: Option<PathBuf>,

    /// Write an archive regardless of the output filename extension.
    #[arg(long, conflicts_with = "folder")]
    file: bool,

    /// Write to a directory regardless of the output filename extension.
    #[arg(long)]
    folder: bool,

    /// Set the indentation string (default: three spaces).
    #[arg(long = "indent-string", value_name = "INDENT")]
    indent: Option<String>,

    /// Use names from the local variable table (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    use_lvt_names: Option<String>,

    /// Omit synthetic declarations (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    remove_synthetic: Option<String>,

    /// Use parameter names from the MethodParameters attribute (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    use_method_parameters: Option<String>,

    /// Omit bridge methods (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    remove_bridge: Option<String>,

    /// Read generic signatures (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    decompile_generics: Option<String>,

    /// Escape non-ASCII characters in literals (default: false).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    ascii_strings: Option<String>,

    /// Omit no-argument constructors that only call super() (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    hide_default_constructor: Option<String>,

    /// Include the bytecode-to-source line mapping (default: false).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    bytecode_source_mapping: Option<String>,

    /// Include original source line numbers (default: false).
    #[arg(long, alias = "__dump_original_lines__", num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    dump_original_lines: Option<String>,

    /// Omit redundant super() calls (default: true).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    hide_empty_super: Option<String>,

    /// Append source maps for test comparisons (default: false).
    #[arg(long, alias = "__unit_test_mode__", num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    unit_test_mode: Option<String>,

    /// Use LF when enabled or CRLF when disabled (default: LF).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    new_line_separator: Option<String>,

    /// Use fully qualified class names rather than imports (default: false).
    #[arg(long, num_args = 0..=1, require_equals = true, default_missing_value = "1")]
    remove_imports: Option<String>,

    /// Add text at the beginning of each decompiled file.
    #[arg(long, value_name = "TEXT")]
    banner: Option<String>,
}

const LEGACY_OPTIONS: &[(&str, &str)] = &[
    ("ind", "indent-string"),
    ("ban", "banner"),
    ("udv", "use-lvt-names"),
    ("ump", "use-method-parameters"),
    ("rsy", "remove-synthetic"),
    ("rbr", "remove-bridge"),
    ("dgs", "decompile-generics"),
    ("asc", "ascii-strings"),
    ("hdc", "hide-default-constructor"),
    ("hes", "hide-empty-super"),
    ("bsm", "bytecode-source-mapping"),
    ("nls", "new-line-separator"),
    ("rim", "remove-imports"),
];

fn normalize_args(args: impl IntoIterator<Item = OsString>) -> impl Iterator<Item = OsString> {
    let mut positional_only = false;
    args.into_iter().map(move |arg| {
        if positional_only {
            return arg;
        }
        if arg == "--" {
            positional_only = true;
            return arg;
        }
        let Some(text) = arg.to_str() else {
            return arg;
        };
        if text == "-help" {
            return OsString::from("--help");
        }
        if let Some(name) = text.strip_prefix("--no-") {
            let supported_bool = matches!(
                name,
                "dump-original-lines"
                    | "__dump_original_lines__"
                    | "unit-test-mode"
                    | "__unit_test_mode__"
            ) || (!matches!(name, "indent-string" | "banner")
                && LEGACY_OPTIONS.iter().any(|&(_, long)| long == name));
            if supported_bool {
                return OsString::from(format!("--{name}=0"));
            }
        }
        if let Some((short, value)) = text.strip_prefix('-').and_then(|arg| arg.split_once('='))
            && let Some((_, long)) = LEGACY_OPTIONS.iter().find(|&&(name, _)| name == short)
        {
            return OsString::from(format!("--{long}={value}"));
        }
        arg
    })
}

impl Cli {
    fn options(&self) -> Result<Options, crate::OptionError> {
        let mut options = Options::default();
        for (name, value) in [
            ("indent-string", &self.indent),
            ("use-lvt-names", &self.use_lvt_names),
            ("use-method-parameters", &self.use_method_parameters),
            ("remove-synthetic", &self.remove_synthetic),
            ("remove-bridge", &self.remove_bridge),
            ("decompile-generics", &self.decompile_generics),
            ("ascii-strings", &self.ascii_strings),
            ("hide-default-constructor", &self.hide_default_constructor),
            ("bytecode-source-mapping", &self.bytecode_source_mapping),
            ("__dump_original_lines__", &self.dump_original_lines),
            ("hide-empty-super", &self.hide_empty_super),
            ("__unit_test_mode__", &self.unit_test_mode),
            ("new-line-separator", &self.new_line_separator),
            ("remove-imports", &self.remove_imports),
            ("banner", &self.banner),
        ] {
            if let Some(value) = value {
                options.set(name, value)?;
            }
        }
        Ok(options)
    }

    fn destination(&mut self) -> Result<Destination, files::FrontendError> {
        let path = self.output.take().or_else(|| {
            if self.paths.len() > 1 {
                self.paths.pop()
            } else {
                None
            }
        });
        match path.filter(|path| path != Path::new("-")) {
            Some(path) if self.file || (!self.folder && is_archive(&path)) => {
                Ok(Destination::Archive(path))
            }
            Some(path) => Ok(Destination::Directory(path)),
            None if self.file || self.folder => Err(files::FrontendError::MissingDestination),
            None => Ok(Destination::Stdout),
        }
    }
}

fn is_archive(path: &Path) -> bool {
    path.extension().is_some_and(|ext| {
        ext.eq_ignore_ascii_case(OsStr::new("zip")) || ext.eq_ignore_ascii_case(OsStr::new("jar"))
    })
}

enum Destination {
    Stdout,
    Directory(PathBuf),
    Archive(PathBuf),
}

/// Process the command line arguments, excluding the executable name.
pub fn run(args: impl IntoIterator<Item = OsString>) -> Result<(), Box<dyn Error>> {
    run_with_output(args, &mut io::stdout().lock())
}

fn run_with_output(
    args: impl IntoIterator<Item = OsString>,
    stdout: &mut impl Write,
) -> Result<(), Box<dyn Error>> {
    let args = std::iter::once(OsString::from("vineflower-rs")).chain(normalize_args(args));
    let mut cli = match Cli::try_parse_from(args) {
        Ok(cli) => cli,
        Err(error)
            if matches!(
                error.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) =>
        {
            write!(stdout, "{error}")?;
            stdout.flush()?;
            return Ok(());
        }
        Err(error) => return Err(error.into()),
    };
    let options = cli.options()?;
    let destination = cli.destination()?;
    files::decompile_paths(cli.paths, destination, &options, stdout)?;
    Ok(())
}
