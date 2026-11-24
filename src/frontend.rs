// Based on Vineflower's ConsoleDecompiler.
// Copyright 2000-2018 JetBrains s.r.o. Licensed under the Apache License, Version 2.0.

use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clap::{Arg, ArgMatches, Args, Command, FromArgMatches, error::ErrorKind};

use crate::Options;

mod files;
#[cfg(test)]
mod tests;

#[derive(Args)]
struct Cli {
    /// Input .class, directory, .jar or .zip paths, optionally followed by the output path.
    #[arg(required_unless_present = "list_plugins", value_name = "PATH")]
    paths: Vec<PathBuf>,

    /// Explicit output directory or archive; use - for stdout.
    #[arg(short, long, value_name = "DEST")]
    output: Option<PathBuf>,

    /// Write an archive regardless of the output filename extension.
    #[arg(long, conflicts_with_all = ["folder", "legacy_saving"])]
    file: bool,

    /// Write to a directory regardless of the output filename extension.
    #[arg(long, conflicts_with = "legacy_saving")]
    folder: bool,

    /// Rebuild input archives under the destination directory.
    #[arg(long)]
    legacy_saving: bool,

    /// Class, directory or archive used for resolution but not decompiled. Repeatable.
    #[arg(
        short = 'e',
        long,
        require_equals = true,
        value_delimiter = ',',
        value_name = "PATH"
    )]
    add_external: Vec<PathBuf>,

    /// Decompile only classes whose internal names start with a given prefix. Repeatable.
    #[arg(
        long,
        require_equals = true,
        value_delimiter = ',',
        value_name = "PREFIX"
    )]
    only: Vec<String>,

    /// Only report errors.
    #[arg(short, long)]
    silent: bool,

    /// Display compiled-in decompiler plugins.
    #[arg(long)]
    list_plugins: bool,

    #[arg(skip)]
    settings: ArgMatches,
}

struct Setting {
    name: &'static str,
    alternate: &'static str,
    value_name: Option<&'static str>,
    help: &'static str,
}

impl Setting {
    fn arg(&self) -> Arg {
        let arg = Arg::new(self.name).long(self.name).help(self.help);
        let arg = match self.value_name {
            Some(value) => arg.value_name(value).allow_hyphen_values(true),
            None => arg
                .num_args(0..=1)
                .require_equals(true)
                .default_missing_value("1")
                .value_parser(["0", "1", "false", "true"])
                .ignore_case(true),
        };
        if self.alternate.len() > 3 {
            arg.alias(self.alternate)
        } else {
            arg
        }
    }
}

const fn flag(name: &'static str, alternate: &'static str, help: &'static str) -> Setting {
    Setting {
        name,
        alternate,
        value_name: None,
        help,
    }
}

const fn text(
    name: &'static str,
    alternate: &'static str,
    value_name: &'static str,
    help: &'static str,
) -> Setting {
    Setting {
        name,
        alternate,
        value_name: Some(value_name),
        help,
    }
}

const SETTINGS: &[Setting] = &[
    text(
        "indent-string",
        "ind",
        "INDENT",
        "Set the indentation string (default: three spaces)",
    ),
    text(
        "banner",
        "ban",
        "TEXT",
        "Add text at the beginning of each decompiled file",
    ),
    flag(
        "use-lvt-names",
        "udv",
        "Use names from the local variable table",
    ),
    flag(
        "use-method-parameters",
        "ump",
        "Use names from the MethodParameters attribute",
    ),
    flag("remove-synthetic", "rsy", "Omit synthetic declarations"),
    flag("remove-bridge", "rbr", "Omit bridge methods"),
    flag("decompile-generics", "dgs", "Read generic signatures"),
    flag(
        "ascii-strings",
        "asc",
        "Escape non-ASCII characters in literals",
    ),
    flag(
        "hide-default-constructor",
        "hdc",
        "Omit redundant default constructors",
    ),
    flag("hide-empty-super", "hes", "Omit redundant super() calls"),
    flag(
        "bytecode-source-mapping",
        "bsm",
        "Include bytecode-to-source line mappings",
    ),
    flag(
        "dump-original-lines",
        "__dump_original_lines__",
        "Include original source line numbers",
    ),
    flag(
        "unit-test-mode",
        "__unit_test_mode__",
        "Append source maps for test comparisons",
    ),
    flag(
        "new-line-separator",
        "nls",
        "Use LF when enabled or CRLF when disabled",
    ),
    flag(
        "remove-imports",
        "rim",
        "Use fully qualified class names rather than imports",
    ),
    flag(
        "decompile-inner",
        "din",
        "Include nested classes in their enclosing compilation units",
    ),
    flag(
        "sourcefile-comments",
        "sfc",
        "Include the SourceFile attribute in a comment",
    ),
    flag(
        "decompile-assert",
        "das",
        "Recover assert statements from compiler-generated guards",
    ),
    flag(
        "override-annotation",
        "",
        "Restore @Override when the overridden declaration is available",
    ),
    text(
        "method-to-decompile",
        "",
        "METHOD",
        "Decompile only the specified JVM method",
    ),
    flag(
        "resugar-idea-notnull",
        "inn",
        "Resugar IntelliJ IDEA's generated @NotNull checks",
    ),
    flag(
        "force-jsr-inline",
        "fji",
        "Inline legacy subroutines regardless of class version",
    ),
    flag(
        "decompile-kotlin",
        "kt-enable",
        "Recover Kotlin source from Kotlin class files",
    ),
    flag(
        "kt-decompile-facades",
        "",
        "Recover Kotlin multifile facades and their source parts",
    ),
    flag(
        "keep-literals",
        "lit",
        "Keep special floating-point literals without resugaring",
    ),
    flag(
        "rename-members",
        "ren",
        "Rename classes and members with unusable identifiers",
    ),
    text(
        "preferred-line-length",
        "pll",
        "WIDTH",
        "Preferred maximum line length before wrapping",
    ),
    text(
        "include-runtime",
        "jrt",
        "JDK",
        "Use a JDK's class library; 1/current reads JAVA_HOME",
    ),
    flag("include-classpath", "iec", "Read libraries from CLASSPATH"),
    text(
        "variable-renaming",
        "",
        "SCHEME",
        "Rename local variables using jad or tiny naming",
    ),
    flag(
        "rename-parameters",
        "",
        "Include parameters when renaming local variables",
    ),
    flag(
        "jad-style-variable-naming",
        "jvn",
        "Use legacy JAD naming for local variables",
    ),
    flag(
        "jad-style-parameter-naming",
        "jpr",
        "Use legacy JAD naming for parameters",
    ),
    flag(
        "skip-extra-files",
        "sef",
        "Do not copy non-class files to the output",
    ),
];

fn expand_config(
    args: impl IntoIterator<Item = OsString>,
) -> Result<Vec<OsString>, files::FrontendError> {
    let mut expanded = Vec::new();
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        if arg == "--" {
            expanded.push(arg);
            expanded.extend(args);
            break;
        }
        let config = if arg == "-cfg" {
            Some(PathBuf::from(
                args.next().ok_or(files::FrontendError::MissingConfig)?,
            ))
        } else {
            arg.to_str()
                .and_then(|arg| arg.strip_prefix("-cfg="))
                .map(PathBuf::from)
        };
        if let Some(config) = config {
            let content = fs::read_to_string(&config)
                .map_err(|error| files::io_error("read config", &config, error))?;
            expanded.extend(content.lines().map(OsString::from));
        } else {
            expanded.push(arg);
        }
    }
    Ok(expanded)
}

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
        if let Some(name) = text.strip_prefix("--no-")
            && let Some(setting) = SETTINGS.iter().find(|setting| {
                setting.value_name.is_none()
                    && (setting.name == name
                        || (setting.alternate.len() > 3 && setting.alternate == name))
            })
        {
            return OsString::from(format!("--{}=0", setting.name));
        }
        if let Some((short, value)) = text.strip_prefix('-').and_then(|arg| arg.split_once('=')) {
            if short == "only" {
                return OsString::from(format!("--only={value}"));
            }
            if let Some(setting) = SETTINGS
                .iter()
                .find(|setting| short.len() == 3 && setting.alternate == short)
            {
                return OsString::from(format!("--{}={value}", setting.name));
            }
        }
        arg
    })
}

impl Cli {
    fn try_parse_from(args: impl IntoIterator<Item = OsString>) -> Result<Self, clap::Error> {
        let command = Command::new("vineflower-rs")
            .version(env!("CARGO_PKG_VERSION"))
            .about("Decompile JVM class files without Java")
            .after_help(
                "With one path, write Java sources to stdout. Otherwise the last path is the\n\
                 output unless -o is supplied. Resources are copied to directories and archives,\n\
                 not to stdout. Boolean settings accept =0, =1, or a --no- prefix. Use -- to pass\n\
                 paths starting with a hyphen. Use -cfg=<path> to read arguments (one per line).",
            )
            .args_override_self(true)
            .args(SETTINGS.iter().map(Setting::arg));
        let mut matches = Self::augment_args(command).try_get_matches_from(args)?;
        let mut cli = Self::from_arg_matches_mut(&mut matches)?;
        cli.settings = matches;
        Ok(cli)
    }

    fn options(&self) -> Result<Options, crate::OptionError> {
        let mut options = Options::default();
        for setting in SETTINGS
            .iter()
            .filter(|setting| setting.name != "skip-extra-files")
        {
            if let Some(value) = self.settings.get_one::<String>(setting.name) {
                let value = if setting.value_name.is_none() {
                    if value == "1" || value.eq_ignore_ascii_case("true") {
                        "1"
                    } else {
                        "0"
                    }
                } else {
                    value
                };
                options.set(setting.name, value)?;
            }
        }
        Ok(options)
    }

    fn skip_extra_files(&self) -> bool {
        self.settings
            .get_one::<String>("skip-extra-files")
            .is_some_and(|value| value == "1" || value.eq_ignore_ascii_case("true"))
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
            Some(path) if self.legacy_saving => Ok(Destination::Legacy(path)),
            Some(path) if self.file || (!self.folder && is_archive_destination(&path)) => {
                Ok(Destination::Archive(path))
            }
            Some(path) => Ok(Destination::Directory(path)),
            None if self.file || self.folder || self.legacy_saving => {
                Err(files::FrontendError::MissingDestination)
            }
            None => Ok(Destination::Stdout),
        }
    }
}

fn is_archive(path: &Path) -> bool {
    path.extension().is_some_and(|ext| {
        ext.eq_ignore_ascii_case(OsStr::new("zip")) || ext.eq_ignore_ascii_case(OsStr::new("jar"))
    })
}

fn is_archive_destination(path: &Path) -> bool {
    is_archive(path)
        || path
            .file_name()
            .and_then(OsStr::to_str)
            .is_some_and(|name| name.contains(".jar") || name.contains(".zip"))
}

fn write_plugins(stdout: &mut impl Write) -> io::Result<()> {
    const PLUGINS: &[(&str, &str)] = &[
        (
            "IdeaNotNull",
            "Decompiles code inserted by IntelliJ IDEA's @NotNull annotation.",
        ),
        ("Kotlin", "Detects and decompiles Kotlin class files."),
        (
            "VariableRenaming",
            "Allows automatic renaming of variables with a common naming scheme.",
        ),
    ];
    writeln!(
        stdout,
        "=== Vineflower Decompiler {} ===\n",
        env!("CARGO_PKG_VERSION")
    )?;
    writeln!(stdout, "Loaded {} plugins:", PLUGINS.len())?;
    for (name, description) in PLUGINS {
        writeln!(
            stdout,
            "{name} (loaded from native code)\n - {description}\n"
        )?;
    }
    stdout.flush()
}

enum Destination {
    Stdout,
    Directory(PathBuf),
    Archive(PathBuf),
    Legacy(PathBuf),
}

/// Process the command line arguments, excluding the executable name.
pub fn run(args: impl IntoIterator<Item = OsString>) -> Result<(), Box<dyn Error>> {
    run_with_output(args, &mut io::stdout().lock())
}

fn run_with_output(
    args: impl IntoIterator<Item = OsString>,
    stdout: &mut impl Write,
) -> Result<(), Box<dyn Error>> {
    let args = std::iter::once(OsString::from("vineflower-rs"))
        .chain(normalize_args(expand_config(args)?));
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
    if cli.list_plugins {
        write_plugins(stdout)?;
        return Ok(());
    }
    let options = cli.options()?;
    let destination = cli.destination()?;
    let skip_extra_files = cli.skip_extra_files();
    files::decompile_paths(
        cli.paths,
        destination,
        &options,
        files::Selection {
            libraries: cli.add_external,
            only: cli.only,
            silent: cli.silent,
            skip_extra_files,
        },
        stdout,
    )?;
    Ok(())
}
