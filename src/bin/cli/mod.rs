//! The command model shared by argument parsing, help and shell completions.

use std::{ffi::OsString, fs, io, path::PathBuf};

use clap::{Arg, ArgAction, ArgGroup, ArgMatches, CommandFactory, Parser, Subcommand, ValueHint};
use clap_complete::{Generator, Shell};
use clap_lex::OsStrExt;
use vineflower_rs::engine::{
    Options,
    options::{PREFERENCES, PreferenceKind, PreferenceSpec},
};

/// Vineflower-rs: Native Java decompiler
/// By YinMo19.
///
/// Boolean preferences accept --name, --no-name, or --name=true/false/1/0.
/// Vineflower's three-letter options are also supported, e.g. -thr=4.
#[derive(Parser)]
#[command(
    verbatim_doc_comment,
    name = env!("CARGO_BIN_NAME"),
    bin_name = env!("CARGO_BIN_NAME"),
    version,
    help_template = help_template(),
    args_override_self = true
)]
#[command(group(ArgGroup::new("output mode").args(["folder", "file", "legacy_saving"])))]
pub(super) struct Cli {
    /// Input class files, directories or archives. With two or more paths the last is the destination.
    /// A single input prints the decompiled sources to stdout.
    #[arg(value_name = "PATH", value_hint = ValueHint::AnyPath)]
    pub paths: Vec<PathBuf>,

    /// Expand classes and resources into a directory.
    #[arg(long, help_heading = "Output")]
    pub folder: bool,

    /// Write classes and resources to a ZIP or JAR.
    #[arg(long, help_heading = "Output")]
    pub file: bool,

    /// Preserve the original names of input archives in the output directory.
    #[arg(long, help_heading = "Output")]
    pub legacy_saving: bool,

    /// Add libraries for type lookup. Repeat or separate paths with commas.
    #[arg(short = 'e', long, value_name = "PATH", value_delimiter = ',', value_hint = ValueHint::AnyPath)]
    pub add_external: Vec<PathBuf>,

    /// Select classes by internal-name prefix, e.g. com/example/. Repeat or separate prefixes with commas.
    #[arg(long, value_name = "PREFIX", value_delimiter = ',')]
    pub only: Vec<String>,

    /// Read one argument per line at this position (also -cfg FILE).
    #[arg(long, value_name = "FILE", value_hint = ValueHint::FilePath)]
    config: Vec<PathBuf>,

    /// Show only errors in the decompiler log.
    #[arg(short, long)]
    pub silent: bool,

    /// List the bundled decompiler plugins.
    #[arg(long)]
    pub list_plugins: bool,

    #[command(subcommand)]
    pub action: Option<Action>,
}

#[derive(Subcommand)]
pub(super) enum Action {
    /// Write a shell completion script to stdout.
    Completions {
        /// Shell that will load the script.
        #[arg(value_enum)]
        shell: Shell,
    },
}

fn help_template() -> String {
    let styles = clap::builder::Styles::styled();
    let heading = styles.get_header();
    format!(
        "{{about-with-newline}}
{{usage-heading}} {{usage}}

{heading}Examples:{heading:#}
  # Decompile a JAR into the out/ directory
  {{name}} app.jar out/

  # Print the Java source for one class to the terminal
  {{name}} Example.class

  # Save the decompiled sources and resources in a ZIP
  {{name}} --file app.jar sources.zip

{{all-args}}"
    )
}

pub(super) fn command() -> clap::Command {
    with_preferences(PREFERENCES)
}

pub(super) fn completions(shell: Shell, out: &mut dyn io::Write) -> io::Result<()> {
    // Fish validates every long name in its option specification, even hidden
    // ones. The engine's internal __test__ names are not valid Fish options.
    let mut command = with_preferences(PREFERENCES.iter().filter(|p| !p.name.starts_with("__")));
    command.build();
    shell.try_generate(&command, out)
}

fn with_preferences(specs: impl IntoIterator<Item = &'static PreferenceSpec>) -> clap::Command {
    let mut command = Cli::command();
    for spec in specs {
        let help = match (spec.kind, spec.default_help) {
            (PreferenceKind::Text, Some(value)) if value.trim().is_empty() => {
                format!("{} [default: {value:?}]", spec.help)
            }
            (_, Some(value)) => format!("{} [default: {value}]", spec.help),
            (_, None) => spec.help.to_owned(),
        };
        let mut arg = Arg::new(spec.name)
            .long(spec.name)
            .help(help)
            .help_heading("Decompiler preferences")
            .hide_short_help(spec.name != "thread-count")
            .hide(spec.name.starts_with("__"));
        if let Some(alias) = spec.alias {
            arg = arg.alias(alias);
        }
        arg = match spec.kind {
            PreferenceKind::Bool => {
                let negative = format!("no-{}", spec.name);
                command = command.arg(
                    Arg::new(negative.clone())
                        .long(negative.clone())
                        .action(ArgAction::SetTrue)
                        .overrides_with(spec.name)
                        .help(format!("Disable --{}.", spec.name))
                        .hide_short_help(true)
                        .hide_long_help(true)
                        .hide(spec.name.starts_with("__")),
                );
                arg.value_name("BOOL")
                    .value_parser(["true", "false", "1", "0"])
                    .hide_possible_values(true)
                    .ignore_case(true)
                    .num_args(0..=1)
                    .require_equals(true)
                    .default_missing_value("1")
                    .overrides_with(negative)
            }
            PreferenceKind::Integer => arg.value_name("N").allow_negative_numbers(true),
            PreferenceKind::Text => match spec.name {
                "log-level" => arg
                    .value_name("LEVEL")
                    .value_parser(["TRACE", "INFO", "WARN", "ERROR"])
                    .ignore_case(true),
                "include-runtime" => arg.value_name("JDK").value_hint(ValueHint::DirPath),
                _ => arg.value_name("VALUE"),
            },
        };
        command = command.arg(arg);
    }
    command
}

pub(super) fn options(matches: &ArgMatches, silent: bool) -> Result<Options, clap::Error> {
    let mut options = Options::default();
    options.idea_notnull = true;
    options.decompile_kotlin = true;
    for spec in PREFERENCES {
        if let Some(value) = matches.get_one::<String>(spec.name) {
            // The original parser also accepts true and false for numeric preferences.
            let value = match spec.kind {
                PreferenceKind::Bool | PreferenceKind::Integer
                    if value.eq_ignore_ascii_case("true") =>
                {
                    "1"
                }
                PreferenceKind::Bool | PreferenceKind::Integer
                    if value.eq_ignore_ascii_case("false") =>
                {
                    "0"
                }
                _ => value,
            };
            if spec.kind == PreferenceKind::Integer && value.parse::<i32>().is_err() {
                return Err(command().error(
                    clap::error::ErrorKind::ValueValidation,
                    format!(
                        "invalid value '{value}' for '--{} <N>': expected a 32-bit integer",
                        spec.name
                    ),
                ));
            }
            options.set(spec.name, value);
        } else if spec.kind == PreferenceKind::Bool
            && matches.get_flag(&format!("no-{}", spec.name))
        {
            options.set(spec.name, "0");
        }
    }
    if silent && matches.index_of("silent") > matches.index_of("log-level") {
        options.log_level = "error".into();
    }
    Ok(options)
}

// Expand argument files in place before clap runs. '--' also applies to the
// remaining outer arguments when it occurs inside an argument file.
pub(super) fn arguments(args: Vec<OsString>) -> io::Result<Vec<OsString>> {
    let mut output = Vec::new();
    expand(args, &mut output, &mut Vec::new(), &mut false)?;
    Ok(output)
}

fn expand(
    args: Vec<OsString>,
    output: &mut Vec<OsString>,
    files: &mut Vec<PathBuf>,
    positional: &mut bool,
) -> io::Result<()> {
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        if *positional || arg == "--" {
            output.push(arg);
            output.extend(args);
            *positional = true;
            break;
        }
        let file = if arg == "-cfg" || arg == "--config" {
            Some(PathBuf::from(args.next().ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "expected a file after --config",
                )
            })?))
        } else {
            arg.strip_prefix("-cfg=")
                .or_else(|| arg.strip_prefix("--config="))
                .map(PathBuf::from)
        };
        if let Some(path) = file {
            let read_error = |e: io::Error| {
                io::Error::new(e.kind(), format!("config '{}': {e}", path.display()))
            };
            let canonical = fs::canonicalize(&path).map_err(read_error)?;
            if files.contains(&canonical) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("recursive config file '{}'", path.display()),
                ));
            }
            files.push(canonical);
            let contents = fs::read_to_string(&path).map_err(read_error)?;
            expand(
                contents.lines().map(OsString::from).collect(),
                output,
                files,
                positional,
            )?;
            files.pop();
        } else {
            output.push(legacy_arg(arg));
        }
    }
    Ok(())
}

fn legacy_arg(arg: OsString) -> OsString {
    let Some(text) = arg.to_str() else { return arg };
    if text == "-help" {
        return "--help".into();
    }
    if let Some(short) = text.strip_prefix('-').filter(|s| !s.starts_with('-')) {
        let key = short.split('=').next().unwrap_or(short);
        if key == "only" || PREFERENCES.iter().any(|p| p.alias == Some(key)) {
            return format!("--{short}").into();
        }
    }
    if let Some(name) = text.strip_prefix("--no-")
        && let Some(spec) = PREFERENCES
            .iter()
            .find(|p| p.name == name || p.alias == Some(name))
        && (spec.kind != PreferenceKind::Bool || name != spec.name)
    {
        return format!("--{}=0", spec.name).into();
    }
    arg
}
