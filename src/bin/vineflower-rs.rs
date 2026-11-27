//! Command-line front end for the native Java pipeline.

mod cli;

use std::{
    env,
    ffi::{OsStr, OsString},
    fs, io,
    io::Write,
    path::Path,
    process::ExitCode,
};

use clap::FromArgMatches;
use cli::{Action, Cli};
use log::{Level, LevelFilter, Log, Metadata, Record};
use vineflower_rs::engine::driver::{Decompiler, Output};

fn main() -> ExitCode {
    match run(env::args_os().skip(1).collect()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(arguments: Vec<OsString>) -> io::Result<()> {
    let args = cli::arguments(arguments)?;
    let mut command = cli::command();
    if args.is_empty() {
        command.print_help()?;
        return Ok(());
    }
    let matches = command
        .try_get_matches_from_mut(
            std::iter::once(OsString::from(env!("CARGO_BIN_NAME"))).chain(args),
        )
        .unwrap_or_else(|e| e.exit());
    let cli = Cli::from_arg_matches(&matches).unwrap_or_else(|e| e.exit());
    if let Some(Action::Completions { shell }) = cli.action {
        return cli::completions(shell, &mut io::stdout().lock());
    }
    if cli.list_plugins {
        print_plugins(&command);
        return Ok(());
    }
    let options = cli::options(&matches, cli.silent).unwrap_or_else(|e| e.exit());
    configure_log(&options.log_level);
    let mut paths = cli.paths;
    let mut destination = paths.pop();
    let mut sources: Vec<_> = paths
        .into_iter()
        .filter(|path| input_exists(path))
        .collect();
    if sources.is_empty()
        && let Some(last) = destination.take()
        && input_exists(&last)
    {
        sources.push(last);
    }
    if sources.is_empty() {
        command
            .error(
                clap::error::ErrorKind::MissingRequiredArgument,
                "no sources given",
            )
            .exit();
    }
    let output = match destination {
        None => Output::Stdout,
        Some(path) if cli.file => Output::File(path),
        Some(path) if cli.folder => Output::Folder(path),
        Some(path) if cli.legacy_saving => Output::Legacy(path),
        Some(path) if archive_name(&path) => {
            if let Some(base) = path.parent().filter(|base| !base.as_os_str().is_empty()) {
                fs::create_dir_all(base)?;
            }
            Output::File(path)
        }
        Some(path) => {
            fs::create_dir_all(&path)?;
            Output::Folder(path)
        }
    };
    let mut decompiler = Decompiler::new(options)?;
    for library in cli
        .add_external
        .into_iter()
        .filter(|path| input_exists(path))
    {
        decompiler.add_library(library)?;
    }
    for source in sources {
        decompiler.add_source(source)?;
    }
    for prefix in cli.only {
        decompiler.add_whitelist(prefix);
    }
    match decompiler.save(output) {
        Err(error) if error.kind() == io::ErrorKind::Interrupted => {
            println!("Decompilation canceled");
            Ok(())
        }
        result => result,
    }
}

fn input_exists(path: &Path) -> bool {
    let exists = path.exists();
    if !exists {
        println!("warn: missing '{}', ignored", path.display());
    }
    exists
}

fn archive_name(path: &Path) -> bool {
    let name = path
        .file_name()
        .unwrap_or_else(|| OsStr::new(""))
        .to_string_lossy();
    name.contains(".zip") || name.contains(".jar")
}

fn print_plugins(command: &clap::Command) {
    let plugins = [
        (
            "VariableRenaming",
            "Allows automatic renaming of variables with a common naming scheme.",
        ),
        ("Kotlin", "Detects and decompiles Kotlin class files."),
        (
            "IdeaNotNull",
            "Decompiles code inserted by Intellij IDEA's @NotNull annotation.",
        ),
    ];
    if let Some(about) = command.get_about() {
        println!("{about}");
    }
    if let Some(credit) = command.get_after_help() {
        println!("{credit}");
    }
    println!("\nLoaded {} plugins:", plugins.len());
    for (name, description) in plugins {
        println!("{name} (loaded from native binary)\n - {description}\n");
    }
}

struct ConsoleLogger;

impl Log for ConsoleLogger {
    fn enabled(&self, metadata: &Metadata<'_>) -> bool {
        metadata.level() <= log::max_level()
    }

    fn log(&self, record: &Record<'_>) {
        if !self.enabled(record.metadata()) {
            return;
        }
        let prefix = match record.level() {
            Level::Error => "ERROR: ",
            Level::Warn => "WARN:  ",
            Level::Info => "INFO:  ",
            Level::Debug | Level::Trace => "TRACE: ",
        };
        let _ = writeln!(io::stdout().lock(), "{prefix}{}", record.args());
    }

    fn flush(&self) {}
}

fn configure_log(level: &str) {
    static LOGGER: ConsoleLogger = ConsoleLogger;
    let severity = match level.to_ascii_lowercase().as_str() {
        "trace" => LevelFilter::Trace,
        "warn" => LevelFilter::Warn,
        "error" => LevelFilter::Error,
        _ => LevelFilter::Info,
    };
    let _ = log::set_logger(&LOGGER);
    log::set_max_level(severity);
}
