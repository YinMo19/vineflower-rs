//! Command-line front end for the native Java pipeline.

use std::{
    env,
    ffi::{OsStr, OsString},
    fs, io,
    io::Write,
    path::{Path, PathBuf},
    process::ExitCode,
};

use log::{Level, LevelFilter, Log, Metadata, Record};
use vineflower_rs::engine::{
    Options,
    driver::{Decompiler, Output},
};
use vineflower_rs::util::java_str;

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
    let Some(args) = expand_config(arguments)? else {
        return Ok(());
    };
    if args.is_empty()
        || args
            .iter()
            .any(|arg| matches!(arg.to_str(), Some("-h" | "--help" | "-help")))
    {
        print_help();
        return Ok(());
    }
    if args.iter().any(|arg| arg == "--list-plugins") {
        print_plugins();
        return Ok(());
    }
    let Some(command) = parse(args)? else {
        return Ok(());
    };
    configure_log(&command.options.log_level);
    let mut decompiler = Decompiler::new(command.options)?;
    for library in command.libraries {
        decompiler.add_library(library)?;
    }
    for source in command.sources {
        decompiler.add_source(source)?;
    }
    for prefix in command.whitelist {
        decompiler.add_whitelist(prefix);
    }
    match decompiler.save(command.output) {
        Err(error) if error.kind() == io::ErrorKind::Interrupted => {
            println!("Decompilation canceled");
            Ok(())
        }
        result => result,
    }
}

fn expand_config(arguments: Vec<OsString>) -> io::Result<Option<Vec<OsString>>> {
    let mut result = Vec::new();
    let mut args = arguments.into_iter();
    while let Some(arg) = args.next() {
        let Some(text) = arg.to_str().filter(|text| text.starts_with("-cfg")) else {
            result.push(arg);
            continue;
        };
        let path = if let Some(path) = text.strip_prefix("-cfg=") {
            PathBuf::from(path)
        } else if let Some(path) = args.next() {
            PathBuf::from(path)
        } else {
            println!("Must specify a file when using -cfg argument.");
            return Ok(None);
        };
        if !path.exists() {
            println!("error: missing config '{}'", path.display());
            return Ok(None);
        }
        let contents = fs::read_to_string(&path).map_err(|error| {
            println!("error: Failed to read config file '{}'", path.display());
            error
        })?;
        result.extend(contents.lines().map(OsString::from));
    }
    Ok(Some(result))
}

struct Command {
    options: Options,
    sources: Vec<PathBuf>,
    libraries: Vec<PathBuf>,
    whitelist: Vec<String>,
    output: Output,
}

enum SaveType {
    File,
    Folder,
    Legacy,
}

fn parse(args: Vec<OsString>) -> io::Result<Option<Command>> {
    let mut options = Options::default();
    options.idea_notnull = true;
    options.decompile_kotlin = true;
    let mut sources = Vec::new();
    let mut libraries = Vec::new();
    let mut whitelist = Vec::new();
    let mut user_save_type = None;
    let mut reading_options = true;
    let mut last_path = None;
    let mut thread_count = None;
    for arg in &args {
        let text = arg.to_str();
        if let Some(save_type) = match text {
            Some("--file") => Some(SaveType::File),
            Some("--folder") => Some(SaveType::Folder),
            Some("--legacy-saving") => Some(SaveType::Legacy),
            _ => None,
        } {
            if user_save_type.replace(save_type).is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "Multiple save types specified",
                ));
            }
            continue;
        }
        if reading_options
            && let Some(arg) = text
            && arg.starts_with('-')
            && arg.encode_utf16().count() > 5
            && let Some((name, value)) = parse_option(arg)
        {
            if matches!(name, "thread-count" | "thr") {
                thread_count = Some(value);
            } else {
                options.set(name, value);
            }
            continue;
        }

        reading_options = false;
        match text {
            Some("-s" | "--silent") => options.log_level = "error".to_owned(),
            Some(text) if text.starts_with("-e=") || text.starts_with("--add-external=") => {
                for path in java_str::split(text.split_once('=').unwrap().1, ",") {
                    add_path(&mut libraries, PathBuf::from(path));
                }
            }
            Some(text) if text.starts_with("-only=") || text.starts_with("--only=") => {
                whitelist.extend(
                    java_str::split(text.split_once('=').unwrap().1, ",")
                        .into_iter()
                        .map(str::to_owned),
                );
            }
            _ => {
                if let Some(previous) = last_path.replace(PathBuf::from(arg)) {
                    add_path(&mut sources, previous);
                }
            }
        }
    }
    if sources.is_empty()
        && let Some(last) = last_path.take()
    {
        add_path(&mut sources, last);
    }
    if sources.is_empty() {
        println!("error: no sources given");
        return Ok(None);
    }
    if let Some(value) = thread_count {
        // ContextUnit reads the final setting with Integer.parseInt.
        options.thread_count = value.parse().map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("invalid thread-count '{value}'"),
            )
        })?;
    }
    let output = match last_path {
        None => Output::Stdout,
        Some(path) => match user_save_type {
            Some(SaveType::File) => Output::File(path),
            Some(SaveType::Folder) => Output::Folder(path),
            Some(SaveType::Legacy) => Output::Legacy(path),
            None if archive_name(&path) => {
                if let Some(base) = path.parent().filter(|base| !base.as_os_str().is_empty()) {
                    fs::create_dir_all(base)?;
                }
                Output::File(path)
            }
            None => {
                fs::create_dir_all(&path)?;
                Output::Folder(path)
            }
        },
    };
    Ok(Some(Command {
        options,
        sources,
        libraries,
        whitelist,
        output,
    }))
}

fn parse_option(arg: &str) -> Option<(&str, &str)> {
    const CUSTOM: &[&str] = &[
        "-e=",
        "--add-external=",
        "-only=",
        "--only=",
        "-s",
        "--silent",
    ];
    if CUSTOM.iter().any(|prefix| arg.starts_with(prefix)) {
        return None;
    }

    let (name, value) = if let Some(long) = arg.strip_prefix("--") {
        long.split_once('=')
            .or_else(|| long.strip_prefix("no-").map(|name| (name, "0")))
            .unwrap_or((long, "1"))
    } else {
        (arg.get(1..4).unwrap_or(""), arg.get(5..).unwrap_or(""))
    };
    let value = if value.eq_ignore_ascii_case("true") {
        "1"
    } else if value.eq_ignore_ascii_case("false") {
        "0"
    } else {
        value
    };
    Some((name, value))
}

fn add_path(paths: &mut Vec<PathBuf>, path: PathBuf) {
    if path.exists() {
        paths.push(path);
    } else {
        println!("warn: missing '{}', ignored", path.display());
    }
}

fn archive_name(path: &Path) -> bool {
    let name = path
        .file_name()
        .unwrap_or_else(|| OsStr::new(""))
        .to_string_lossy();
    name.contains(".zip") || name.contains(".jar")
}

const BANNER: &str = "=== Vineflower Decompiler 1.12.0 (native Rust) ===";

fn print_plugins() {
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
    println!("{BANNER}\n\nLoaded {} plugins:", plugins.len());
    for (name, description) in plugins {
        println!("{name} (loaded from native binary)\n - {description}\n");
    }
}

fn print_help() {
    println!(
        "{BANNER}\n\n\
        Usage: vineflower-rs [options] <source>... [destination]\n\n\
        Supply class files, directories or archives as sources. Omit the destination for stdout.\n\
        --folder           Unpack classes and resources into a directory\n\
        --file             Write output to a ZIP or JAR\n\
        --legacy-saving    Keep input archives under their original names\n\
        --add-external=PATH[,PATH]  Add libraries for lookups\n\
        --only=PREFIX[,PREFIX]      Select classes by internal-name prefix\n\
        --thread-count=N, -thr=N    Worker threads (default: all available processors)\n\
        --list-plugins     Display loaded plugin information\n\
        -cfg PATH          Read one command-line argument per line\n\
        -s, --silent       Suppress informational logs"
    );
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
