//! Register the host or a configured JDK without starting a JVM.

use std::{
    env, fs, io,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::engine::{Options, context_source::RuntimeImage};
use crate::structs::StructContext;

pub(super) fn register(context: &mut StructContext, options: &Options) -> io::Result<()> {
    let host = host_home();
    context.set_bootstrap_java_home(host.clone());
    if options.include_classpath {
        if let Some(classpath) = env::var_os("CLASSPATH") {
            let mut seen = std::collections::HashSet::new();
            for root in env::split_paths(&classpath).filter(|path| path.is_file()) {
                let extension = root.extension().and_then(|extension| extension.to_str());
                if matches!(extension, Some("class" | "jar"))
                    && seen.insert(fs::canonicalize(&root)?)
                {
                    context.add_file(&root, false)?;
                }
            }
        }
        return add_host_runtime(context, host.as_deref());
    }

    let runtime = options.include_runtime.as_str();
    if runtime.is_empty() || runtime == "0" {
        return Ok(());
    }
    if runtime.eq_ignore_ascii_case("current") || runtime == "1" {
        return add_host_runtime(context, host.as_deref());
    }

    match add_runtime(context, Path::new(runtime)) {
        Ok(true) => {}
        Ok(false) => log::error!("Unable to detect a java runtime at {runtime}"),
        Err(error) => log::error!("Failed to open java runtime at {runtime}: {error}"),
    }
    Ok(())
}

fn add_host_runtime(context: &mut StructContext, home: Option<&Path>) -> io::Result<()> {
    let Some(home) = home else {
        log::warn!("Could not locate the current Java runtime");
        return Ok(());
    };
    match add_runtime(context, home) {
        Ok(true) => Ok(()),
        Ok(false) => {
            log::warn!("Could not detect a Java runtime at {}", home.display());
            Ok(())
        }
        Err(error) => {
            log::error!("Failed to open current Java runtime for inspection: {error}");
            Ok(())
        }
    }
}

fn add_runtime(context: &mut StructContext, home: &Path) -> io::Result<bool> {
    if home.join("lib/modules").is_file() {
        context.try_add_space(Arc::new(RuntimeImage::open(home)?), false)?;
        return Ok(true);
    }
    let mut added = false;
    for library in ["jre/lib", "lib"] {
        let directory = home.join(library);
        match fs::read_dir(directory) {
            Ok(entries) => {
                for entry in entries {
                    let path = entry?.path();
                    if path.is_file()
                        && path.extension().is_some_and(|extension| extension == "jar")
                    {
                        context.add_file(&path, false)?;
                        added = true;
                    }
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(added)
}

fn host_home() -> Option<PathBuf> {
    env::var_os("JAVA_HOME")
        .filter(|home| !home.is_empty())
        .map(PathBuf::from)
        .filter(|home| has_runtime(home))
        .or_else(|| {
            let paths = env::var_os("PATH")?;
            env::split_paths(&paths).find_map(|path| {
                let launcher = path.join(if cfg!(windows) { "java.exe" } else { "java" });
                let real = fs::canonicalize(launcher).ok()?;
                let home = real.parent()?.parent()?;
                has_runtime(home).then(|| home.to_owned())
            })
        })
        .or_else(platform_home)
}

fn has_runtime(home: &Path) -> bool {
    ["lib/modules", "jre/lib/rt.jar", "lib/rt.jar"]
        .iter()
        .any(|name| home.join(name).is_file())
}

fn platform_home() -> Option<PathBuf> {
    #[cfg(target_os = "macos")]
    {
        // The system /usr/bin/java is a launcher shim, not a JDK binary.
        let found = std::process::Command::new("/usr/libexec/java_home")
            .output()
            .ok()?;
        if found.status.success() {
            let home = PathBuf::from(std::str::from_utf8(&found.stdout).ok()?.trim_end());
            if has_runtime(&home) {
                return Some(home);
            }
        }
    }
    None
}
