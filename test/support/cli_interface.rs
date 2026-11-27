use std::{fs, process::Command};

use super::upstream_reference::run;

const CLI: &str = env!("CARGO_BIN_EXE_vineflower-rs");

fn stdout(command: &mut Command) -> String {
    let output = run(command);
    assert!(
        output.stderr.is_empty(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn help_lists_commands_and_decompiler_preferences() {
    let help = stdout(Command::new(CLI).arg("--help"));
    for item in [
        "completions",
        "--folder",
        "--add-external",
        "--thread-count",
        "--bytecode-source-mapping",
        "--kt-enable",
        "--variable-renaming",
    ] {
        assert!(help.contains(item), "missing {item} in --help");
    }
    let legacy = stdout(Command::new(CLI).arg("-help"));
    assert!(legacy.contains("Usage:") && legacy.contains("--folder"));
}

#[test]
fn root_help_places_the_credit_and_decompilation_examples_before_commands() {
    for args in [&[][..], &["-h"], &["--help"]] {
        let help = stdout(Command::new(CLI).args(args));
        assert_eq!(help.lines().nth(1), Some("By YinMo19."), "{args:?}");
        let (_, usage) = help.split_once("Usage:").expect("missing usage");
        let (intro, _) = usage.split_once("Commands:").expect("missing commands");
        let (_, examples) = intro
            .split_once("Examples:")
            .expect("missing examples after usage");
        for command in [
            "vineflower-rs app.jar out/",
            "vineflower-rs Example.class",
            "vineflower-rs --file app.jar sources.zip",
        ] {
            assert!(
                examples.lines().any(|line| line.trim() == command),
                "{command}"
            );
        }
    }

    for (args, marker) in [
        (&["completions", "--help"][..], "powershell"),
        (&["--list-plugins"][..], "Kotlin"),
    ] {
        let output = stdout(Command::new(CLI).args(args));
        assert!(output.contains(marker), "{args:?}");
        assert!(!output.contains("Examples:"), "{args:?}");
    }
}

#[test]
fn completions_register_the_cli_in_each_shell() {
    for (shell, registration) in [
        ("bash", "complete -F"),
        ("zsh", "#compdef vineflower-rs"),
        ("fish", "complete -c vineflower-rs"),
        ("powershell", "Register-ArgumentCompleter"),
        ("elvish", "edit:completion:arg-completer[vineflower-rs]"),
    ] {
        let script = stdout(Command::new(CLI).args(["completions", shell]));
        for item in [registration, "vineflower-rs", "thread-count"] {
            assert!(script.contains(item), "missing {item} in {shell} script");
        }
        assert!(
            !script.contains("__unit_test_mode__"),
            "{shell} exposes a test-only option"
        );
        assert!(!script.lines().any(|line| line.starts_with("INFO:")));
    }
}

#[test]
fn bash_completes_shell_names_after_the_subcommand() {
    if !Command::new("bash")
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
    {
        eprintln!("Skipping the interactive completion check because Bash is unavailable");
        return;
    }
    let scratch = tempfile::tempdir().unwrap();
    let script = stdout(Command::new(CLI).args(["completions", "bash"]));
    fs::write(scratch.path().join("completion.bash"), script).unwrap();
    let candidates = stdout(
        Command::new("bash")
            .current_dir(scratch.path())
            .env_remove("BASH_ENV")
            .args([
                "--noprofile",
                "--norc",
                "-ec",
                r#"
                source ./completion.bash
                registration=$(complete -p vineflower-rs)
                handler=${registration#* -F }
                handler=${handler%% *}
                COMP_WORDS=(vineflower-rs completions pow)
                COMP_CWORD=2
                "$handler" vineflower-rs pow completions
                printf '%s\n' "${COMPREPLY[@]}"
            "#,
            ]),
    );
    assert!(
        candidates.lines().any(|name| name == "powershell"),
        "{candidates}"
    );
}

#[test]
fn last_boolean_preference_controls_default_constructor_output() {
    let show = "--no-hide-default-constructor";
    let hide = "--hide-default-constructor";
    for (flags, constructor_visible) in [
        (&[show, hide][..], false),
        (&[hide, show][..], true),
        (&["--hide-default-constructor=FALSE"][..], true),
    ] {
        let source = stdout(
            Command::new(CLI)
                .args(["--include-runtime=0", "--silent"])
                .args(flags)
                .arg("test/smoke/java8/TestSimpleWhile.class"),
        );
        assert!(source.contains("class TestSimpleWhile"));
        assert_eq!(
            source.contains("public TestSimpleWhile()"),
            constructor_visible,
            "{flags:?}"
        );
    }
}

#[test]
fn positional_paths_work_with_modern_options_and_legacy_config() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let class = "TestSimpleWhile.class";
    fs::write(
        root.join(class),
        include_bytes!("../smoke/java8/TestSimpleWhile.class"),
    )
    .unwrap();
    fs::write(root.join("args.cfg"), "--indent-string=    \n-thr=1\n").unwrap();

    let mut cli = Command::new(CLI);
    cli.current_dir(root)
        .args(["--include-runtime=0", "--silent"]);
    let console = stdout(cli.arg(class));
    assert!(console.contains("class TestSimpleWhile"));

    for (options, destination) in [
        (&["-cfg", "args.cfg"][..], "from-config"),
        (
            &["--indent-string=    ", "--thread-count", "1", "--"][..],
            "--help",
        ),
    ] {
        let mut cli = Command::new(CLI);
        let log = stdout(
            cli.current_dir(root)
                .args(["--include-runtime=0", "--log-level=ERROR"])
                .args(options)
                .args([class, destination]),
        );
        assert!(log.is_empty(), "{log}");
        let source =
            fs::read_to_string(root.join(destination).join("TestSimpleWhile.java")).unwrap();
        assert!(
            source
                .lines()
                .any(|line| line.starts_with("    public void test("))
        );
    }
}
