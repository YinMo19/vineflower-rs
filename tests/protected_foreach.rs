use std::{env, fs, process::Command};

use vineflower_rs::{Options, decompile};

const ORIGINAL: &[u8] = include_bytes!("smoke/java8/TestSwitchInTry.class");

#[test]
fn protected_string_switch_foreach_break() {
    let source = decompile(ORIGINAL, &Options::default()).unwrap().text;
    let foreach = source.find("for (String ").expect(&source);
    let (_, body) = source[foreach..].split_once("try {").expect(&source);
    let (protected, tail) = body.split_once("} catch (Exception ").expect(&source);
    let (_, catch) = tail.split_once(") {").expect(&source);
    assert!(catch.split_once('}').expect(&source).0.trim().is_empty(), "{source}");
    let switch = protected
        .lines()
        .find(|line| line.trim_start().starts_with("switch ("))
        .expect(&source);
    let depth = switch.len() - switch.trim_start().len();
    assert!(protected.contains("case \"a\":"), "{source}");
    assert!(
        protected.lines().any(|line| {
            line.trim_start() == "break;" && line.len() - line.trim_start().len() == depth
        }),
        "{source}"
    );
    assert!(tail.contains("Arrays.asList("), "{source}");
    assert_eq!(source.matches("Arrays.asList(").count(), 1, "{source}");
    assert!(!source.contains("asList((Object[])"), "{source}");
}

#[test]
#[ignore = "requires VINEFLOWER_JDK_8 to recompile and run the original Java 8 fixture"]
fn recompiled_protected_switch_preserves_break_and_catch() {
    let jdk = std::path::PathBuf::from(env::var_os("VINEFLOWER_JDK_8").expect("set VINEFLOWER_JDK_8"));
    let javac = jdk.join("bin/javac");
    let java = jdk.join("bin/java");
    let source = decompile(ORIGINAL, &Options::default()).unwrap().text;

    let scratch = tempfile::tempdir().unwrap();
    let candidate = scratch.path().join("candidate");
    let runner_classes = scratch.path().join("runner");
    fs::create_dir(&candidate).unwrap();
    let class_root = scratch.path().join("original");
    fs::create_dir_all(class_root.join("pkg")).unwrap();
    fs::write(class_root.join("pkg/TestSwitchInTry.class"), ORIGINAL).unwrap();
    fs::create_dir(&runner_classes).unwrap();
    let candidate_source = scratch.path().join("TestSwitchInTry.java");
    fs::write(&candidate_source, source).unwrap();
    run(Command::new(&javac)
        .arg("-d")
        .arg(&candidate)
        .arg(&candidate_source));

    let runner = scratch.path().join("Runner.java");
    fs::write(
        &runner,
        r#"
import java.util.Arrays;
import java.util.List;
import pkg.TestSwitchInTry;

public class Runner {
  public static void main(String[] args) {
    String[][] inputs = { {null, "a"}, {"x", "a"}, {}, {null, null} };
    String[] expected = { "a", "", "", "" };
    for (int i = 0; i < inputs.length; i++) {
      List<String> actual = TestSwitchInTry.method(inputs[i]);
      if (!actual.equals(Arrays.asList(expected[i]))) {
        throw new AssertionError(Arrays.toString(inputs[i]) + " yielded " + actual);
      }
    }
  }
}
"#,
    )
    .unwrap();
    run(Command::new(&javac)
        .arg("-cp")
        .arg(&class_root)
        .arg("-d")
        .arg(&runner_classes)
        .arg(&runner));
    for classes in [&class_root, &candidate] {
        run(Command::new(&java)
            .arg("-cp")
            .arg(env::join_paths([&runner_classes, classes]).unwrap())
            .arg("Runner"));
    }
}

fn run(command: &mut Command) {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("{command:?}: {error}"));
    assert!(
        output.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
