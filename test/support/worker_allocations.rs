use std::{fs, io::Write, process::Command};

use super::upstream_reference::{jdk_tool, run, upstream_jar};
use super::{compile_java17, directory, replace_utf8_entry, run_main};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn worker_allocations_observe_lambdas_published_by_an_earlier_unit() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let classes = root.join("classes");
    let source = root.join("Verify.java");
    fs::write(
        &source,
        r#"
class LambdaOwner {
    static Runnable make() { return () -> System.out.println("lambda"); }
}
class AllocationUser {
    static Object make() { return new OriginalTarget(); }
}
class OriginalTarget {
    @Override public String toString() { return "real class"; }
}
class OwnerCompanion { static int value() { return 1; } }
class UserCompanion { static int value() { return 3; } }
public class Verify {
    public static void main(String[] args) {
        LambdaOwner.make().run();
        System.out.println(AllocationUser.make());
        System.out.println(OwnerCompanion.value() + UserCompanion.value());
    }
}
"#,
    )
    .unwrap();
    compile_java17(&[&source], &classes);
    let expected_execution = b"lambda\nreal class\n4\n";
    assert_eq!(run_main(&classes, "Verify"), expected_execution);

    let details = run(Command::new(jdk_tool("javap"))
        .arg("-v")
        .arg(classes.join("LambdaOwner.class")))
    .stdout;
    let details = std::str::from_utf8(&details).unwrap();
    let (_, indices) = details
        .lines()
        .find_map(|line| line.split_once("= InvokeDynamic"))
        .expect("the lambda needs an invokedynamic constant");
    let (bootstrap, name_and_type) = indices.trim().split_once(":#").unwrap();
    let bootstrap: u16 = bootstrap.strip_prefix('#').unwrap().parse().unwrap();
    let name_and_type: u16 = name_and_type.split_once(' ').unwrap().0.parse().unwrap();
    let colliding_name = format!("LambdaOwner##Lambda_{bootstrap}_{name_and_type}");
    let colliding_class = format!("{colliding_name}.class");

    let allocation_path = classes.join("AllocationUser.class");
    let mut allocation = fs::read(&allocation_path).unwrap();
    replace_utf8_entry(&mut allocation, "OriginalTarget", &colliding_name);
    fs::write(allocation_path, allocation).unwrap();
    let target_path = classes.join("OriginalTarget.class");
    let mut target = fs::read(&target_path).unwrap();
    replace_utf8_entry(&mut target, "OriginalTarget", &colliding_name);
    replace_utf8_entry(
        &mut target,
        "LOriginalTarget;",
        &format!("L{colliding_name};"),
    );
    fs::remove_file(target_path).unwrap();
    fs::write(classes.join(&colliding_class), target).unwrap();
    assert_eq!(run_main(&classes, "Verify"), expected_execution);

    let jar = |name, entries: &[&str]| {
        let path = root.join(name);
        let mut jar = zip::ZipWriter::new(fs::File::create(&path).unwrap());
        for &entry in entries {
            jar.start_file(entry, zip::write::SimpleFileOptions::default())
                .unwrap();
            jar.write_all(&fs::read(classes.join(entry)).unwrap())
                .unwrap();
        }
        jar.finish().unwrap();
        path
    };
    // Both units need a second root so the first unit takes the snapshot and
    // the allocation in the second unit is prepared on a worker.
    let owner = jar("owner.jar", &["LambdaOwner.class", "OwnerCompanion.class"]);
    let user = jar("user.jar", &["AllocationUser.class", "UserCompanion.class"]);
    let library = jar("library.jar", &[&colliding_class]);
    let library = format!("-e={}", library.display());
    let options = [
        "--folder",
        "--include-runtime=1",
        "--dump-exception-on-error=0",
        "--log-level=WARN",
    ];
    for (layout, inputs, published) in [
        ("owner-first", [&owner, &user], true),
        ("user-first", [&user, &owner], false),
    ] {
        let expected = root.join(format!("{layout}-upstream"));
        fs::create_dir(&expected).unwrap();
        run(Command::new(jdk_tool("java"))
            .arg("-jar")
            .arg(upstream_jar())
            .arg("--thread-count=1")
            .args(options)
            .arg(&library)
            .args(inputs)
            .arg(&expected));
        let source = fs::read_to_string(expected.join("AllocationUser.java")).unwrap();
        assert_eq!(
            source.contains("Couldn't be decompiled"),
            published,
            "{source}"
        );
        assert_eq!(
            source.contains(&format!("return new {colliding_name}();")),
            !published,
            "{source}"
        );
        let expected = directory(&expected);
        for count in [1, 2, 0] {
            let actual = root.join(format!("{layout}-native-{count}"));
            fs::create_dir(&actual).unwrap();
            let result = run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
                .arg(format!("--thread-count={count}"))
                .args(options)
                .arg(&library)
                .args(inputs)
                .arg(&actual));
            let log = String::from_utf8_lossy(&result.stdout);
            assert!(
                !log.contains("Could not decompile AllocationUser.make"),
                "{layout}, thread-count={count}: {log}"
            );
            assert_eq!(
                directory(&actual),
                expected,
                "{layout}, thread-count={count}"
            );
        }
    }
}
