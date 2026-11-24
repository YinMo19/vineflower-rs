use vineflower_rs::{
    Options,
    bytecode::{Operand, decode},
    classfile::{ClassFile, Constant, find_attribute},
    decompile,
};

// Unmodified classes compiled from the corresponding upstream java21preview sources.
const RAW: &[u8] = include_bytes!("fixtures/java_templates/TestRawProcessor.class");
const FMT: &[u8] = include_bytes!("fixtures/java_templates/TestFmtProcessor.class");
const CUSTOM: &[u8] = include_bytes!("fixtures/java_templates/TestCustomProcessor.class");

#[test]
fn reconstructs_java21_preview_processors() {
    for (bytes, expected) in [
        (RAW, r#"StringTemplate.RAW."Text: \{s} \{i} \{o}""#),
        (FMT, r#"FormatProcessor.FMT."Text: %s\{s} %4d\{i} %.2f\{d}""#),
        (CUSTOM, r#"processor.process(StringTemplate.RAW."Text: \{s} \{i} \{d}")"#),
    ] {
        let source = decompile(bytes, &Options::default()).unwrap().text;
        assert!(source.contains(expected), "missing {expected:?}:\n{source}");
        assert!(!source.contains("TemplateRuntime"), "{source}");
    }
}

fn with_escaped_fragment() -> Vec<u8> {
    // Replace just the first fragment's CONSTANT_Utf8 payload. Leave the
    // compiler's instruction stream, bootstrap, and other fragments intact.
    let original = b"\x01\x00\x06Text: ";
    let start = RAW.windows(original.len()).position(|window| window == original).unwrap();
    let new = format!("literal \\{{x}} \"\"\" é 😀 \t\n {}", "\\".repeat(3));
    let encoded = cesu8::to_java_cesu8(&new);
    let mut class = RAW.to_vec();
    class.splice(start + 1..start + original.len(),
        (encoded.len() as u16).to_be_bytes().into_iter().chain(encoded.iter().copied()));
    class
}

#[test]
fn escapes_delimiters_backslashes_controls_and_utf16_in_template_fragments() {
    let class = with_escaped_fragment();
    let mut options = Options::default();
    for (ascii, accent) in [(false, "é"), (true, r"\u00e9")] {
        options.ascii_strings = ascii;
        let source = decompile(&class, &options).unwrap().text;
        let expected = format!(
            r#"StringTemplate.RAW."literal \\{{x}} \"\"\" {accent} \ud83d\ude00 \t\n {}\{{s}} \{{i}} \{{o}}""#,
            r"\\".repeat(3),
        );
        assert!(source.contains(&expected), "missing {expected:?}:\n{source}");
    }
}

fn assert_rejected(bytes: &[u8], reason: &str) {
    let error = decompile(bytes, &Options::default()).unwrap_err().to_string();
    assert!(error.contains(reason), "{error}");
}

#[test]
fn declines_unrecognized_template_bootstraps_and_invalid_fragments() {
    let mut wrong_version = RAW.to_vec();
    wrong_version[4..6].copy_from_slice(&0u16.to_be_bytes());
    assert_rejected(&wrong_version, "string templates require Java 21 preview");

    let name = b"newStringTemplate";
    let pos = RAW.windows(name.len()).position(|window| window == name).unwrap();
    let mut unknown = RAW.to_vec();
    unknown[pos..pos + 3].copy_from_slice(b"bad");
    assert_rejected(&unknown, "unrecognized string template bootstrap or descriptor");

    let class = ClassFile::parse(RAW).unwrap();
    let data = find_attribute(&class.attributes, &class.pool, "BootstrapMethods").unwrap().unwrap();
    let pos = data.as_ptr() as usize - RAW.as_ptr() as usize;
    let mut invalid_fragment = RAW.to_vec();
    // Use the bootstrap method handle in place of a fragment String.
    invalid_fragment[pos + 6..pos + 8].copy_from_slice(&data[2..4]);
    assert_rejected(&invalid_fragment, "string template fragment is not a String");
}

#[test]
fn declines_linked_formatting_when_the_evaluated_processor_is_not_fmt() {
    let class = ClassFile::parse(FMT).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let op = decode(code.bytes).unwrap().into_iter().find(|op| {
        matches!(op.operand, Operand::Constant(index) if op.opcode == 0xb2
            && class.pool.member_ref(index).unwrap().1 == "FMT")
    }).unwrap();
    let start = code.bytes.as_ptr() as usize - FMT.as_ptr() as usize + op.offset as usize;
    let mut invalid = FMT.to_vec();
    // Retain stack shape and bootstrap handle; bypass the actual getstatic.
    invalid[start..start + 3].copy_from_slice(&[0x01, 0, 0]);
    assert_rejected(&invalid, "linked string template processor is not a direct FMT field read");
}

fn raw_fragments(bytes: &[u8]) -> Vec<Vec<u16>> {
    let class = ClassFile::parse(bytes).unwrap();
    class.bootstrap_methods().unwrap().into_iter().find_map(|bootstrap| {
        let Constant::MethodHandle { reference_index, .. } = *class.pool.get(bootstrap.method_ref).unwrap() else {
            panic!("missing bootstrap method handle");
        };
        let (_, name, _) = class.pool.member_ref(reference_index).unwrap();
        (name == "newStringTemplate").then(|| bootstrap.arguments.into_iter().map(|index| {
            let Constant::String(utf8) = *class.pool.get(index).unwrap() else {
                panic!("expected a string fragment");
            };
            class.pool.utf16(utf8).unwrap().into_owned()
        }).collect())
    }).expect("newStringTemplate bootstrap")
}

#[test]
#[ignore = "requires a Java 21 JDK at VINEFLOWER_JDK_21"]
fn recompiles_processor_syntax_and_preserves_fragment_payloads() {
    let jdk = std::env::var_os("VINEFLOWER_JDK_21").expect("set VINEFLOWER_JDK_21");
    let javac = std::path::PathBuf::from(jdk).join("bin").join(if cfg!(windows) { "javac.exe" } else { "javac" });
    let temp = tempfile::tempdir().unwrap();
    let edge = with_escaped_fragment();
    let sources = [("TestRawProcessor", edge.as_slice()), ("TestFmtProcessor", FMT), ("TestCustomProcessor", CUSTOM)]
        .map(|(name, bytes)| {
            let file = temp.path().join(format!("{name}.java"));
            std::fs::write(&file, decompile(bytes, &Options::default()).unwrap().text).unwrap();
            file
        });
    let output = std::process::Command::new(javac)
        .args(["--enable-preview", "--release", "21", "-encoding", "UTF-8", "-d"])
        .arg(temp.path()).args(sources).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let recompiled = std::fs::read(temp.path().join("pkg/TestRawProcessor.class")).unwrap();
    assert_eq!(raw_fragments(&recompiled), raw_fragments(&edge));
}
