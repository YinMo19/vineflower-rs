use crate::{Options, bytecode::decode, classfile::ClassFile, decompile};

const PREVIEW_BASIC: &[u8] = include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching1.class");
const PREVIEW_DEFAULT: &[u8] = include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching4.class");
const PREVIEW_REPEATED: &[u8] = include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching15.class");
const PREVIEW_NESTED: &[u8] = include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching17.class");
const PREVIEW_FALSE: &[u8] = include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching20.class");
const J21: &[u8] = include_bytes!("../../tests/smoke/java21/TestSwitchPatternMatchingJ21.class");
const J25: &[u8] = include_bytes!("../../tests/smoke/java25/TestSwitchPatternMatchingJ25.class");

#[test]
fn preview_single_pass_and_default_only_dispatch_remain_source_switches() {
    let basic = decompile(PREVIEW_BASIC, &Options::default()).unwrap().text;
    assert!(basic.contains("switch (o)") && basic.contains("case Integer i:") && basic.contains("case String s:"), "{basic}");
    let default = decompile(PREVIEW_DEFAULT, &Options::default()).unwrap().text;
    assert!(default.contains("switch (") && default.contains("default:") && default.contains("println(\"default\")"), "{default}");
    assert!(!default.contains("typeSwitch"), "{default}");
}

#[test]
fn failed_guards_resume_at_the_next_bootstrap_label() {
    let source = decompile(PREVIEW_REPEATED, &Options::default()).unwrap().text;
    assert_eq!(source.matches("case Integer ").count(), 2, "{source}");
    assert_eq!(source.matches("case Number ").count(), 2, "{source}");
    assert_eq!(source.matches(" && ").count(), 2, "{source}");
    assert_eq!(source.matches("hashCode()").count(), 1, "{source}");
    assert!(!source.contains("typeSwitch") && !source.contains("while ("), "{source}");
}

#[test]
fn preview_false_guard_retries_after_its_binding() {
    let source = decompile(PREVIEW_FALSE, &Options::default()).unwrap().text;
    assert!(source.lines().any(|line| line.contains("case Integer ") && line.contains(" && (false):")), "{source}");
    assert!(source.contains("case String s:") && source.contains("default:"), "{source}");
    assert!(!source.contains("typeSwitch"), "{source}");

    let class = ClassFile::parse(PREVIEW_FALSE).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let base = code.bytes.as_ptr() as usize - PREVIEW_FALSE.as_ptr() as usize;
    let instructions = decode(code.bytes).unwrap();
    let retry = instructions.windows(3)
        .find(|ops| ops[0].opcode == 0x04 && ops[1].opcode == 0x3e && ops[2].opcode == 0xa7)
        .unwrap();
    let mut altered = PREVIEW_FALSE.to_vec();
    altered[base + retry[0].offset as usize] = 0x05;
    assert!(decompile(&altered, &Options::default()).is_err());
}

#[test]
fn the_same_guard_protocol_uses_when_in_final_switch_syntax() {
    let mut bytes = PREVIEW_REPEATED.to_vec();
    bytes[4..8].copy_from_slice(&[0, 0, 0, 65]);
    let source = decompile(&bytes, &Options::default()).unwrap().text;
    assert_eq!(source.matches(" when ").count(), 2, "{source}");
    assert!(!source.contains(" && ") && !source.contains("typeSwitch"), "{source}");
}

#[test]
fn nested_predicate_switch_preserves_the_failed_retry_and_success_continuations() {
    let source = decompile(PREVIEW_NESTED, &Options::default()).unwrap().text;
    assert!(source.contains("case String s && (switch (s.charAt(0))"), "{source}");
    assert!(source.contains("case 'a' -> true;") && source.contains("case 'b' -> s.length() > 5;"), "{source}");
    assert!(source.contains("default -> false;"), "{source}");
    let println = source.find("println(s)").unwrap();
    assert!(println < source.find("throw new IllegalArgumentException").unwrap(), "{source}");
    assert_eq!(source.matches("charAt(0)").count(), 1, "{source}");
    assert!(!source.contains("typeSwitch") && !source.contains("while ("), "{source}");
}

#[test]
fn a_retry_that_skips_labels_is_not_a_source_guard() {
    let class = ClassFile::parse(PREVIEW_NESTED).unwrap();
    let method = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "test4").unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let base = code.bytes.as_ptr() as usize - PREVIEW_NESTED.as_ptr() as usize;
    let instructions = decode(code.bytes).unwrap();
    let retry = instructions.windows(3).find(|ops| ops[0].opcode == 0x04 && ops[1].opcode == 0x3d && ops[2].opcode == 0xa7).unwrap();
    let mut altered = PREVIEW_NESTED.to_vec();
    altered[base + retry[0].offset as usize] = 0x05;
    assert!(decompile(&altered, &Options::default()).is_err());
}

#[test]
fn stable_pattern_values_keep_incoming_call_operands_and_combined_default() {
    for bytes in [J21, J25] {
        let options = Options { method_to_decompile: "test1(Ljava/lang/Object;)V".into(), ..Options::default() };
        let source = decompile(bytes, &options).unwrap().text;
        assert!(source.contains("println(switch (o)"), "{source}");
        assert!(source.contains("case Integer i ->") && source.contains("case null, default -> \"null\";"), "{source}");
    }
    let source = decompile(J21, &Options::default()).unwrap().text;
    assert!(source.contains("return switch (o.get())") && source.contains("return switch (this.test4)"), "{source}");
    assert!(source.contains("case String s -> s;") && source.contains("default:"), "{source}");
}
