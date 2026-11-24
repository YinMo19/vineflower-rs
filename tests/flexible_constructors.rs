use vineflower_rs::{Options, bytecode::{Operand, decode}, classfile::{ClassFile, Code}, decompile};

const CLASS: &[u8] = include_bytes!("fixtures/flexible_constructors/FlexibleConstructor.class");
const ENUM: &[u8] = include_bytes!("fixtures/flexible_constructors/FlexibleConstructorEnum.class");
const RECORD: &[u8] = include_bytes!("fixtures/flexible_constructors/FlexibleConstructorRecord.class");
const PREVIEW_SINGLE: &[u8] = include_bytes!("smoke/java17preview/TestSwitchPatternMatchingConstructor2.class");
const PREVIEW_GUARDED: [&[u8]; 3] = [
    include_bytes!("smoke/java17preview/TestSwitchPatternMatchingConstructor1.class"),
    include_bytes!("smoke/java17preview/TestSwitchPatternMatchingConstructor1$Shape.class"),
    include_bytes!("smoke/java17preview/TestSwitchPatternMatchingConstructor1$Triangle.class"),
];

fn assert_order(mut source: &str, needles: &[&str]) {
    let original = source;
    for &needle in needles {
        let (_, rest) = source.split_once(needle).unwrap_or_else(|| {
            panic!("missing {needle:?} in the expected order:\n{original}")
        });
        source = rest;
    }
}

#[test]
fn keeps_constructor_prologue_epilogue_and_local_lifetimes() {
    let source = decompile(CLASS, &Options::default()).unwrap().text;
    assert_eq!(source.matches("super();").count(), 1, "{source}");
    assert!(source.lines().any(|line| line.trim() == "final int value;"), "{source}");
    assert_order(&source, &[
        "FlexibleConstructor(int input)", "int prepared = step(input);",
        "throw new IllegalArgumentException(\"negative\");", "this.value = prepared;",
        "step(2);", "new String(\"constructed\");", "super();", "step(9);",
        "this.audit = step(prepared);", "FlexibleConstructor()", "int prepared = step(4);",
        "this.audit = step(5);", "this(prepared);", "FlexibleConstructor(boolean alternate)",
        "step(6);", "step(7);", "this.audit = ", "this(", "step(8)",
    ]);
    for argument in [6, 7, 8] {
        assert_eq!(source.matches(&format!("step({argument})")).count(), 1, "{source}");
    }
}

#[test]
fn enum_and_record_prologues_can_delegate_to_another_constructor() {
    let enumeration = decompile(ENUM, &Options::default()).unwrap().text;
    assert_order(&enumeration, &["FlexibleConstructorEnum()", "int prepared = twice(3);", "this(prepared);"]);
    assert!(!enumeration.contains("super("), "{enumeration}");
    let record = decompile(RECORD, &Options::default()).unwrap().text;
    assert_order(&record, &["FlexibleConstructorRecord()", "int prepared = Math.abs(-4);", "this(prepared);"]);
    assert!(!record.contains("super("), "{record}");
}

fn constructor<'a>(class: &ClassFile<'a>, descriptor: &str) -> Code<'a> {
    class.methods.iter().find(|method| {
        class.pool.utf8(method.name_index).unwrap() == "<init>"
            && class.pool.utf8(method.descriptor_index).unwrap() == descriptor
    }).unwrap().code(&class.pool).unwrap().unwrap()
}

fn store_site(class: &ClassFile<'_>, descriptor: &str, name: &str) -> (usize, u16) {
    let code = constructor(class, descriptor);
    let start = code.bytes.as_ptr() as usize - CLASS.as_ptr() as usize;
    decode(code.bytes).unwrap().into_iter().find_map(|op| {
        let (0xb5, Operand::Constant(index)) = (op.opcode, op.operand) else { return None };
        (class.pool.member_ref(index).unwrap().1 == name).then_some((start + op.offset as usize, index))
    }).unwrap()
}

#[test]
fn rejects_reads_and_casts_of_the_uninitialized_receiver() {
    let class = ClassFile::parse(CLASS).unwrap();
    let (store, field) = store_site(&class, "(I)V", "value");
    assert_eq!(&CLASS[store - 2..store], &[0x2a, 0x1c]); // aload_0; iload_2
    for (operation, operand) in [(0xb4, field), (0xc0, class.this_class)] {
        let [high, low] = operand.to_be_bytes();
        let mut invalid = CLASS.to_vec();
        // Keep Code length, frames and control-flow offsets intact.
        invalid[store - 1..store + 3].copy_from_slice(&[operation, high, low, 0x57]);
        let error = decompile(&invalid, &Options::default()).unwrap_err().to_string();
        assert!(error.contains("uninitialized receiver used before invokespecial"), "{error}");
    }
}

#[test]
fn refuses_to_delegate_after_writing_a_blank_final_field() {
    let class = ClassFile::parse(CLASS).unwrap();
    let (_, final_field) = store_site(&class, "(I)V", "value");
    let (nonfinal_store, _) = store_site(&class, "()V", "audit");
    let mut invalid = CLASS.to_vec();
    invalid[nonfinal_store + 1..nonfinal_store + 3].copy_from_slice(&final_field.to_be_bytes());
    let error = decompile(&invalid, &Options::default()).unwrap_err().to_string();
    assert!(error.contains("alternate constructor invocation after early final field assignment"), "{error}");
}

#[test]
fn preview_pattern_values_feed_the_constructor_without_spilling_this() {
    let single = decompile(PREVIEW_SINGLE, &Options::default()).unwrap().text;
    assert_eq!(single.matches("this(switch (s)").count(), 2, "{single}");
    assert_eq!(single.matches("default -> \"Non-triangle\";").count(), 2, "{single}");
    assert!(single.contains("case null -> \"null\";"), "{single}");

    let guarded = vineflower_rs::ClassGroup::new(PREVIEW_GUARDED).unwrap()
        .decompile("pkg/TestSwitchPatternMatchingConstructor1", &Options::default()).unwrap().text;
    assert_order(&guarded, &[
        "this(switch (", "case null -> \"null\";", " && (", "calculateArea()",
        "-> \"Large triangle\";", "-> \"Small triangle\";", "default -> \"Non-triangle\";",
    ]);
    assert!(!guarded.contains("typeSwitch") && !guarded.contains("while ("), "{guarded}");
}

#[test]
fn preview_switch_rejects_a_stack_map_without_the_constructor_receiver() {
    let class = ClassFile::parse(PREVIEW_SINGLE).unwrap();
    let code = constructor(&class, "(Ljava/lang/Object;)V");
    let map = code.attributes.iter().find(|attribute| {
        class.pool.utf8(attribute.name_index).unwrap() == "StackMapTable"
    }).unwrap();
    // The first frame at offset 5 is full: four locals and one stack entry;
    // the final tag of this frame must be uninitializedThis.
    let stack = 2 + 1 + 2 + 2 + (1 + 3 + 3 + 1) + 2;
    assert_eq!(map.data[stack], 6);
    let base = map.data.as_ptr() as usize - PREVIEW_SINGLE.as_ptr() as usize;
    let mut invalid = PREVIEW_SINGLE.to_vec();
    invalid[base + stack] = 5; // Null, a structurally valid but incompatible verifier operand.
    assert!(decompile(&invalid, &Options::default()).is_err());
}
