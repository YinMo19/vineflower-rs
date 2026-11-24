use crate::Options;

use super::*;

const ECLIPSE: &[u8] =
    include_bytes!("../../tests/upstream/testData/classes/custom/TestEclipseSwitchEnum.class");
const EMPTY: &[u8] = include_bytes!("../../tests/smoke/java8/TestEnumSwitchEmpty.class");
const EMPTY_AUX: &[u8] = include_bytes!("../../tests/smoke/java8/TestEnumSwitchEmpty$1.class");
const JAVAC: [&[u8]; 5] = [
    include_bytes!("../../tests/smoke/java8/TestSwitchOnEnum.class"),
    include_bytes!("../../tests/smoke/java8/TestSwitchOnEnum$1.class"),
    include_bytes!("../../tests/smoke/java8/TestSwitchOnEnum$Example.class"),
    include_bytes!("../../tests/smoke/java8/TestSwitchOnEnum$Example$A.class"),
    include_bytes!("../../tests/smoke/java8/TestSwitchOnEnum$Example$B.class"),
];
const ECJ_OWNER: &str = "pkg/TestEclipseSwitchEnum";
const ECJ_TABLE: &str = "$SWITCH_TABLE$pkg$TestEclipseSwitchEnum";
const EMPTY_OWNER: &str = "pkg/TestEnumSwitchEmpty";
const EMPTY_HOLDER: &str = "pkg/TestEnumSwitchEmpty$1";

fn method_key(group: &ClassGroup<'_>, owner: &str, name: &str) -> Method {
    let class = group.get(owner).unwrap();
    let method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == name)
        .unwrap();
    (method.name_index, method.descriptor_index)
}

fn code_range(bytes: &[u8], name: &str) -> std::ops::Range<usize> {
    let class = ClassFile::parse(bytes).unwrap();
    let method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == name)
        .unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - bytes.as_ptr() as usize;
    start..start + code.bytes.len()
}

#[test]
fn eclipse_guarded_lazy_table_yields_enum_cases_and_hides_both_members() {
    let group = ClassGroup::new([ECLIPSE]).unwrap();
    let plan = Plan::build(&group);
    let method = method_key(&group, ECJ_OWNER, "test");
    assert!(matches!(
        plan.action(ECJ_OWNER, method, 8, false),
        Some(Action::Switch(ECJ_OWNER))
    ));
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, FIELD),
        Some(true)
    );
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, ACCESSOR),
        Some(true)
    );
    assert_eq!(
        plan.label(ECJ_OWNER, method, 8, 1, false),
        Some(("Lpkg/TestEclipseSwitchEnum;", "A"))
    );
    assert_eq!(
        plan.label(ECJ_OWNER, method, 8, 2, false),
        Some(("Lpkg/TestEclipseSwitchEnum;", "B"))
    );
    assert_eq!(
        plan.label(ECJ_OWNER, method, 8, 3, false),
        Some(("Lpkg/TestEclipseSwitchEnum;", "C"))
    );

    let options = Options {
        decompile_inner: false,
        remove_synthetic: false,
        ..Options::default()
    };
    let source = group.decompile(ECJ_OWNER, &options).unwrap().text;
    assert!(source.contains("switch ("), "{source}");
    assert!(
        !source.contains("ordinal()") && !source.contains(ECJ_TABLE),
        "{source}"
    );
    let labels = ["case A:", "case B:", "case C:"].map(|label| source.find(label).unwrap());
    assert!(labels[0] < labels[1] && labels[1] < labels[2], "{source}");
}

#[test]
fn javac_empty_switches_consume_the_map_but_keep_all_three_evaluations() {
    let group = ClassGroup::new([EMPTY, EMPTY_AUX]).unwrap();
    let plan = Plan::build(&group);
    for (name, offset) in [("test", 10), ("test2", 16), ("test2", 25)] {
        assert!(matches!(
            plan.action(
                EMPTY_OWNER,
                method_key(&group, EMPTY_OWNER, name),
                offset,
                true
            ),
            Some(Action::Empty("java/lang/annotation/ElementType"))
        ));
    }
    assert_eq!(plan.auxiliary_visibility(EMPTY_HOLDER), Some(true));

    let source = group
        .decompile(EMPTY_OWNER, &Options::default())
        .unwrap()
        .text;
    assert!(source.contains("switch (ElementType.TYPE) {}"), "{source}");
    assert!(
        source.contains("switch (et) {}") && source.contains("switch (et2) {}"),
        "{source}"
    );
    assert_eq!(source.matches("switch (").count(), 3, "{source}");
    assert!(!source.contains(JAVAC_PREFIX), "{source}");
}

#[test]
fn javac_auxiliary_recovers_multiple_independent_enum_maps() {
    let group = ClassGroup::new(JAVAC).unwrap();
    let plan = Plan::build(&group);
    let owner = "pkg/TestSwitchOnEnum";
    let method = method_key(&group, owner, "testSOE");
    assert_eq!(
        plan.auxiliary_visibility("pkg/TestSwitchOnEnum$1"),
        Some(true)
    );
    assert!(plan.action(owner, method, 8, false).is_none());
    assert!(matches!(
        plan.action(owner, method, 8, true),
        Some(Action::Switch("java/util/concurrent/TimeUnit"))
    ));
    assert_eq!(
        plan.label(owner, method, 8, 1, true),
        Some(("Ljava/util/concurrent/TimeUnit;", "MICROSECONDS"))
    );
    assert_eq!(
        plan.label(owner, method, 8, 2, true),
        Some(("Ljava/util/concurrent/TimeUnit;", "SECONDS"))
    );

    let source = group.decompile(owner, &Options::default()).unwrap().text;
    for label in ["MICROSECONDS", "SECONDS", "A1", "A2", "B1", "B2"] {
        assert!(source.contains(&format!("case {label}:")), "{source}");
    }
    assert!(!source.contains(JAVAC_PREFIX), "{source}");
}

#[test]
fn eclipse_catch_must_protect_each_entry_and_consume_only_no_such_field_error() {
    let range = code_range(ECLIPSE, ECJ_TABLE);
    let mut changed = ECLIPSE.to_vec();
    // Code bytes are followed by u2 exception_table_length and four u2 values
    // per row. Replace the first catch class with the class of the fixture.
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let catch_type = range.end + 2 + 6;
    changed[catch_type..catch_type + 2].copy_from_slice(&class.this_class.to_be_bytes());
    let group = ClassGroup::new([changed.as_slice()]).unwrap();
    let plan = Plan::build(&group);
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, FIELD),
        Some(false)
    );
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, ACCESSOR),
        Some(false)
    );
    assert!(
        plan.action(ECJ_OWNER, method_key(&group, ECJ_OWNER, "test"), 8, true)
            .is_none()
    );
}

#[test]
fn label_lookup_keeps_case_order_from_the_switch_not_enum_declaration_order() {
    let range = code_range(ECLIPSE, ECJ_TABLE);
    let ops = bytecode::decode(&ECLIPSE[range.clone()]).unwrap();
    let mut get_constants = ops
        .windows(2)
        .filter(|pair| pair[0].opcode == 0xb2 && pair[1].opcode == 0xb6);
    let first = range.start + get_constants.next().unwrap()[0].offset as usize + 1;
    let second = range.start + get_constants.next().unwrap()[0].offset as usize + 1;
    let mut changed = ECLIPSE.to_vec();
    changed[first..first + 2].copy_from_slice(&ECLIPSE[second..second + 2]);
    changed[second..second + 2].copy_from_slice(&ECLIPSE[first..first + 2]);
    let group = ClassGroup::new([changed.as_slice()]).unwrap();
    let source = group
        .decompile(ECJ_OWNER, &Options::default())
        .unwrap()
        .text;
    assert!(
        source.find("case B:").unwrap() < source.find("case A:").unwrap(),
        "{source}"
    );
}

#[test]
fn javac_table_escape_keeps_the_entire_auxiliary_and_other_uses() {
    let range = code_range(EMPTY, "test");
    let mut changed = EMPTY.to_vec();
    // Leave the original getstatic, but discard the array itself instead of
    // its selected value. The two canonical lookups in test2 stay untouched.
    changed[range.start + 3..range.end - 1].fill(0x00);
    changed[range.start + 3] = 0x57;
    let group = ClassGroup::new([changed.as_slice(), EMPTY_AUX]).unwrap();
    let plan = Plan::build(&group);
    assert_eq!(plan.auxiliary_visibility(EMPTY_HOLDER), Some(false));
    assert_eq!(
        plan.member_visibility(
            EMPTY_HOLDER,
            "$SwitchMap$java$lang$annotation$ElementType",
            FIELD
        ),
        Some(false)
    );
    assert!(
        plan.action(
            EMPTY_OWNER,
            method_key(&group, EMPTY_OWNER, "test2"),
            16,
            true
        )
        .is_none()
    );

    let source = group
        .decompile(EMPTY_OWNER, &Options::default())
        .unwrap()
        .text;
    assert!(
        source.contains("static final int[] $SwitchMap$java$lang$annotation$ElementType"),
        "{source}"
    );
    assert!(
        source.contains("et.ordinal()") && source.contains("et2.ordinal()"),
        "{source}"
    );
}

#[test]
fn an_unused_but_otherwise_valid_eclipse_table_is_not_hidden() {
    let mut changed = ECLIPSE.to_vec();
    let range = code_range(ECLIPSE, "test");
    changed[range.clone()].fill(0x00);
    changed[range.start] = 0xb1;
    let group = ClassGroup::new([changed.as_slice()]).unwrap();
    let plan = Plan::build(&group);
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, FIELD),
        Some(false)
    );
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, ACCESSOR),
        Some(false)
    );
}

#[test]
fn a_case_key_without_a_proven_enum_constant_retains_the_map() {
    let range = code_range(ECLIPSE, ECJ_TABLE);
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let ops = bytecode::decode(&ECLIPSE[range.clone()]).unwrap();
    let key = ops
        .windows(2)
        .find(|pair| integer(&class.pool, &pair[0]) == Some(3) && pair[1].opcode == 0x4f)
        .unwrap()[0]
        .offset as usize;
    let mut changed = ECLIPSE.to_vec();
    changed[range.start + key] = 0x07; // iconst_4

    let group = ClassGroup::new([changed.as_slice()]).unwrap();
    let plan = Plan::build(&group);
    assert_eq!(
        plan.member_visibility(ECJ_OWNER, ECJ_TABLE, ACCESSOR),
        Some(false)
    );
    assert!(
        plan.action(ECJ_OWNER, method_key(&group, ECJ_OWNER, "test"), 8, true)
            .is_none()
    );
}

#[test]
fn an_effectful_selector_call_and_array_access_are_emitted_once() {
    let class = ClassFile::parse(ECLIPSE).unwrap();
    let helper = code_range(ECLIPSE, ECJ_TABLE);
    let helper_ops = bytecode::decode(&ECLIPSE[helper.clone()]).unwrap();
    let values = helper_ops
        .iter()
        .find(|op| {
            matches!(
                reference(&class.pool, op, 0xb8),
                Some((ECJ_OWNER, "values", _))
            )
        })
        .unwrap();
    let invoke = helper.start + values.offset as usize;

    let test = code_range(ECLIPSE, "test");
    let mut changed = ECLIPSE.to_vec();
    // Replace aload_1 with values()[0]. The enclosing tableswitch shifts by
    // four bytes, preserving its alignment and every relative branch target.
    drop(changed.splice(
        test.start + 3..test.start + 4,
        [
            ECLIPSE[invoke],
            ECLIPSE[invoke + 1],
            ECLIPSE[invoke + 2],
            0x03,
            0x32,
        ],
    ));
    changed[test.start - 8..test.start - 6].copy_from_slice(&3u16.to_be_bytes());
    for offset in [test.start - 12, test.start - 4] {
        let length = u32::from_be_bytes(ECLIPSE[offset..offset + 4].try_into().unwrap());
        changed[offset..offset + 4].copy_from_slice(&(length + 4).to_be_bytes());
    }
    let test_method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == "test")
        .unwrap();
    let code = test_method.code(&class.pool).unwrap().unwrap();
    let stack_map = find_attribute(&code.attributes, &class.pool, "StackMapTable")
        .unwrap()
        .unwrap();
    let first_frame = stack_map.as_ptr() as usize - ECLIPSE.as_ptr() as usize + 2;
    changed[first_frame + 4] += 4; // shift only the first (relative) frame
    let lines = find_attribute(&code.attributes, &class.pool, "LineNumberTable")
        .unwrap()
        .unwrap();
    let line_table = lines.as_ptr() as usize - ECLIPSE.as_ptr() as usize;
    for (row, entry) in lines[2..].chunks_exact(4).enumerate() {
        let offset = u16::from_be_bytes(entry[..2].try_into().unwrap());
        if offset >= 8 {
            let start = line_table + 6 + 4 * row;
            changed[start..start + 2].copy_from_slice(&(offset + 4).to_be_bytes());
        }
    }
    let group = ClassGroup::new([changed.as_slice()]).unwrap();
    let source = group
        .decompile(ECJ_OWNER, &Options::default())
        .unwrap()
        .text;
    assert_eq!(source.matches("values()[0]").count(), 1, "{source}");
    assert!(
        source.contains("switch (") && source.contains("case A:"),
        "{source}"
    );
    assert!(!source.contains(ECJ_TABLE), "{source}");
}
