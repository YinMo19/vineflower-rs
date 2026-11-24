use vineflower_rs::{
    classfile::ClassFile,
    kotlin::{KotlinError, decompile_class},
};

// plugins/kotlin/testData/src/kt/pkg/TestTailrecFunctions.kt, compiled by upstream.
static CLASS: &[u8] = include_bytes!("smoke/kotlin/TestTailrecFunctions.class");

#[test]
fn staged_long_arguments_recover_tail_calls_without_assigning_parameters() {
    let source = decompile_class(&ClassFile::parse(CLASS).unwrap()).unwrap().unwrap();
    for expected in [
        "tailrec fun sum(x: Long, sum: Long): Long",
        "if (x == 0L) sum else this.sum(x - 1L, sum + x)",
        "tailrec fun fastPow(x: Long, n: Long, acc: Long = 1L): Long",
        "this.fastPow(x * x, n / 2L, acc)",
        "this.fastPow(x, n - 1L, acc * x)",
        concat!(
            "if (n == 0L) 1L else if (n % 2L == 0L) this.fastPow(x * x, n / 2L) ",
            "else x * this.fastPow(x, n - 1L)"
        ),
        "return this.testFinallyReturn()",
    ] {
        assert!(source.contains(expected), "missing {expected:?}:\n{source}");
    }
    for parameter in ["x", "sum", "n", "acc"] {
        let assignment = format!("{parameter} = ");
        assert!(!source.lines().any(|line| line.trim_start().starts_with(&assignment)));
    }
}

#[test]
fn scratch_reloads_must_match_the_staged_argument_order() {
    let class = ClassFile::parse(CLASS).unwrap();
    let sum = class.methods.iter().find(|method| class.pool.utf8(method.name_index).unwrap() == "sum").unwrap();
    let code = sum.code(&class.pool).unwrap().unwrap();
    let start = code.bytes.as_ptr() as usize - CLASS.as_ptr() as usize;
    assert_eq!(&code.bytes[29..35], &[0x16, 7, 0x40, 0x16, 9, 0x42]);
    // Both old parameters are still evaluated before either is updated, but
    // swapping the reloads invalidates the proof of source argument order.
    let mut modified = CLASS.to_vec();
    modified.swap(start + 30, start + 33);
    assert!(matches!(
        decompile_class(&ClassFile::parse(&modified).unwrap()),
        Err(KotlinError::Unsupported {
            declaration,
            feature: "unproven Kotlin tail-recursive parameter updates",
        }) if declaration == "sum"
    ));
}
