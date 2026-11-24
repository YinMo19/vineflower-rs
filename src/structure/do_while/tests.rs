// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::structure::join_tests::lift;

#[test]
fn inline_test_owns_prefix_update_and_source_offsets() {
    let lines = lift(
        &[0x2a, 0x03, 0x1b, 0x4f, 0x84, 1, 1, 0x1b, 0x2a, 0xbe, 0xa1, 0xff, 0xf6, 0xb1],
        "([II)V",
    ).unwrap();
    assert_eq!(lines[0].text, "do {");
    assert_eq!(lines[1].text, "var0[0] = var1;");
    assert_eq!(lines[1].offsets, [0, 1, 2, 3]);
    assert_eq!(lines[2].text, "} while (++var1 < var0.length);");
    assert_eq!(lines[2].offsets, [4, 5, 6, 7, 8, 9, 10, 11, 12]);
}

#[test]
fn collapses_short_circuit_latch_after_an_early_return() {
    let lines = lift(
        &[
            0xb8, 0, 9, 0x57, 0x1a, 0x99, 0, 4, 0xb1,
            0x1b, 0x99, 0, 8, 0x1c, 0x1d, 0xa1, 0xff, 0xf1, 0xb1,
        ],
        "(ZZII)V",
    ).unwrap();
    assert_eq!(lines[0].text, "do {");
    assert!(lines.iter().any(|line| line.text == "Example.side();"));
    assert!(lines.iter().any(|line| line.text == "return;" && line.depth > 1));
    assert!(lines.iter().any(|line| line.text == "} while (var1 && var2 < var3);"));
}

#[test]
fn test_is_shared_by_the_skip_path_and_normal_body() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 10, 0xb8, 0, 9, 0x57, 0xa7, 0, 3,
            0x1b, 0x9a, 0xff, 0xf4, 0xb1,
        ],
        "(ZZ)V",
    ).unwrap();
    assert_eq!(lines[0].text, "do {");
    assert!(lines.iter().any(|line| line.text == "Example.side();" && line.depth > 1));
    assert_eq!(lines.iter().filter(|line| line.text == "} while (var1);").count(), 1);
}

#[test]
fn explicit_continue_goes_to_the_condition_not_the_shared_body_tail() {
    let lines = lift(
        &[
            0x1a, 0x99, 0, 16, 0x1b, 0x99, 0, 6, 0xa7, 0, 13,
            0xb8, 0, 9, 0x57, 0, 0, 0xb8, 0, 9, 0x57,
            0x1c, 0x9a, 0xff, 0xea, 0xb1,
        ],
        "(ZZZ)V",
    ).unwrap();
    assert_eq!(lines[0].text, "do {");
    assert!(lines.iter().any(|line| line.text == "continue;"));
    assert!(lines.iter().any(|line| line.text == "Example.side();" && line.depth > 1));
    assert!(lines.iter().any(|line| line.text == "Example.side();" && line.depth == 1));
    assert!(lines.iter().any(|line| line.text == "} while (var2);"));
}

#[test]
fn body_local_does_not_escape_into_condition() {
    let lines = lift(
        &[0xb8, 0, 9, 0x3b, 0x1a, 0x9a, 0xff, 0xfb, 0xb1],
        "()V",
    ).unwrap();
    assert_eq!(lines[0].text, "while (true) {");
    assert!(lines.iter().any(|line| line.text == "int var0 = Example.side();"));
    assert!(!lines.iter().any(|line| line.text.starts_with("} while")));
}

#[test]
fn condition_only_self_loop_stays_pre_test() {
    let lines = lift(&[0x84, 0, 0xff, 0x1a, 0x9d, 0xff, 0xfc, 0xb1], "(I)V").unwrap();
    assert_eq!(lines[0].text, "while (--var0 > 0) {");
}
