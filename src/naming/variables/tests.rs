// Based on Vineflower's variable-renaming plugin fixtures (Apache-2.0).

use super::*;

fn types(renamer: &mut VariableNamer, descriptors: &[&str]) -> Vec<String> {
    descriptors
        .iter()
        .map(|descriptor| renamer.rename_local(&Type::parse(descriptor).unwrap(), None).unwrap())
        .collect()
}

#[test]
fn jad_fixture_primitives_and_wrappers() {
    let mut jad = VariableRenamer::Jad.for_method(false, false, 52);
    assert_eq!(
        types(&mut jad, &["S", "S", "B", "B", "C", "C", "D", "D", "F", "F", "I", "I", "J", "J", "I", "I", "J"]),
        ["short1", "short2", "b0", "b1", "c0", "c1", "d0", "d1", "f", "f1", "i", "j", "k", "l", "i1", "j1", "k1"]
    );
    assert_eq!(
        types(&mut jad, &["Z", "Z", "Z", "Z", "Ljava/lang/Class;", "Ljava/lang/Class;", "Ljava/lang/Enum;", "Ljava/lang/Enum;", "Ljava/lang/Package;", "Ljava/lang/Package;"]),
        ["flag", "flag1", "flag2", "flag3", "oclass", "oclass1", "oenum", "oenum1", "opackage", "opackage1"]
    );
    assert_eq!(
        types(&mut jad, &["Ljava/io/File;", "Ljava/io/File;", "Ljava/lang/String;", "Ljava/lang/String;", "Ljava/lang/Long;", "Ljava/lang/Byte;", "Ljava/lang/Short;", "Ljava/lang/Boolean;"]),
        ["file1", "file2", "s", "s1", "olong", "obyte", "oshort", "obool"]
    );
}

#[test]
fn jad_array_rank_and_cleaned_type_stems() {
    let mut jad = VariableRenamer::Jad.for_method(false, false, 52);
    assert_eq!(
        types(&mut jad, &["[I", "[[I", "[J", "[Ljava/lang/String;", "[[[Ljava/lang/String;", "Lpkg/Example;", "Lpkg/Example;"]),
        ["aint", "aint1", "along", "astring", "astring1", "example", "example1"]
    );
    let map = Type::parse("Ljava/util/Map;").unwrap();
    assert_eq!(jad.rename_local(&map, Some("java.util.Map<java.lang.String, Long>")).as_deref(), Some("map"));
    assert_eq!(jad.rename_local(&map, Some("java.util.Map")).as_deref(), Some("map1"));
    assert_eq!(jad.rename_local(&map, Some("this")), None);
}

#[test]
fn tiny_fixture_letter_sequences_use_base_26() {
    for (desc, expected) in [
        ("I", "i j k l m n o p q r s t u v w x y z ba"),
        ("F", "f g h i j k l m n o p q r s t u v w x"),
        ("D", "d e f g h i j k l m n o p q r s t u v"),
        ("S", "s t u v w x y z ba bb bc bd be bf bg bh bi bj bk"),
        ("B", "b c d e f g h i j k l m n o p q r s t"),
        ("C", "c d e f g h i j k l m n o p q r s t u"),
    ] {
        let mut tiny = VariableRenamer::Tiny.for_method(false, false, 52);
        assert_eq!(types(&mut tiny, &[desc; 19]), expected.split_whitespace().collect::<Vec<_>>());
    }
    let mut tiny = VariableRenamer::Tiny.for_method(false, false, 52);
    assert_eq!(types(&mut tiny, &["Z"; 19]), (0..19).map(|i| if i == 0 { "bl".into() } else { format!("bl{i}") }).collect::<Vec<String>>());
}

#[test]
fn tiny_fixture_reserves_type_names_and_pluralizes_object_arrays() {
    let mut tiny = VariableRenamer::Tiny.for_method(false, false, 52);
    assert_eq!(
        types(&mut tiny, &["Lpkg/Owner$PascalCase;"; 3]),
        ["pascalCase", "pascalCase1", "pascalCase2"]
    );
    assert_eq!(types(&mut tiny, &["Lpkg/Owner$camelCase;"; 3]), ["camelCase1", "camelCase2", "camelCase3"]);
    assert_eq!(types(&mut tiny, &["Lpkg/Owner$clas;"; 3]), ["clas1", "clas2", "clas3"]);
    let mut tiny = VariableRenamer::Tiny.for_method(false, false, 52);
    assert_eq!(types(&mut tiny, &["[Lpkg/Owner$PascalCase;"; 3]), ["pascalCases", "pascalCases1", "pascalCases2"]);
    assert_eq!(types(&mut tiny, &["[Lpkg/Owner$camelCase;"; 3]), ["camelCases", "camelCases1", "camelCases2"]);
    assert_eq!(types(&mut tiny, &["[Lpkg/Owner$clas;"; 3]), ["clas1", "clas2", "clas3"]);
    assert_eq!(types(&mut tiny, &["[I", "[[I", "J", "Lpkg/Do;", "Lpkg/İtem;"]), ["i", "j", "l", "do_", "item"]);
}

#[test]
fn options_precedence_and_ordered_binding_versions() {
    use VariableRenamer::{Jad, Tiny};
    assert_eq!(VariableRenamer::select(None, false), None);
    assert_eq!(VariableRenamer::select(None, true), Some(Jad));
    assert_eq!(VariableRenamer::select(Some("tiny"), true), Some(Tiny));
    assert_eq!(VariableRenamer::select(Some(""), true), None);
    assert_eq!(VariableRenamer::select(Some("unknown"), true), None);
    assert_eq!(VariableRenamer::select(Some("JAD"), false), None);
    let int = Type::Primitive(Primitive::Int);
    assert_eq!(Tiny.for_method(false, true, 52).rename_parameter(0, &int, None), None);
    assert_eq!(Jad.for_method(false, false, 52).rename_parameter(0, &int, None), None);
    let mut jad = Jad.for_method(false, true, 52);
    let binding = |index, version, ty| VariableBinding { index, version, ty, cast_name: None };
    let long = Type::Primitive(Primitive::Long);
    assert_eq!(
        jad.rename_bindings(
            4,
            [
                binding(5, 0, &int),
                binding(1, 1, &long),
                binding(4, 1, &int),
                binding(4, 0, &long),
                binding(1, 0, &long),
                binding(3, 0, &int),
            ],
        ),
        [
            ((1, 0), String::from("i")),
            ((1, 1), String::from("i")),
            ((3, 0), String::from("j")),
            ((4, 0), String::from("k")),
            ((4, 1), String::from("l")),
            ((5, 0), String::from("i1")),
        ]
    );
    assert_eq!(jad.rename_parameter(1, &long, None).as_deref(), Some("i"));
    assert_eq!(Tiny.for_method(true, false, 52).rename_parameter(0, &int, None).as_deref(), Some("i"));
}

#[test]
fn enclosed_methods_inherit_names_without_parameter_cache() {
    let int = Type::Primitive(Primitive::Int);
    for provider in [VariableRenamer::Jad, VariableRenamer::Tiny] {
        let mut parent = provider.for_method(true, false, 52);
        assert_eq!(parent.rename_parameter(0, &int, None).as_deref(), Some("i"));
        let mut child = provider.for_method(true, false, 52);
        child.inherit(&parent);
        assert_eq!(child.rename_parameter(0, &int, None).as_deref(), Some("j"));
        assert_eq!(child.rename_local(&int, None).as_deref(), Some("k"));
        assert_eq!(parent.rename_local(&int, None).as_deref(), Some("j"));
    }
}
