// SPDX-License-Identifier: Apache-2.0

use std::{fmt::Write, path::Path, sync::Arc};

use crate::upstream_reference::Corpus;
use vineflower_rs::{
    decompiler::{
        exps::{ExitType, Expr, ExprKind, InvocationFunction},
        ir::{ExprId, ExprListId},
        vars::var_version_pair::VarVersionPair,
    },
    engine::{
        Cx, Options,
        class_nodes::{ClassNodeId, load_classes},
        class_processor::process_class,
        class_writer::prepare_class_for_writing,
    },
    structs::StructContext,
    types::MethodDescriptor,
};

#[test]
fn writer_prepares_checked_in_enum_and_record_classes() {
    let smoke = Path::new(env!("CARGO_MANIFEST_DIR")).join("test/smoke");
    let enum_class = smoke.join("jasm/TestEnumStaticField.class");
    for profile in ["default", "enum-off"] {
        let mut rows = String::new();
        let mut cx = context(&enum_class, profile);
        dump_class(&mut cx, "pkg/TestEnumStaticField", &mut rows);
        assert_eq!(
            rows.contains("call\tjava/lang/Enum\t(Ljava/lang/String;I)V\n"),
            profile == "enum-off"
        );
    }

    for (record, compact) in [("TestRecordSimple", true), ("TestRecordMixup", false)] {
        let mut rows = String::new();
        let mut cx = context(&smoke.join(format!("java16/{record}.class")), "default");
        dump_class(&mut cx, &format!("pkg/{record}"), &mut rows);
        assert!(rows.contains(&format!("constructor\t(II)V\t{compact}\n")));
        assert!(rows.contains("formal\t1\tx\tx\nformal\t2\ty\ty\n"));
        assert_eq!(rows.contains("assign\t"), !compact);
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn writer_prepares_enum_and_record_constructors_like_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let reference = Corpus::discover().run("WriterEnumRecordReference", &[], scratch.path());
    let mut rows = String::new();
    for group in ["java8", "java17", "no-debug"] {
        let classes = scratch.path().join(group);
        let profiles: &[&str] = match group {
            "java8" => &["default", "lvt-off", "enum-off"],
            "java17" => &["default", "lvt-off", "enum-off", "tiny", "jad"],
            _ => &["default", "tiny-params"],
        };
        for &profile in profiles {
            writeln!(rows, "profile\t{group}\t{profile}").unwrap();
            let mut cx = context(&classes, profile);
            if group != "no-debug" && !matches!(profile, "tiny" | "jad") {
                dump_class(&mut cx, "WriterEnum", &mut rows);
                dump_class(&mut cx, "WriterQualifiers", &mut rows);
            }
            if group != "java8" {
                dump_class(&mut cx, "WriterWide", &mut rows);
                dump_class(&mut cx, "WriterExplicit", &mut rows);
            }
        }
    }

    let slices: Vec<_> = rows.split("profile\t").collect();
    let expected: Vec<_> = reference.split("profile\t").collect();
    assert_eq!(slices.len(), expected.len(), "writer profile count");
    for (actual, expected) in slices.into_iter().zip(expected) {
        assert_eq!(actual, expected, "writer preparation profile");
    }
}

fn context(classes: &Path, profile: &str) -> Cx {
    let mut options = Options::default();
    options.use_lvt_names = profile != "lvt-off";
    options.decompile_enums = profile != "enum-off";
    if matches!(profile, "tiny" | "jad") {
        options.variable_renaming = Some(profile.to_owned());
    } else if profile == "tiny-params" {
        options.variable_renaming = Some("tiny".to_owned());
    }
    options.rename_parameters = matches!(profile, "jad" | "tiny-params");
    let options = Arc::new(options);
    let mut context = StructContext::new(options.clone(), None);
    context.add_file(classes, true).unwrap();
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    cx
}

fn dump_class(cx: &mut Cx, name: &str, rows: &mut String) {
    let node = cx.class_nodes.id(name).unwrap();
    process_class(cx, node).unwrap();
    prepare_class_for_writing(cx, node).unwrap();

    writeln!(rows, "class\t{name}").unwrap();
    let mut hidden: Vec<_> = cx.class_nodes[node].hidden_members.iter().collect();
    hidden.sort_unstable();
    for key in hidden {
        writeln!(rows, "hidden\t{key}").unwrap();
    }

    let methods = &cx.class_nodes[node].wrapper.as_ref().unwrap().methods;
    let constructors: Vec<_> = methods
        .iter()
        .enumerate()
        .filter_map(|(index, method)| (method.method.name == "<init>").then_some(index))
        .collect();
    if name == "WriterQualifiers" {
        let initializers = &cx.class_nodes[node]
            .wrapper
            .as_ref()
            .unwrap()
            .static_field_initializers;
        for (expr, key) in initializers.iter().zip(initializers.lst_keys()) {
            dump_qualifiers(cx, key.as_ref().unwrap(), *expr, rows);
        }
        let (index, method) = methods
            .iter()
            .enumerate()
            .find(|(_, method)| method.method.name.starts_with("lambda$"))
            .unwrap();
        let name = method.method.name.clone();
        for list in expr_lists(cx, node, index) {
            for &expr in &cx.ir[list] {
                dump_qualifiers(cx, &name, expr, rows);
            }
        }
    }
    for index in constructors {
        dump_constructor(cx, node, index, rows);
    }
}

fn expr_lists(cx: &mut Cx, node: ClassNodeId, index: usize) -> Vec<ExprListId> {
    let method = &mut cx.class_nodes[node].wrapper.as_mut().unwrap().methods[index];
    assert!(
        method.decompile_error().is_none(),
        "{:?}",
        method.decompile_error()
    );
    let graph = method
        .body
        .as_mut()
        .unwrap()
        .as_mut()
        .unwrap()
        .graph(&mut cx.ir);
    graph
        .regular_breadth_first()
        .map(|node| graph[node].exprents)
        .collect()
}

fn dump_qualifiers(cx: &Cx, context: &str, expr: ExprId, rows: &mut String) {
    for expr in Expr::all_exprents(&cx.ir, expr, true, true) {
        if let ExprKind::Field(field) = &cx.ir[expr].kind {
            writeln!(
                rows,
                "qualifier\t{context}\t{}\t{}",
                field.name, field.force_qualified
            )
            .unwrap();
        }
    }
}

fn dump_constructor(cx: &mut Cx, node: ClassNodeId, index: usize, rows: &mut String) {
    let method = &cx.class_nodes[node].wrapper.as_ref().unwrap().methods[index];
    let descriptor = &method.method.descriptor;
    writeln!(
        rows,
        "constructor\t{descriptor}\t{}",
        method.is_compact_record_constructor
    )
    .unwrap();
    let variables = &cx.ir[method.variables];
    for (slot, _) in MethodDescriptor::parse_descriptor(descriptor).parameter_slots(false) {
        let pair = VarVersionPair::new(slot, 0);
        let name = variables
            .names
            .get(&pair)
            .and_then(Option::as_deref)
            .unwrap_or("null");
        let clash = variables
            .clashing_names
            .get(&pair)
            .map_or("null", |name| name.as_str());
        writeln!(rows, "formal\t{slot}\t{name}\t{clash}").unwrap();
    }
    for list in expr_lists(cx, node, index) {
        for &expr in &cx.ir[list] {
            match &cx.ir[expr].kind {
                ExprKind::Invocation(inv) if inv.function == InvocationFunction::Init => {
                    writeln!(
                        rows,
                        "call\t{}\t{}",
                        inv.classname.as_ref().unwrap(),
                        inv.string_descriptor()
                    )
                    .unwrap();
                }
                ExprKind::Assignment { left, right, .. } => {
                    if let ExprKind::Field(field) = &cx.ir[*left].kind {
                        write!(rows, "assign\t{}\t", field.name).unwrap();
                        if let ExprKind::Variable(var) = &cx.ir[*right].kind {
                            writeln!(rows, "{}\t{}", var.index, var.lvt.is_some()).unwrap();
                        } else {
                            writeln!(rows, "non-var").unwrap();
                        }
                    } else if let ExprKind::Variable(var) = &cx.ir[*left].kind
                        && var.definition
                    {
                        let variables = &cx.ir[var.processor.unwrap()];
                        let pair = var.pair();
                        let name = variables
                            .clashing_names
                            .get(&pair)
                            .or(var
                                .lvt
                                .as_ref()
                                .filter(|_| cx.options.use_lvt_names)
                                .map(|lvt| lvt.get_name()))
                            .or_else(|| variables.names.get(&pair).and_then(Option::as_ref))
                            .unwrap();
                        writeln!(rows, "local\t{}\t{name}", var.index).unwrap();
                    }
                }
                ExprKind::If { .. } => writeln!(rows, "if").unwrap(),
                ExprKind::Exit {
                    kind: ExitType::Throw,
                    ..
                } => writeln!(rows, "throw").unwrap(),
                _ => {}
            }
        }
    }
}
