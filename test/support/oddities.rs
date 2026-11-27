use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use vineflower_rs::decompiler::{
    exps::{Expr, ExprKind, FunctionType},
    ir::{ExprId, Ir, StatId},
    stats::StatementKind,
};
use vineflower_rs::engine::{
    Cx, Options,
    class_nodes::{ClassKind, load_classes},
    class_processor::process_class_methods,
    context_source::RuntimeImage,
    import_collector::get_short_name,
    method_processor::defined_method,
};
use vineflower_rs::structs::{StructContext, attr::LocalVariable};
use vineflower_rs::types::{CodeType, VarType};

use super::upstream_reference::{Corpus, jdk_home};

fn expressions(ir: &Ir, stat: StatId, output: &mut Vec<ExprId>) {
    let list = ir[stat]
        .exprents
        .map_or_else(|| stat.stat_exprents(ir), |list| ir[list].clone());
    for expr in list {
        output.extend(Expr::all_exprents(ir, expr, true, true));
    }
    for &child in &ir[stat].stats {
        expressions(ir, child, output);
    }
}

fn prepare_oddities(cx: &mut Cx, root: StatId, name: &str) {
    let mut exprs = Vec::new();
    expressions(&cx.ir, root, &mut exprs);
    match name {
        "unknownCast" | "badCast" => {
            let target = exprs
                .into_iter()
                .find_map(|expr| match &mut cx.ir[expr].kind {
                    ExprKind::Function {
                        op: FunctionType::Cast,
                        operands,
                        needs_cast,
                        ..
                    } => {
                        *needs_cast = true;
                        Some(operands[1])
                    }
                    _ => None,
                })
                .expect("Expected a real CHECKCAST");
            let ExprKind::Constant { var_type, .. } = &mut cx.ir[target].kind else {
                panic!("Cast target is not a type constant");
            };
            *var_type = if name == "badCast" {
                VarType::new(CodeType::Address)
            } else {
                VarType::VARTYPE_UNKNOWN
            };
        }
        "badDefinition" => {
            let definition = exprs
                .into_iter()
                .find(
                    |&expr| matches!(&cx.ir[expr].kind, ExprKind::Variable(var) if var.definition),
                )
                .expect("Expected a variable definition");
            let ExprKind::Variable(var) = &mut cx.ir[definition].kind else {
                unreachable!()
            };
            var.lvt = None;
            var.var_type = None;
            let (owner, pair) = (var.processor.unwrap(), var.pair());
            cx.ir[owner].versions.lower.remove(&pair);
        }
        "debugUnknown" => {
            let use_site = exprs
                .into_iter()
                .find(
                    |&expr| matches!(&cx.ir[expr].kind, ExprKind::Variable(var) if !var.definition),
                )
                .expect("Expected a variable read");
            let ExprKind::Variable(var) = &mut cx.ir[use_site].kind else {
                unreachable!()
            };
            var.lvt = Some(Arc::new(LocalVariable::new(
                0,
                1,
                "value".into(),
                "U".into(),
                var.index,
            )));
        }
        _ => {}
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn final_expression_diagnostics_preserve_import_lock() {
    let scratch = tempfile::tempdir().unwrap();
    let reference = Corpus::discover().run("OdditiesReference", &[], scratch.path());
    let jdk_image = Arc::new(RuntimeImage::open(&jdk_home()).unwrap());

    let mut rows = Vec::new();
    for nest in [false, true] {
        let mut options = Options::default();
        options.decompile_assert = !nest;
        let options = Arc::new(options);
        let mut context = StructContext::new(options.clone(), None);
        context.add_space(jdk_image.clone(), false);
        context
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let roots: Vec<_> = ["oddity/OdditiesContract", "oddity/OdditiesSubject"]
            .iter()
            .map(|name| cx.class_nodes.id(name).unwrap())
            .collect();
        for root in roots {
            assert_eq!(cx.class_nodes[root].kind, ClassKind::Root);
            process_class_methods(&mut cx, root, |cx, class, method| {
                let mut result = defined_method(cx, class, method)?.expect("Expected method body");
                prepare_oddities(cx, result.root, &method.name);
                let previous_lock = cx.imports.set_write_locked(nest);
                let previous_imports = cx.imports.imports();
                let failure = catch_unwind(AssertUnwindSafe(|| result.finish_method(cx, class)));
                let outcome = if method.name == "badCast" {
                    let message = failure.unwrap_err();
                    assert!(
                        message
                            .downcast_ref::<String>()
                            .unwrap()
                            .starts_with("invalid type: ")
                    );
                    "invalid-type"
                } else {
                    failure.unwrap()?;
                    "ok"
                };
                assert_eq!(cx.imports.set_write_locked(nest), nest);
                assert_eq!(cx.imports.imports(), previous_imports);
                let mut collision = String::new();
                if method.name == "cast" {
                    let shadow = get_short_name(cx, "shadow.types.Instant");
                    let time = get_short_name(cx, "java.time.Instant");
                    collision = format!(":{shadow}:{time}");
                }
                cx.imports.set_write_locked(previous_lock);

                let StatementKind::Root {
                    comment_lines,
                    add_error_comment,
                    ..
                } = &cx.ir[result.root].kind
                else {
                    unreachable!()
                };
                let warnings = comment_lines
                    .as_ref()
                    .into_iter()
                    .flatten()
                    .map(String::as_str)
                    .collect::<Vec<_>>()
                    .join("|");
                let profile = if nest { "nested" } else { "unlocked" };
                rows.push(format!(
                    "{profile}\t{}\t{}{}\t{outcome}:{add_error_comment}:{warnings}{collision}",
                    class.qualified_name, method.name, method.descriptor,
                ));
                Ok(Some(result))
            })
            .unwrap();
        }
    }
    let mut expected = reference.lines().collect::<Vec<_>>();
    expected.sort_unstable();
    rows.sort_unstable();
    assert_eq!(rows, expected);
    assert!(
        rows.iter()
            .any(|row| row.contains("Could not properly define all variable types"))
    );
    assert!(
        rows.iter()
            .any(|row| row.contains("OdditiesContract\tchecks")
                && row.contains("Could not resugar all assert statements"))
    );
    assert!(rows.iter().any(|row| row.contains("invalid-type:false")));
}
