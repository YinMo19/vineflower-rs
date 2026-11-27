use crate::upstream_reference::Corpus;
use std::{fmt::Write, fs, sync::Arc};
use vineflower_rs::{
    engine::{Cx, Options, class_nodes::load_classes, import_collector::ImportCollector},
    kotlin::{
        identifier, imports,
        types::{java_signature, kotlin_type},
    },
    structs::StructContext,
    types::{FieldDescriptor, MethodDescriptor, VarType},
    util::text_buffer::TextBuffer,
};

#[test]
#[ignore = "requires the upstream Kotlin plugin and its compiled kt classes"]
fn kotlin_classifier_and_source_types_match_the_bundled_plugin() {
    let corpus = Corpus::discover();
    let scratch = tempfile::tempdir().unwrap();
    let classes = corpus
        .root
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("plugins/kotlin/testData/classes/kt/pkg");
    let names = ["TestGenerics", "TestKotlinTypes", "TestReflection"];
    for name in names {
        let file = format!("{name}.class");
        fs::copy(classes.join(&file), scratch.path().join(file)).unwrap();
    }
    let reference = corpus.run_with_kotlin("KotlinTypesReference", &[], scratch.path());
    let options = Arc::new(Options::default());
    let mut context = StructContext::new(options.clone(), None);
    context.add_file(scratch.path(), true).unwrap();
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    let mut actual = String::new();
    let emit = |cx: &mut Cx, out: &mut String, ty: &VarType| {
        for outer in [false, true] {
            writeln!(out, "{}", kotlin_type(cx, Some(ty), outer).unwrap()).unwrap();
        }
        for nullable in [false, true] {
            writeln!(out, "{}", java_signature(ty.name(), nullable)).unwrap();
        }
    };
    for name in names {
        let node = cx.class_nodes.id(&format!("pkg/{name}")).unwrap();
        let class = Arc::clone(&cx.class_nodes[node].class);
        cx.imports = imports::from_parent(&ImportCollector::for_root(
            &cx.struct_context,
            &cx.class_nodes,
            &cx.class_nodes[node],
        ));
        for field in &class.fields {
            writeln!(actual, "{}", identifier(&field.name)).unwrap();
            let ty = field.signature().map_or_else(
                || FieldDescriptor::parse_descriptor(&field.descriptor).ty,
                |sig| sig.ty.clone(),
            );
            emit(&mut cx, &mut actual, &ty);
        }
        for method in &class.methods {
            writeln!(actual, "{}", identifier(&method.name)).unwrap();
            let desc = MethodDescriptor::parse_descriptor(&method.descriptor);
            let sig = method.signature();
            let (params, ret) = sig.as_ref().map_or((&desc.params, &desc.ret), |s| {
                (&s.parameter_types, &s.return_type)
            });
            for ty in params.iter().chain([ret]) {
                emit(&mut cx, &mut actual, ty);
            }
        }
        let mut buffer = TextBuffer::new(&cx);
        imports::write_imports(&cx, &mut buffer, true);
        writeln!(
            actual,
            "{}",
            buffer.convert_to_string_and_allow_data_discard()
        )
        .unwrap();
    }
    let (source, classifiers) = reference.split_once("signature|").unwrap();
    assert_eq!(source, actual);
    for row in classifiers.lines() {
        let mut columns = row.trim_start_matches("signature|").split('|');
        let name = columns.next().unwrap();
        let nullable = columns.next().unwrap().parse().unwrap();
        assert_eq!(java_signature(name, nullable), columns.next().unwrap());
    }
}

#[test]
#[ignore = "requires the bundled Kotlin plugin and compiled declaration fixtures"]
fn metadata_declarations_and_contracts_match_upstream() {
    use vineflower_rs::kotlin::{
        declarations::{KContract, KParameter, KType, KTypeParameter},
        metadata::{self, Payload},
    };
    let corpus = Corpus::discover();
    let scratch = tempfile::tempdir().unwrap();
    let classes = corpus
        .root
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("plugins/kotlin/testData/classes/kt/pkg");
    let names = [
        "TestContracts",
        "TestFunVarargs",
        "TestGenerics",
        "TestKotlinTypes",
    ];
    for name in names {
        let file = format!("{name}.class");
        fs::copy(classes.join(&file), scratch.path().join(file)).unwrap();
    }
    let reference = corpus.run_with_kotlin("KotlinDeclarationsReference", &[], scratch.path());
    let mut actual = String::new();
    for width in [160, 24] {
        let mut options = Options::default();
        options.preferred_line_length = width;
        let options = Arc::new(options);
        let mut context = StructContext::new(options.clone(), None);
        context.add_file(scratch.path(), true).unwrap();
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        for name in names {
            let node = cx.class_nodes.id(&format!("pkg/{name}")).unwrap();
            cx.imports = imports::from_parent(&ImportCollector::for_root(
                &cx.struct_context,
                &cx.class_nodes,
                &cx.class_nodes[node],
            ));
            let meta = metadata::parse(&cx.class_nodes[node].class)
                .unwrap()
                .unwrap();
            let Payload::Class(class) = meta.payload else {
                panic!("Expected Kotlin class")
            };
            let resolver = meta.names.as_ref().unwrap();
            let table = class.type_table.unwrap_or_default();
            let add_type = |cx: &mut Cx, buf: &mut TextBuffer, ty: KType| {
                buf.append(&ty.to_string()).append_char(' ');
                ty.write(cx, buf, 1).unwrap();
                buf.append_line_separator();
            };
            for func in &class.function {
                let mut buf = TextBuffer::new(&cx);
                for generic in &func.type_parameter {
                    for ty in KTypeParameter::from_proto(generic, resolver)
                        .unwrap()
                        .upper_bounds
                    {
                        add_type(&mut cx, &mut buf, ty);
                    }
                }
                let params = func
                    .value_parameter
                    .iter()
                    .map(|p| KParameter::for_function(p, resolver).unwrap())
                    .collect::<Vec<_>>();
                for p in &params {
                    p.write(&mut cx, &mut buf, 1).unwrap();
                    buf.append_line_separator();
                }
                add_type(
                    &mut cx,
                    &mut buf,
                    KType::from_proto(func.return_type.as_ref(), resolver).unwrap(),
                );
                if let Some(contract) = &func.contract {
                    KContract::from_proto(contract, &params, resolver, &table)
                        .unwrap()
                        .write(&mut cx, &mut buf, 1)
                        .unwrap();
                }
                buf.reformat();
                writeln!(actual, "{}", buf.convert_to_string_and_allow_data_discard()).unwrap();
            }
        }
    }
    assert_eq!(reference, actual);
}
