use std::{env, fmt::Write, fs, path::PathBuf, sync::Arc};

use vineflower_rs::{
    engine::{
        Cx, Options, class_nodes::load_classes, class_processor::process_class,
        class_writer::prepare_class_for_writing,
    },
    kotlin::{
        declarations::KParameter,
        members::{
            self, ClassElement, FieldElement, Hidden, KConstructor, KFunction, KProperty,
            MethodElement, PropertyMethod,
        },
    },
    structs::StructClass,
};

use super::upstream_reference::Corpus;

#[test]
#[ignore = "requires the upstream Kotlin plugin, its compiled Kotlin fixtures, and JDK 17+"]
fn kotlin_members_match_upstream() {
    let upstream = env::var_os("VINEFLOWER_UPSTREAM")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../vineflower"));
    let fixtures = upstream.join("plugins/kotlin/testData/classes");
    let scratch = tempfile::tempdir().unwrap();
    fs::write(scratch.path().join("fixtures"), fixtures.to_str().unwrap()).unwrap();
    let expected = Corpus::discover().run_with_kotlin(
        "KotlinMembersReference",
        &["KotlinMetadataBadMemberSubject"],
        scratch.path(),
    );

    let mut options = Options::default();
    options.decompile_kotlin = true;
    options.kt_enable = false;
    options.kt_export_metadata = true;
    let options = Arc::new(options);
    let mut context = vineflower_rs::structs::StructContext::new(options.clone(), None);
    for directory in ["kt", "ktold"] {
        context.add_file(&fixtures.join(directory), true).unwrap();
    }
    let mut classes = context.get_own_classes();
    classes.sort_unstable_by(|a, b| a.qualified_name.cmp(&b.qualified_name));
    let mut cx = Cx::new(Arc::new(context));
    let mut actual = String::new();
    for class in classes {
        assert!(!members::select_language(&mut cx, &class));
        print_class(&cx, &mut actual, &class);
    }

    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    for name in ["pkg/TestCompanionObject", "pkg/TestObject"] {
        let node = cx.class_nodes.id(name).unwrap();
        process_class(&mut cx, node).unwrap();
        prepare_class_for_writing(&mut cx, node).unwrap();
        members::process_objects(&mut cx, node).unwrap();
        writeln!(actual, "processed").unwrap();
        print_class(&cx, &mut actual, &cx.class_nodes[node].class);
        for &nested in &cx.class_nodes[node].nested {
            let class = &cx.class_nodes[nested].class;
            if class.qualified_name != name {
                print_class(&cx, &mut actual, class);
            }
        }
    }

    let mut options = Options::default();
    options.decompile_kotlin = true;
    options.kt_enable = false;
    let mut context = vineflower_rs::structs::StructContext::new(Arc::new(options), None);
    context
        .add_file(&fixtures.join("kt/ext/Person.class"), false)
        .unwrap();
    let class = context.get_class("ext/Person").unwrap();
    let method = class.get_method("getName", "()Ljava/lang/String;").unwrap();
    let mut library = Cx::new(Arc::new(context));
    assert!(!members::select_language(&mut library, &class));
    assert!(library.kotlin_members().is_none());
    writeln!(actual, "library|{}|-", class.own).unwrap();
    let invocation = members::invocation(
        &mut library,
        "ext/Person",
        "getName",
        "()Ljava/lang/String;",
    )
    .unwrap();
    assert_eq!(invocation.1, Some(PropertyMethod::Getter));
    let state = library.kotlin_members().unwrap();
    writeln!(
        actual,
        "library|{}|{}",
        class.own,
        method_element(state.method(method))
    )
    .unwrap();
    print_class(&library, &mut actual, &class);

    let mut options = Options::default();
    options.decompile_kotlin = true;
    let mut context = vineflower_rs::structs::StructContext::new(Arc::new(options), None);
    let malformed = [
        "KotlinMetadataBadMemberSubject",
        "KotlinMetadataBadFacadeSubject",
    ];
    for subject in malformed {
        context
            .add_file(&scratch.path().join(format!("{subject}.class")), false)
            .unwrap();
    }
    let mut malformed_context = Cx::new(Arc::new(context));
    for subject in malformed {
        let class = malformed_context
            .struct_context
            .get_class(&format!("kotlin/{subject}"))
            .unwrap();
        let method = class.get_method("first", "()V").unwrap();
        let selected = members::select_language(&mut malformed_context, &class);
        let Some(MethodElement::Function(first)) = malformed_context
            .kotlin_members()
            .and_then(|data| data.method(method))
            .cloned()
        else {
            panic!("Parsing failed before the first method attribute was published");
        };
        let selected_again = members::select_language(&mut malformed_context, &class);
        let Some(MethodElement::Function(updated)) = malformed_context
            .kotlin_members()
            .and_then(|data| data.method(method))
        else {
            panic!("Retry discarded the first method attribute");
        };
        writeln!(
            actual,
            "retry|{selected}|{selected_again}|{}",
            Arc::ptr_eq(&first, updated)
        )
        .unwrap();
        print_class(&malformed_context, &mut actual, &class);
    }

    let mut class = "";
    for (i, (expected, actual)) in expected.lines().zip(actual.lines()).enumerate() {
        if let Some(name) = expected.strip_prefix("class|") {
            class = name;
        }
        assert_eq!(actual, expected, "{class} at line {}", i + 1);
    }
    assert_eq!(actual.lines().count(), expected.lines().count());
}

fn print_class(cx: &Cx, out: &mut String, class: &StructClass) {
    let members = cx.kotlin_members();
    let class_element = match members.and_then(|members| members.class(class)) {
        Some(ClassElement::Class(cl)) => format!("class|{}", cl.proto.flags()),
        Some(ClassElement::File(file)) => {
            format!(
                "file|{}",
                file.multifile_name
                    .as_ref()
                    .map_or("null", |name| name.as_utf8_lossy())
            )
        }
        Some(ClassElement::MultifileFacade(parts)) => {
            let parts = parts
                .iter()
                .map(|part| part.as_utf8_lossy().as_str())
                .collect::<Vec<_>>();
            format!("facade|{}", parts.join(","))
        }
        Some(ClassElement::Synthetic(function)) => function_element(function),
        Some(ClassElement::FailedLambda) => "failed-lambda".to_owned(),
        Some(ClassElement::FunctionReference) => "reference".to_owned(),
        None => "-".to_owned(),
    };
    writeln!(out, "class|{}|{class_element}", class.qualified_name).unwrap();
    let primary = members
        .and_then(|data| data.primary_constructor(class))
        .map_or_else(|| "-".to_owned(), |ctor| constructor_element(ctor));
    writeln!(out, "primary|{primary}").unwrap();

    let mut field = |field: &vineflower_rs::structs::StructField| {
        let element = match members.and_then(|data| data.field(field)) {
            Some(FieldElement::Property(property)) => property_element(property),
            Some(FieldElement::Hidden(hidden)) => hidden_element(*hidden),
            None => "-".to_owned(),
        };
        writeln!(out, "field|{}|{}|{element}", field.name, field.descriptor).unwrap();
    };
    if let Some(members) = members {
        members.fields(class).for_each(|member| field(member));
    } else {
        class.fields.iter().for_each(|member| field(member));
    }

    let mut method = |method: &vineflower_rs::structs::StructMethod| {
        let element = method_element(members.and_then(|data| data.method(method)));
        let role = match members.and_then(|data| data.property_method(method)) {
            Some(PropertyMethod::Getter) => "GETTER",
            Some(PropertyMethod::Setter) => "SETTER",
            None => "null",
        };
        writeln!(
            out,
            "method|{}|{}|{element}|{role}",
            method.name, method.descriptor
        )
        .unwrap();
    };
    if let Some(members) = members {
        members.methods(class).for_each(|member| method(member));
    } else {
        class.methods.iter().for_each(|member| method(member));
    }
}

fn method_element(element: Option<&MethodElement>) -> String {
    match element {
        Some(MethodElement::Function(function)) => function_element(function),
        Some(MethodElement::Constructor(constructor)) => constructor_element(constructor),
        Some(MethodElement::Property(property)) => property_element(property),
        Some(MethodElement::Hidden(hidden)) => hidden_element(*hidden),
        None => "-".to_owned(),
    }
}

fn function_element(function: &KFunction) -> String {
    format!(
        "function|{}|{}|{}|{}|{}|{}|{}|{}|{}",
        function.name,
        function.flags,
        params(&function.parameters),
        function.return_type,
        display_option(function.receiver_type.as_ref()),
        function
            .type_parameters
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>()
            .join(","),
        function
            .context_receiver_types
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(","),
        function.contract.is_some(),
        function.known_override,
    )
}

fn constructor_element(constructor: &KConstructor) -> String {
    format!(
        "constructor|{}|{}|{}",
        constructor.flags,
        constructor.is_primary,
        params(&constructor.parameters)
    )
}

fn property_element(property: &KProperty) -> String {
    format!(
        "property|{}|{}|{}|{}|{}|{}|{}|{}|{}",
        property.name,
        property.flags,
        display_option(property.ty.as_ref()),
        property
            .getter
            .as_ref()
            .map_or_else(|| "-".to_owned(), |getter| getter.flags.to_string()),
        property
            .setter
            .as_ref()
            .map_or_else(|| "-".to_owned(), |setter| setter.flags.to_string()),
        property.setter_param_name.as_deref().unwrap_or("null"),
        property
            .underlying_field
            .as_ref()
            .map_or("-", |field| field.name.as_str()),
        property
            .annotations
            .iter()
            .map(|anno| anno.class_name.as_str())
            .collect::<Vec<_>>()
            .join(","),
        property.initializer.is_some(),
    )
}

fn hidden_element(hidden: Hidden) -> String {
    let name = match hidden {
        Hidden::Generic => "GENERIC",
        Hidden::CompanionInstance => "COMPANION_INSTANCE",
        Hidden::CompanionItem => "COMPANION_ITEM",
        Hidden::ObjectInstance => "OBJECT_INSTANCE",
        Hidden::DefaultImpl => "DEFAULT_IMPL",
    };
    format!("hidden|{name}")
}

fn params(values: &[KParameter]) -> String {
    values
        .iter()
        .map(|parameter| {
            format!(
                "{}:{}:{}:{}:{}",
                parameter.name,
                parameter.flags,
                parameter.ty,
                display_option(parameter.vararg_type.as_ref()),
                parameter.type_id,
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn display_option(value: Option<&impl std::fmt::Display>) -> String {
    value.map_or_else(|| "null".to_owned(), ToString::to_string)
}
