use super::*;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn local_class_declarations_match_upstream_scopes() {
    use std::collections::{BTreeMap, VecDeque};
    use vineflower_rs::decompiler::exps::ExprKind;
    use vineflower_rs::decompiler::stats::StatementKind;
    use vineflower_rs::engine::{
        class_processor::process_class_methods, counter_container::VAR_COUNTER,
        method_processor::defined_method, nested,
    };

    let scratch = tempfile::tempdir().unwrap();
    let java = upstream_reference::Corpus::discover().run(
        "LocalClassDeclarationReference",
        &["WrapperStages"],
        scratch.path(),
    );
    let mut rust = Vec::new();
    for debug in [false, true] {
        rust.push(format!("debug={}", u8::from(debug)));
        let mut options = Options::default();
        options.use_lvt_names = debug;
        options.include_runtime = "0".into();
        let options = Arc::new(options);
        let mut classes = StructContext::new(options.clone(), None);
        classes
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        let mut cx = Cx::new(Arc::new(classes));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let root = cx.class_nodes.id("DeclarationHost").unwrap();
        process_class_methods(&mut cx, root, defined_method).unwrap();

        let class = &mut cx.class_nodes[root];
        let missing = class.class.methods.index_of_key("missing ()V").unwrap();
        class.wrapper.as_mut().unwrap().methods[missing].body = Ok(None);
        let children: BTreeMap<_, _> = cx
            .class_nodes
            .iter()
            .filter_map(|(name, node)| {
                (node.kind == ClassKind::Local).then(|| {
                    let key = node.enclosing_method.as_ref().unwrap();
                    let owner = &cx.class_nodes[root];
                    let index = owner.class.methods.index_of_key(key.as_str()).unwrap();
                    let wrapper = &owner.wrapper.as_ref().unwrap().methods[index];
                    let slot = wrapper
                        .body
                        .as_ref()
                        .unwrap()
                        .as_ref()
                        .map(|body| body.counters.get_counter(VAR_COUNTER));
                    (name.to_string(), (index, slot))
                })
            })
            .collect();
        assert_eq!(children.len(), 9);
        nested::process_class(&mut cx, root).unwrap();

        for (name, (index, old_slot)) in children {
            let wrapper = &cx.class_nodes[root].wrapper.as_ref().unwrap().methods[index];
            if index == missing {
                let comments = wrapper
                    .comment_lines
                    .as_ref()
                    .unwrap()
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>()
                    .join("/");
                rust.push(format!("missing|{}|{comments}", wrapper.add_error_comment));
                continue;
            }
            let local = old_slot.unwrap();
            let body = wrapper.body.as_ref().unwrap().as_ref().unwrap();
            let new_count = body.counters.get_counter(VAR_COUNTER);
            let method_name = wrapper.method.name.clone();
            let owner = wrapper.variables;
            let mut queue = VecDeque::from([body.root]);
            let mut found = false;
            while let Some(stat) = queue.pop_front() {
                let statement = &cx.ir[stat];
                let kind = match statement.kind {
                    StatementKind::BasicBlock { .. } => "BASIC_BLOCK",
                    StatementKind::Do(_) => "DO",
                    StatementKind::If(_) => "IF",
                    StatementKind::Root { .. } => "ROOT",
                    StatementKind::Sequence => "SEQUENCE",
                    _ => "OTHER",
                };
                let stat_id = statement.id;
                queue.extend(statement.stats.iter().copied());
                let lists = [
                    Some(statement.var_definitions.as_slice()),
                    statement.exprents.map(|list| cx.ir[list].as_slice()),
                ];
                let mut declaration = None;
                for (region, list) in ["defs", "body"].into_iter().zip(lists) {
                    let Some(list) = list else {
                        continue;
                    };
                    for (pos, &expr) in list.iter().enumerate() {
                        let ExprKind::Variable(variable) = &cx.ir[expr].kind else {
                            continue;
                        };
                        if !variable.class_definition
                            || variable
                                .var_type
                                .as_ref()
                                .and_then(|ty| ty.value.as_deref())
                                != Some(name.as_str())
                        {
                            continue;
                        }
                        assert!(!found);
                        assert_eq!(variable.index, local);
                        assert_eq!(variable.version, 0);
                        found = true;
                        let previous = pos.checked_sub(1).map_or(-1, |pos| cx.ir[list[pos]].id);
                        let next = list.get(pos + 1).map_or(-1, |&expr| cx.ir[expr].id);
                        let fields = format!(
                            "{name}|{method_name}|{kind}|{stat_id}|{region}|{pos}/{}|{previous}|{next}|{local}|{new_count}|{}|{}|{}|{}|{}|{}",
                            list.len(),
                            cx.ir[expr].id,
                            variable.definition,
                            variable.class_definition,
                            variable.processor == Some(owner),
                            variable.lvt.is_none(),
                            cx.ir[expr].bytecode.is_none()
                        );
                        declaration = Some((fields, expr));
                    }
                }
                if let Some((fields, expr)) = declaration {
                    let copy = Expr::copy(&mut cx, &mut CounterContainer::default(), expr);
                    let ExprKind::Variable(variable) = &cx.ir[copy].kind else {
                        unreachable!();
                    };
                    rust.push(format!(
                        "{fields}|{}|{}",
                        variable.definition, variable.class_definition
                    ));
                }
            }
            assert!(found, "{name}");
        }
    }
    assert_eq!(rust.join("\n"), java.trim_end());
}
