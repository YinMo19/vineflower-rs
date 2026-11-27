use super::{ClassNodeId, Cx};
use crate::decompiler::{
    exps::{Expr, ExprKind, Invocation},
    ir::Ir,
    vars::processor::{VarNamesCollector, VarProcessor},
    vars::var_version_pair::VarVersionPair as Version,
};
use crate::engine::class_wrapper::MethodSlot;
use crate::structs::attr::LocalVariable;
use crate::types::{MethodDescriptor, VarType};
use crate::util::jhash::JHashMap;
use arcstr::ArcStr;
use std::{io, sync::Arc};

struct Binding {
    name: Option<ArcStr>,
    lvt: Option<Arc<LocalVariable>>,
    source: Option<Version>,
}

type Bindings = JHashMap<Version, Binding>;

/// Snapshot the enclosing scope before any collision has been renamed. New
/// names occupy a separate collector and do not turn a later local into a collision.
fn reserved_names(vars: &VarProcessor) -> VarNamesCollector {
    let mut reserved = vars.name_collector.clone();
    reserved.used.extend(vars.names.values().cloned());
    reserved
        .used
        .extend(vars.clashing_names.values().cloned().map(Some));
    for receiver in vars.this_vars.keys() {
        reserved
            .used
            .remove(&vars.names.get(receiver).cloned().flatten());
    }
    reserved
}

struct LambdaParameters {
    content: MethodDescriptor,
    captures: usize,
    is_static: bool,
}

impl LambdaParameters {
    fn bind(
        &self,
        ir: &Ir,
        invocation: &Invocation,
        outer: &VarProcessor,
        local: &VarProcessor,
        names: &mut VarNamesCollector,
        bindings: &mut Bindings,
    ) -> io::Result<()> {
        for (i, (slot, _)) in self.content.parameter_slots(self.is_static).enumerate() {
            let pair = Version::new(slot, 0);
            if i < self.captures {
                let operand = invocation
                    .parameters
                    .get(i + usize::from(!self.is_static))
                    .ok_or_else(|| {
                        io::Error::new(
                            io::ErrorKind::InvalidData,
                            "Missing captured lambda operand",
                        )
                    })?;
                if let Some(var) = Expr::variable(ir, *operand) {
                    bindings.insert(
                        pair,
                        Binding {
                            name: outer.names.get(&var.pair()).cloned().flatten(),
                            lvt: var.lvt.clone(),
                            source: Some(var.pair()),
                        },
                    );
                }
            } else if !bindings.contains_key(&pair) {
                bindings.insert(
                    pair,
                    Binding {
                        name: names.free_name(local.names.get(&pair).and_then(Option::as_deref)),
                        lvt: None,
                        source: None,
                    },
                );
            }
        }
        Ok(())
    }
}

/// Resolve a lambda implementation's names in the enclosing method's scope.
pub fn set_lambda_vars(cx: &mut Cx, parent: ClassNodeId, child: ClassNodeId) -> io::Result<()> {
    let info = cx.class_nodes[child]
        .lambda
        .as_ref()
        .expect("Expected a lambda");
    if info.is_method_reference {
        return Ok(());
    }
    let slot = MethodSlot::by_key(cx, parent, &info.content_method_key).ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidData, "Missing lambda content method")
    })?;
    let variables = slot.get(cx).variables;
    if cx.ir[variables].nested_processed {
        log::warn!(
            "{}.{} processed twice",
            cx.class_nodes[parent].class.qualified_name,
            slot.get(cx).method
        );
        return Ok(());
    }
    let enclosing_key = cx.class_nodes[child]
        .enclosing_method
        .clone()
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Missing lambda enclosing method",
            )
        })?;
    let enclosing = MethodSlot::by_key(cx, parent, &enclosing_key).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "Missing enclosing method wrapper",
        )
    })?;
    if slot.get(cx).body.is_err() || enclosing.get(cx).body.is_err() {
        return Ok(());
    }

    let outer = enclosing.get(cx).variables;
    let content = MethodDescriptor::parse_descriptor(&info.content_method_descriptor);
    let formals = MethodDescriptor::parse_descriptor(&info.method_descriptor);
    let captures = content.params.len().saturating_sub(formals.params.len());
    let is_static = info.is_content_method_static;
    let parameters = LambdaParameters {
        content,
        captures,
        is_static,
    };
    let lambda_type =
        VarType::from_signature_cl(cx.class_nodes[child].simple_name.as_deref().unwrap(), true);
    if !is_static && cx.options.lambda_to_anonymous_class {
        let receiver = Version::new(0, 0);
        let name = cx.class_nodes[parent]
            .simple_name
            .as_deref()
            .unwrap_or("null");
        cx.ir[variables].this_vars.insert(
            receiver,
            cx.class_nodes[slot.node].class.qualified_name.clone(),
        );
        cx.ir[variables]
            .names
            .insert(receiver, Some(format!("{name}.this").into()));
    }

    let reserved = reserved_names(&cx.ir[outer]);
    let mut names = reserved.clone();
    let mut bindings = JHashMap::new();
    let local = &cx.ir[variables];
    for (pair, name) in local.names.iter() {
        let lvt = local.local_variables.get(pair);
        let name = lvt.map(|lv| lv.get_name()).or(name.as_ref()).cloned();
        if name.as_deref() != Some("this") && reserved.used.contains(&name) {
            let name = names.free_name(name.as_deref());
            let lvt = lvt
                .zip(name.clone())
                .map(|(lv, name)| Arc::new(lv.rename(name)));
            bindings.insert(
                *pair,
                Binding {
                    name,
                    lvt,
                    source: None,
                },
            );
        }
    }

    if enclosing.get(cx).body.as_ref().unwrap().is_none() {
        return Ok(());
    }
    for list in cx.wrapper_expr_lists(enclosing) {
        for &expr in &cx.ir[list] {
            for expr in Expr::all_exprents(&cx.ir, expr, true, true) {
                let ExprKind::New {
                    lambda: true,
                    new_type,
                    constructor: Some(call),
                    ..
                } = &cx.ir[expr].kind
                else {
                    continue;
                };
                if *new_type != lambda_type {
                    continue;
                }
                let ExprKind::Invocation(invocation) = &cx.ir[*call].kind else {
                    unreachable!()
                };
                parameters.bind(
                    &cx.ir,
                    invocation,
                    &cx.ir[outer],
                    &cx.ir[variables],
                    &mut names,
                    &mut bindings,
                )?;
            }
        }
    }

    slot.get_mut(cx)
        .outer_var_names
        .extend(bindings.values().map(|binding| binding.name.clone()));
    let vars = &mut cx.ir[variables];
    vars.name_collector.used.extend(names.used);
    for (&pair, binding) in bindings.iter() {
        vars.inherit_name(pair, binding.name.clone());
        if let Some(lvt) = &binding.lvt {
            vars.local_variables.insert(pair, lvt.clone());
        }
        if let Some(source) = binding.source {
            vars.sources.insert(pair, (enclosing_key.clone(), source));
        }
    }

    if slot.get(cx).body.as_ref().unwrap().is_none() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Missing lambda body",
        ));
    }
    for list in cx.wrapper_expr_lists(slot) {
        for i in 0..cx.ir[list].len() {
            for id in Expr::all_exprents(&cx.ir, cx.ir[list][i], true, true) {
                if let ExprKind::Variable(var) = &mut cx.ir[id].kind
                    && let Some(binding) = bindings.get(&var.pair())
                {
                    if let Some(lvt) = &binding.lvt {
                        Expr::set_local_variable(&mut cx.ir, id, lvt.clone());
                    } else {
                        var.lvt = None;
                    }
                }
            }
        }
    }
    cx.ir[variables].nested_processed = true;
    Ok(())
}
