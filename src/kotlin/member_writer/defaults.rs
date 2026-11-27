//! Recover default argument values from Kotlin's mask and marker wrappers.

use std::io;

use super::{invalid, method_slot};
use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::{
    exps::{ConstantValue, Expr, ExprKind, write},
    ir::{ExprId, StatId},
    stats::StatementKind,
};
use crate::engine::{
    Cx, class_nodes::ClassNodeId, class_wrapper::MethodSlot, counter_container::CounterContainer,
};
use crate::kotlin::{
    declarations::KParameter,
    members::{DefaultArguments, KConstructor, MethodElement},
    writer::annotations,
};
use crate::structs::{StructMember, StructMethod, attr::StructLocalVariableTableAttribute};
use crate::types::MethodDescriptor;
use crate::util::{interpreter_util::make_unique_key, text_buffer::TextBuffer};

#[derive(Clone)]
enum DefaultValue {
    Expression(ExprId),
    Annotation(annotations::DefaultValue),
}

/// DefaultArgsMap. Entries follow the Kotlin parameter order after recovering
/// the wrapper's mask indexes or the annotation methods' named defaults.
pub struct DefaultArgsMap {
    values: Vec<Option<DefaultValue>>,
}

impl DefaultArgsMap {
    pub(super) fn for_method(
        cx: &mut Cx,
        node: ClassNodeId,
        method: &StructMethod,
        params: &[KParameter],
        defaults: &DefaultArguments,
    ) -> io::Result<Self> {
        let mut map = Self {
            values: vec![None; params.len()],
        };
        let DefaultArguments::Method { name, descriptor } = defaults else {
            return Err(invalid("Expected a Kotlin default argument wrapper"));
        };
        let Some(defaults) = MethodSlot::by_key(cx, node, &make_unique_key(name, descriptor))
        else {
            return Ok(map);
        };
        let calling = method_slot(cx, node, method)?;
        let method = calling.get(cx).method.clone();
        let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
        let masks_start = i32::from(!method.has_modifier(ACC_STATIC))
            + descriptor
                .params
                .iter()
                .map(|ty| ty.stack_size)
                .sum::<i32>();
        if defaults.get(cx).root().is_none() {
            return Err(invalid(
                "Kotlin default argument wrapper has no method tree",
            ));
        }
        let graph = cx.wrapper_graph(defaults);
        let statements: Vec<_> = graph.order.iter().map(|&node| graph[node].stat).collect();
        for stat in statements {
            if let Some((index, value)) = read_mask_check(cx, stat, masks_start)? {
                let mut counters = CounterContainer::with_expression_ids(cx.expression_ids.clone());
                let copied = Expr::copy(cx, &mut counters, value);
                if let Some(table) = method.get_local_variable_attr() {
                    apply_calling_locals(cx, table, copied);
                }
                let parameter = params.get(index).ok_or_else(|| {
                    invalid(format!(
                        "Kotlin default argument index {index} is outside the parameter list"
                    ))
                })?;
                map.insert(params, parameter, DefaultValue::Expression(copied));
            }
        }
        Ok(map)
    }

    pub fn for_constructor(
        cx: &mut Cx,
        node: ClassNodeId,
        constructor: &KConstructor,
    ) -> io::Result<Self> {
        match &constructor.defaults {
            DefaultArguments::Method { .. } => {
                let method = constructor
                    .method
                    .as_deref()
                    .ok_or_else(|| invalid("Kotlin constructor has no method"))?;
                Self::for_method(
                    cx,
                    node,
                    method,
                    &constructor.parameters,
                    &constructor.defaults,
                )
            }
            DefaultArguments::Annotation => Self::from_annotation(cx, constructor),
        }
    }

    fn from_annotation(cx: &mut Cx, constructor: &KConstructor) -> io::Result<Self> {
        let mut map = Self {
            values: vec![None; constructor.parameters.len()],
        };
        let Some(members) = &cx.kotlin_members else {
            return Ok(map);
        };
        let mut defaults = std::collections::BTreeMap::new();
        for method in members.methods(&constructor.class) {
            if let Some(MethodElement::Property(property)) = members.method(method)
                && let Some(default) = &method.attributes.annotation_default
                && defaults
                    .insert(property.name.clone(), default.default_value.value.clone())
                    .is_some()
            {
                return Err(invalid(format!(
                    "Duplicate Kotlin annotation default for {}",
                    property.name
                )));
            }
        }
        for parameter in &constructor.parameters {
            if let Some(value) = defaults.get(&parameter.name) {
                let value = annotations::DefaultValue::from_element(cx, value);
                map.insert(
                    &constructor.parameters,
                    parameter,
                    DefaultValue::Annotation(value),
                );
            }
        }
        Ok(map)
    }

    fn insert(&mut self, params: &[KParameter], key: &KParameter, value: DefaultValue) {
        // Java's KParameter is a record. KType inherits VarType.equals.
        for (index, parameter) in params.iter().enumerate() {
            if parameter.name == key.name
                && parameter.flags == key.flags
                && parameter.type_id == key.type_id
                && parameter.ty.jvm == key.ty.jvm
                && parameter.vararg_type.as_ref().map(|ty| &ty.jvm)
                    == key.vararg_type.as_ref().map(|ty| &ty.jvm)
            {
                self.values[index] = Some(value.clone());
            }
        }
    }

    pub fn render_parameter(
        &self,
        cx: &mut Cx,
        index: usize,
        indent: i32,
    ) -> io::Result<TextBuffer> {
        let mut buffer = TextBuffer::new(cx);
        let value = self
            .values
            .get(index)
            .ok_or_else(|| invalid("Invalid Kotlin parameter index"))?;
        match value {
            Some(DefaultValue::Expression(expr)) => {
                buffer
                    .append(" = ")
                    .append_buffer(&write::to_java(cx, *expr, indent)?);
            }
            Some(DefaultValue::Annotation(value)) => {
                buffer
                    .append(" = ")
                    .append_buffer(&value.render(cx, indent)?);
            }
            None if !cx.options.kt_unknown_defaults.is_empty() => {
                buffer.append(" = ").append(&cx.options.kt_unknown_defaults);
            }
            None => {}
        }
        Ok(buffer)
    }
}

fn read_mask_check(cx: &Cx, stat: StatId, masks_start: i32) -> io::Result<Option<(usize, ExprId)>> {
    let ir = &cx.ir;
    let StatementKind::If(branch) = ir[stat].kind else {
        return Ok(None);
    };
    let condition = branch
        .head_exprents
        .and_then(|list| ir[list].first().copied());
    let Some(condition) = condition else {
        return Err(invalid("Kotlin default argument check has no condition"));
    };
    let ExprKind::If { condition } = ir[condition].kind else {
        return Err(invalid(
            "Kotlin default argument condition is not an If expression",
        ));
    };
    let ExprKind::Function { operands, .. } = &ir[condition].kind else {
        return Ok(None);
    };
    let Some(&bitmask) = operands.first() else {
        return Err(invalid("Kotlin default argument check has no operand"));
    };
    let ExprKind::Function { operands, .. } = &ir[bitmask].kind else {
        return Ok(None);
    };
    let &[check, mask] = operands.as_slice() else {
        return Ok(None);
    };
    let Some(var) = Expr::variable(ir, check) else {
        return Ok(None);
    };
    let ExprKind::Constant { value, .. } = &ir[mask].kind else {
        return Ok(None);
    };
    let ConstantValue::Integer(mask) = value else {
        return Err(invalid("Kotlin default argument bitmask is not an integer"));
    };
    let block = branch
        .if_stat
        .and_then(|stat| ir[stat].exprents)
        .ok_or_else(|| invalid("Kotlin default argument check has no assignment block"))?;
    let expr = *ir[block]
        .first()
        .ok_or_else(|| invalid("Kotlin default argument block is empty"))?;
    let ExprKind::Assignment { right, .. } = ir[expr].kind else {
        return Ok(None);
    };
    let bit = if *mask == 0 {
        0
    } else {
        mask.trailing_zeros() as i32
    };
    let index = var
        .index
        .wrapping_sub(masks_start)
        .wrapping_mul(32)
        .wrapping_add(bit);
    Ok(Some((index as usize, right)))
}

fn apply_calling_locals(cx: &mut Cx, table: &StructLocalVariableTableAttribute, expr: ExprId) {
    if let Some(local) =
        Expr::variable(&cx.ir, expr).and_then(|var| table.get_variable_at_start(var.index, 0))
    {
        Expr::set_local_variable(&mut cx.ir, expr, local);
    }
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for child in children {
        apply_calling_locals(cx, table, child);
    }
}
