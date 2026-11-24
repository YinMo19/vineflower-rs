use super::super::{
    ContractConstant, ContractEffect, ContractExpression, ContractReference, Function,
    InvocationKind, KotlinError, syntax::{Types, identifier},
};

pub(super) fn write(
    out: &mut String,
    function: &Function,
    types: &Types<'_>,
    indent: &str,
    unit: &str,
) -> Result<usize, KotlinError> {
    if function.contract.is_empty() {
        return Ok(0);
    }
    out.push_str(indent);
    out.push_str(unit);
    out.push_str("kotlin.contracts.contract {\n");
    for effect in &function.contract {
        out.push_str(indent);
        out.push_str(unit);
        out.push_str(unit);
        let implies = match effect {
            ContractEffect::Returns { value, implies } => {
                out.push_str("returns(");
                if let Some(value) = value {
                    out.push_str(constant(*value));
                }
                out.push(')');
                implies.as_ref()
            }
            ContractEffect::ReturnsNotNull { implies } => {
                out.push_str("returnsNotNull()");
                implies.as_ref()
            }
            ContractEffect::CallsInPlace { parameter, kind } => {
                out.push_str("callsInPlace(");
                reference(out, function, ContractReference::Parameter(*parameter))?;
                if let Some(kind) = kind {
                    out.push_str(", kotlin.contracts.InvocationKind.");
                    out.push_str(match kind {
                        InvocationKind::AtMostOnce => "AT_MOST_ONCE",
                        InvocationKind::ExactlyOnce => "EXACTLY_ONCE",
                        InvocationKind::AtLeastOnce => "AT_LEAST_ONCE",
                    });
                }
                out.push(')');
                None
            }
        };
        if let Some(condition) = implies {
            out.push_str(" implies (");
            expression(out, function, types, condition)?;
            out.push(')');
        }
        out.push('\n');
    }
    out.push_str(indent);
    out.push_str(unit);
    out.push_str("}\n");
    Ok(function.contract.len() + 2)
}

fn constant(value: ContractConstant) -> &'static str {
    match value {
        ContractConstant::True => "true",
        ContractConstant::False => "false",
        ContractConstant::Null => "null",
    }
}

fn reference(out: &mut String, function: &Function, reference: ContractReference) -> Result<(), KotlinError> {
    match reference {
        ContractReference::Receiver => {
            out.push_str("this@");
            identifier(out, &function.name, &function.name)
        }
        ContractReference::Parameter(index) => identifier(out, &function.parameters[index].name, &function.name),
    }
}

fn expression(
    out: &mut String, function: &Function, types: &Types<'_>, condition: &ContractExpression,
) -> Result<(), KotlinError> {
    use ContractExpression::*;
    match condition {
        Constant(value) => out.push_str(constant(*value)),
        Boolean { reference: variable, negated } => {
            if *negated { out.push('!'); }
            reference(out, function, *variable)?;
        }
        IsNull { reference: variable, negated } => {
            reference(out, function, *variable)?;
            out.push_str(if *negated { " != null" } else { " == null" });
        }
        IsInstance { reference: variable, ty, negated } => {
            reference(out, function, *variable)?;
            out.push_str(if *negated { " !is " } else { " is " });
            types.write(out, ty)?;
        }
        All(terms) | Any(terms) => {
            let operator = if matches!(condition, All(_)) { " && " } else { " || " };
            out.push('(');
            for (index, term) in terms.iter().enumerate() {
                if index != 0 { out.push_str(operator); }
                expression(out, function, types, term)?;
            }
            out.push(')');
        }
    }
    Ok(())
}
