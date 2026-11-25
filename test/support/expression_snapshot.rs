// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::fmt::Write;

use itertools::Itertools;
use vineflower_rs::code::instruction::Instruction;
use vineflower_rs::decompiler::exps::{Expr, ExprKind, FunctionType, SwitchCaseValues};
use vineflower_rs::decompiler::ir::{ExprId, ExprListId, StatId};
use vineflower_rs::decompiler::stats::{LoopType, StatementKind, SwitchCase};
use vineflower_rs::engine::Cx;
use vineflower_rs::engine::counter_container::{
    CounterContainer, EXPRESSION_COUNTER, STATEMENT_COUNTER, VAR_COUNTER,
};
use vineflower_rs::structs::attr::LocalVariable;
use vineflower_rs::structs::consts::{ConstantValue, LinkConstant, PooledConstant};
use vineflower_rs::types::{MethodDescriptor, VarType};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Detail {
    Base,
    LoopHeaders,
    SecondaryFunctions,
    IntersectionCasts,
    Switches,
    Resources,
    AfterMain,
    VariableDefinitions,
}

pub fn snapshot(cx: &Cx, root: StatId, counters: &CounterContainer) -> String {
    snapshot_details(cx, root, counters, Detail::Base)
}

pub fn snapshot_details(
    cx: &Cx,
    root: StatId,
    counters: &CounterContainer,
    detail: Detail,
) -> String {
    let ir = &cx.ir;
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!();
    };
    let mut pending = vec![dummy_exit, root];
    let mut snapshot = Snapshot {
        cx,
        root,
        nodes: BTreeMap::new(),
        detail,
    };
    let mut fields = vec![format!(
        "counters={},{},{}",
        counters.get_counter(STATEMENT_COUNTER),
        counters.get_counter(EXPRESSION_COUNTER),
        counters.get_counter(VAR_COUNTER)
    )];
    while let Some(stat) = pending.pop() {
        let statement = &ir[stat];
        let id = statement.id;
        fields.push(format!("body{id}={}", snapshot.list(statement.exprents)));
        if detail >= Detail::LoopHeaders {
            fields.push(format!(
                "definitions{id}={}",
                snapshot.expressions(&statement.var_definitions)
            ));
        }
        match &statement.kind {
            StatementKind::Do(loop_) if detail >= Detail::LoopHeaders => {
                fields.push(format!(
                    "loop{id}={},{},{}",
                    snapshot.expression(loop_.init(ir)),
                    snapshot.expression(loop_.condition(ir)),
                    snapshot.expression(loop_.increment(ir))
                ));
                if loop_.ty == LoopType::ForEach {
                    let source = if Expr::expr_type(cx, loop_.increment(ir).unwrap()).array_dim > 0
                    {
                        "array"
                    } else {
                        "iterator"
                    };
                    fields.push(format!("foreach{id}={source}"));
                }
            }
            StatementKind::If(branch) => {
                fields.push(format!("head{id}={}", snapshot.list(branch.head_exprents)));
                fields.push(format!("pattern{id}={}", branch.pattern_matched));
                fields.push(format!("ppmm{id}={}", branch.has_ppmm));
            }
            StatementKind::Switch(branch) => {
                fields.push(format!("head{id}={}", snapshot.list(branch.head_exprents)));
                let linked = branch
                    .head_exprents
                    .and_then(|list| ir[list].first())
                    .is_some_and(|&head| {
                        matches!(&ir[head].kind, ExprKind::SwitchHead {
                            case_values: Some(SwitchCaseValues::Statement(owner)), ..
                        } if *owner == stat)
                    });
                fields.push(format!(
                    "cases{id}={}|{linked}",
                    snapshot.cases(&branch.cases)
                ));
                if detail >= Detail::Switches {
                    let guards = branch
                        .case_guards
                        .iter()
                        .map(|&expr| snapshot.expression(expr))
                        .join(",");
                    fields.push(format!("guards{id}={guards}"));
                }
                if detail == Detail::VariableDefinitions {
                    let scoped = branch
                        .scoped_case_statements
                        .iter()
                        .map(|&case| ir[case].id)
                        .sorted_unstable()
                        .join(",");
                    fields.push(format!("scoped-cases{id}={scoped}"));
                }
            }
            StatementKind::Synchronized { head_exprents, .. } => {
                fields.push(format!("head{id}={}", snapshot.list(*head_exprents)));
            }
            StatementKind::Catch {
                vars, resources, ..
            } => {
                fields.push(format!("catch{id}={}", snapshot.expressions(vars)));
                if detail >= Detail::Resources {
                    let resources = resources.map_or(&[][..], |list| ir[list].as_slice());
                    fields.push(format!("resources{id}={}", snapshot.expressions(resources)));
                }
            }
            StatementKind::CatchAll { vars, monitor, .. } => {
                fields.push(format!(
                    "catch{id}={}|{}",
                    snapshot.expressions(vars),
                    snapshot.expression(*monitor)
                ));
            }
            StatementKind::DummyExit { bytecode } if detail >= Detail::AfterMain => {
                let offsets = bytecode
                    .as_ref()
                    .map_or_else(|| "~".to_owned(), |set| set.iter().join(","));
                fields.push(format!("exit-offsets{id}={offsets}"));
            }
            _ => {}
        }
        pending.extend(statement.stats.iter().rev().copied());
    }
    fields.extend(snapshot.nodes.into_values().map(|(_, snapshot)| snapshot));
    fields.join(";")
}

struct Snapshot<'a> {
    cx: &'a Cx,
    root: StatId,
    nodes: BTreeMap<i32, (ExprId, String)>,
    detail: Detail,
}

impl Snapshot<'_> {
    fn list(&mut self, list: Option<ExprListId>) -> String {
        let ir = &self.cx.ir;
        list.map_or_else(|| "~".into(), |list| self.expressions(&ir[list]))
    }

    fn expressions(&mut self, exprs: &[ExprId]) -> String {
        exprs
            .iter()
            .map(|&expr| self.expression(Some(expr)))
            .join(",")
    }

    fn cases(&mut self, cases: &[SwitchCase]) -> String {
        self.case_values(cases.iter().map(|case| case.values.as_slice()))
    }

    fn case_values<'a>(&mut self, cases: impl IntoIterator<Item = &'a [Option<ExprId>]>) -> String {
        let rows = cases
            .into_iter()
            .map(|row| row.iter().map(|&expr| self.expression(expr)).join(","))
            .join("/");
        format!("[{rows}]")
    }

    fn expression(&mut self, expr: Option<ExprId>) -> String {
        let Some(expr) = expr else {
            return "~".into();
        };
        let node = &self.cx.ir[expr];
        let id = node.id;
        if let Some((previous, _)) = self.nodes.get(&id) {
            assert_eq!(*previous, expr, "duplicate expression ID {id}");
            return id.to_string();
        }

        self.nodes.insert(id, (expr, String::new()));
        let (kind, operands) = self.operands(&node.kind);
        let ty = var_type(Some(&Expr::expr_type(self.cx, expr)));
        let offsets = node
            .bytecode
            .as_ref()
            .map_or_else(|| "~".into(), |offsets| offsets.iter().join(","));
        self.nodes.get_mut(&id).unwrap().1 = format!("e{id}={kind}|{ty}|{offsets}|{operands}");
        id.to_string()
    }

    fn operands(&mut self, kind: &ExprKind) -> (&'static str, String) {
        let ir = &self.cx.ir;
        match kind {
            ExprKind::Variable(var) => {
                let mut operands = format!(
                    "{}|{}|{}|{}|{}|{}|{}|{}",
                    var.index,
                    var.version,
                    var.stack,
                    var.catch_temp,
                    var_type(var.var_type.as_ref()),
                    local_variable(var.lvt.as_deref()),
                    instruction(var.backing_instruction.as_deref()),
                    var.effectively_final
                );
                if self.detail >= Detail::LoopHeaders {
                    write!(operands, "|{}", var_type(var.bound_type.as_deref())).unwrap();
                }
                if self.detail >= Detail::IntersectionCasts {
                    write!(operands, "|{}", var.intersection_type).unwrap();
                }
                if self.detail == Detail::VariableDefinitions {
                    write!(operands, "|{}", var.definition).unwrap();
                }
                ("VAR", operands)
            }
            ExprKind::Constant {
                value,
                bool_permitted,
                was_condy,
                ..
            } => (
                "CONST",
                format!("{}|{bool_permitted}|{was_condy}", constant_value(value)),
            ),
            ExprKind::Assignment {
                left,
                right,
                compound,
            } => (
                "ASSIGNMENT",
                format!(
                    "{}|{}|{}",
                    self.expression(Some(*left)),
                    self.expression(Some(*right)),
                    compound.map_or_else(|| "~".into(), function_name)
                ),
            ),
            ExprKind::Array {
                array,
                index,
                hard_type,
            } => (
                "ARRAY",
                format!(
                    "{}|{}|{}",
                    self.expression(Some(*array)),
                    self.expression(Some(*index)),
                    var_type(Some(hard_type))
                ),
            ),
            ExprKind::Field(field) => (
                "FIELD",
                format!(
                    "{}|{}|{}|{}|{}|{}|{}",
                    text(Some(&field.name)),
                    text(field.classname.as_deref()),
                    field.is_static(),
                    self.expression(field.instance),
                    text(Some(&field.descriptor.descriptor_string)),
                    field.force_qualified,
                    field.was_condy
                ),
            ),
            ExprKind::Invocation(invocation) => {
                let mut operands = format!(
                    "{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}",
                    enum_name(invocation.kind),
                    enum_name(invocation.function),
                    text(Some(&invocation.name)),
                    text(invocation.classname.as_deref()),
                    invocation.is_static,
                    self.expression(invocation.instance),
                    text(Some(invocation.string_descriptor())),
                    descriptor(&invocation.descriptor),
                    text(invocation.dynamic_class_suffix.as_deref()),
                    self.expressions(&invocation.parameters),
                    invocation
                        .bootstrap_method
                        .as_ref()
                        .map_or_else(|| "~".into(), link_constant),
                    invocation.bootstrap_arguments.as_ref().map_or_else(
                        || "~".into(),
                        |args| args.iter().map(|arg| constant(arg.as_ref())).join("/")
                    ),
                    invocation.synthetic_null_check,
                    invocation.was_lazy_condy
                );
                if self.detail >= Detail::SecondaryFunctions {
                    write!(operands, "|{}", invocation.force_boxing).unwrap();
                }
                if self.detail >= Detail::AfterMain {
                    write!(operands, "|{}", invocation.can_ignore_boxing).unwrap();
                }
                ("INVOCATION", operands)
            }
            ExprKind::Function {
                op,
                operands,
                implicit_type,
                needs_cast,
            } => {
                let mut operands = format!(
                    "{}|{}|{}",
                    function_name(*op),
                    self.expressions(operands),
                    var_type(implicit_type.as_deref()),
                );
                if self.detail >= Detail::SecondaryFunctions {
                    write!(operands, "|{needs_cast}").unwrap();
                }
                ("FUNCTION", operands)
            }
            ExprKind::Pattern(pattern) => (
                "PATTERN",
                format!(
                    "{}|{}|{}",
                    text(Some(&pattern.class.qualified_name)),
                    self.expressions(&pattern.children),
                    pattern
                        .bound_types
                        .iter()
                        .map(|bound| var_type(bound.as_ref()))
                        .join("/")
                ),
            ),
            ExprKind::Switch {
                backing,
                fallthrough,
                standalone,
                ..
            } => (
                "SWITCH",
                format!(
                    "{}|{}|{fallthrough}|{standalone}",
                    ir[*backing].id,
                    super::structure_statements(ir, self.root).any(|stat| stat == *backing),
                ),
            ),
            ExprKind::Yield { value, .. } => ("YIELD", self.expression(Some(*value))),
            ExprKind::New {
                new_type,
                dimensions,
                constructor,
                array_elements,
                anonymous,
                lambda,
                method_reference,
                direct_array_init,
            } => (
                "NEW",
                format!(
                    "{}|{}|{}|{}|{anonymous}|{lambda}|{method_reference}|{direct_array_init}",
                    var_type(Some(new_type)),
                    self.expressions(dimensions),
                    self.expression(*constructor),
                    self.expressions(array_elements)
                ),
            ),
            ExprKind::Exit {
                kind,
                value,
                return_type,
                method_descriptor,
            } => (
                "EXIT",
                format!(
                    "{}|{}|{}|{}",
                    enum_name(kind),
                    self.expression(*value),
                    var_type(return_type.as_ref()),
                    descriptor(method_descriptor)
                ),
            ),
            ExprKind::Assert { condition, message } => (
                "ASSERT",
                format!(
                    "{}|{}",
                    self.expression(*condition),
                    self.expression(*message)
                ),
            ),
            ExprKind::Monitor {
                kind,
                value,
                remove,
            } => (
                "MONITOR",
                format!(
                    "{}|{}|{remove}",
                    enum_name(kind),
                    self.expression(Some(*value))
                ),
            ),
            ExprKind::If { condition } => ("IF", self.expression(Some(*condition))),
            ExprKind::SwitchHead { value, case_values } => {
                let cases = match case_values {
                    None => "[]".into(),
                    Some(SwitchCaseValues::Statement(stat)) => {
                        let StatementKind::Switch(branch) = &ir[*stat].kind else {
                            panic!("switch expression has a non-switch owner");
                        };
                        self.cases(&branch.cases)
                    }
                    Some(SwitchCaseValues::Copied(cases)) => {
                        self.case_values(cases.iter().map(Vec::as_slice))
                    }
                };
                (
                    "SWITCH_HEAD",
                    format!("{}|{cases}", self.expression(Some(*value))),
                )
            }
        }
    }
}

fn enum_name(value: impl std::fmt::Debug) -> String {
    let name = format!("{value:?}");
    match name.as_str() {
        "ConstantDynamic" => "CONSTANT_DYNAMIC".into(),
        _ => name.to_ascii_uppercase(),
    }
}

fn function_name(op: FunctionType) -> String {
    match op {
        FunctionType::ArrayLength => "ARRAY_LENGTH".into(),
        FunctionType::BitNot => "BIT_NOT".into(),
        FunctionType::BoolNot => "BOOL_NOT".into(),
        FunctionType::BoolAnd => "BOOLEAN_AND".into(),
        FunctionType::BoolOr => "BOOLEAN_OR".into(),
        FunctionType::StrConcat => "STR_CONCAT".into(),
        _ => enum_name(op),
    }
}

pub(super) fn var_type(ty: Option<&VarType>) -> String {
    let Some(ty) = ty else {
        return "~".into();
    };
    let mut base = format!(
        "{},{},{},{},{}",
        ty.ty.ordinal(),
        ty.array_dim,
        text(ty.value.as_deref()),
        ty.type_family as u8,
        ty.stack_size
    );
    if ty.is_generic_type() {
        write!(
            base,
            "<{},{},{}>",
            ty.wildcard(),
            var_type(ty.parent()),
            ty.arguments()
                .iter()
                .map(|arg| var_type(arg.as_ref()))
                .join("/")
        )
        .unwrap();
    }
    base
}

fn descriptor(descriptor: &MethodDescriptor) -> String {
    let generic = descriptor.generic_info.as_ref().map_or_else(
        || "~".into(),
        |generic| {
            let generic = generic.get();
            format!(
                "{}@{}@{}@{}@{}",
                generic
                    .type_parameters
                    .iter()
                    .map(|name| text(Some(name)))
                    .join("/"),
                generic
                    .type_parameter_bounds
                    .iter()
                    .map(|bounds| types(bounds))
                    .join("|"),
                types(&generic.parameter_types),
                var_type(Some(&generic.return_type)),
                types(&generic.exception_types),
            )
        },
    );
    format!(
        "{}@{}@{}@{generic}",
        text(Some(&descriptor.to_string())),
        var_type(Some(&descriptor.ret)),
        types(&descriptor.params),
    )
}

fn types(types: &[VarType]) -> String {
    types.iter().map(|ty| var_type(Some(ty))).join("/")
}

pub(super) fn local_variable(local: Option<&LocalVariable>) -> String {
    local.map_or_else(
        || "~".into(),
        |local| {
            format!(
                "{},{},{},{},{},{},{}",
                local.get_version().var,
                local.get_version().version,
                local.get_start(),
                local.get_end(),
                text(Some(local.get_name())),
                text(Some(local.get_descriptor())),
                text(local.get_signature().map(AsRef::as_ref))
            )
        },
    )
}

fn instruction(insn: Option<&Instruction>) -> String {
    insn.map_or_else(
        || "~".into(),
        |insn| {
            format!(
                "{},{},{},{},{},{}",
                insn.opcode,
                insn.wide,
                insn.group,
                insn.start_offset,
                insn.length,
                (0..insn.operands_count())
                    .map(|index| insn.operand(index))
                    .join(",")
            )
        },
    )
}

fn constant(constant: Option<&PooledConstant>) -> String {
    match constant {
        None => "~".into(),
        Some(PooledConstant::Primitive(primitive)) => format!(
            "p,{},{},{},{}",
            primitive.ty,
            primitive.index,
            primitive.is_array,
            constant_value(&primitive.value)
        ),
        Some(PooledConstant::Link(link)) => link_constant(link),
    }
}

fn link_constant(link: &LinkConstant) -> String {
    format!(
        "l,{},{},{},{},{},{}",
        link.ty,
        link.index1,
        link.index2,
        text(link.classname.as_deref()),
        text(Some(&link.elementname)),
        text(Some(&link.descriptor))
    )
}

fn constant_value(value: &ConstantValue) -> String {
    match value {
        ConstantValue::Null => "~".into(),
        ConstantValue::Integer(value) => format!("i{value}"),
        ConstantValue::Long(value) => format!("j{value}"),
        ConstantValue::Float(value) => format!("f{:x}", value.to_bits()),
        ConstantValue::Double(value) => format!("d{:x}", value.to_bits()),
        ConstantValue::String(value) => format!("s{}", utf16(value.utf16())),
    }
}

pub(super) fn text(value: Option<&str>) -> String {
    value.map_or_else(|| "~".into(), |value| utf16(value.encode_utf16()))
}

fn utf16(value: impl Iterator<Item = u16>) -> String {
    let mut escaped = String::new();
    for ch in value {
        if !(0x20..=0x7e).contains(&ch) || b"|;,/%~@<>".contains(&(ch as u8)) {
            write!(escaped, "%{ch:04x}").unwrap();
        } else {
            escaped.push(char::from(ch as u8));
        }
    }
    escaped
}
