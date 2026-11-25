// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The pattern language used by Vineflower's built-in statement and expression passes.
//! Compile each description once. Captures belong to an individual match.

use rustc_hash::FxHashMap;

use crate::decompiler::exps::{ConstantValue, ExitType, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::types::VarType;

#[derive(Clone, Copy)]
pub(crate) enum Object {
    Statement(StatId),
    Expression(ExprId),
}

pub(crate) enum Capture {
    Object(Object),
    Value(ConstantValue),
}

#[derive(Default)]
pub(crate) struct Captures(FxHashMap<&'static str, Capture>);

impl Captures {
    pub fn get(&self, name: &str) -> Option<&Capture> {
        self.0.get(name)
    }

    fn bind(&mut self, cx: &Cx, name: &'static str, value: Capture) -> bool {
        use Capture::{Object as Node, Value};
        match (self.0.get(name), &value) {
            (None | Some(Value(ConstantValue::Null)), _) => {
                self.0.insert(name, value);
                true
            }
            (Some(Value(a)), Value(b)) => a == b,
            (Some(Node(Object::Statement(a))), Node(Object::Statement(b))) => a == b,
            (Some(Node(Object::Expression(a))), Node(Object::Expression(b))) => {
                Expr::equals(cx, *a, *b)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Default)]
enum Position {
    #[default]
    Next,
    Head,
    Index(isize),
}

impl Position {
    fn select(self, index: usize, size: usize) -> Option<usize> {
        match self {
            Self::Next => (index < size).then_some(index),
            Self::Index(value) if size > 0 => {
                usize::try_from((size as isize + value) % size as isize).ok()
            }
            _ => None,
        }
    }
}

enum Rule {
    Type(&'static str),
    Capture(&'static str),
    Statements(usize),
    Expressions(isize),
    IfElse(bool),
    Function(FunctionType),
    Exit(ExitType),
    ConstType(VarType),
    Value(&'static str),
    Owner(&'static str),
    Signature(&'static str),
    Parameter(usize, &'static str),
    Index(&'static str),
    Name(&'static str),
}

struct Pattern {
    statement: bool,
    position: Position,
    rules: Vec<Rule>,
    children: Vec<usize>,
}

pub(crate) struct Matcher(Vec<Pattern>);

impl Matcher {
    pub fn new(lines: &[&'static str]) -> Self {
        let mut nodes = Vec::<Pattern>::new();
        let mut parents = Vec::<usize>::new();
        for line in lines {
            let depth = line.len() - line.trim_start_matches(' ').len();
            parents.truncate(depth);
            let index = nodes.len();
            if let Some(&parent) = parents.last() {
                nodes[parent].children.push(index);
            }
            let mut words = line.split_ascii_whitespace();
            let mut node = Pattern {
                statement: words.next() == Some("statement"),
                position: Position::Next,
                rules: Vec::new(),
                children: Vec::new(),
            };
            for word in words {
                let (key, value) = word.split_once(':').expect("missing match property value");
                node.rules.push(match key {
                    "type" => Rule::Type(value),
                    "ret" => Rule::Capture(value),
                    "statsize" => Rule::Statements(value.parse().unwrap()),
                    "exprsize" => Rule::Expressions(value.parse().unwrap()),
                    "iftype" => Rule::IfElse(value == "ifelse"),
                    "functype" => Rule::Function(match value {
                        "eq" => FunctionType::Eq,
                        "neq" => FunctionType::Ne,
                        "ternary" => FunctionType::Ternary,
                        _ => panic!("unknown match function {value}"),
                    }),
                    "exittype" => Rule::Exit(match value {
                        "return" => ExitType::Return,
                        "throw" => ExitType::Throw,
                        _ => panic!("unknown match exit {value}"),
                    }),
                    "consttype" => Rule::ConstType(match value {
                        "null" => VarType::VARTYPE_NULL,
                        "string" => VarType::VARTYPE_STRING,
                        _ => panic!("unknown match constant type {value}"),
                    }),
                    "constvalue" => Rule::Value(value),
                    "invclass" => Rule::Owner(value),
                    "signature" => Rule::Signature(value),
                    "name" => Rule::Name(value),
                    "index" => Rule::Index(value),
                    "parameter" => {
                        let (index, name) = value.split_once(':').unwrap();
                        Rule::Parameter(index.parse().unwrap(), name)
                    }
                    "position" => {
                        node.position = if value == "head" {
                            Position::Head
                        } else {
                            Position::Index(value.parse().unwrap())
                        };
                        continue;
                    }
                    _ => panic!("unknown match property {key}"),
                });
            }
            parents.push(index);
            nodes.push(node);
        }
        Self(nodes)
    }

    pub fn matches(&self, cx: &Cx, object: Object) -> Option<Captures> {
        let mut captures = Captures::default();
        self.visit(cx, 0, object, &mut captures).then_some(captures)
    }

    fn visit(&self, cx: &Cx, node: usize, object: Object, captures: &mut Captures) -> bool {
        let pattern = &self.0[node];
        if pattern.statement != matches!(object, Object::Statement(_))
            || !pattern
                .rules
                .iter()
                .all(|rule| rule.matches(cx, object, captures))
        {
            return false;
        }
        // Statements and expressions advance independent child positions.
        let mut indices = [0, 0];
        pattern.children.iter().all(|&child| {
            let child_pattern = &self.0[child];
            let index = &mut indices[usize::from(child_pattern.statement)];
            let value = child_pattern.find(&cx.ir, object, *index);
            *index += 1;
            value.is_some_and(|value| self.visit(cx, child, value, captures))
        })
    }
}

impl Pattern {
    fn find(&self, ir: &Ir, parent: Object, index: usize) -> Option<Object> {
        match parent {
            Object::Statement(stat) if self.statement => {
                let children = &ir[stat].stats;
                self.position
                    .select(index, children.len())
                    .map(|i| Object::Statement(children[i]))
            }
            Object::Statement(stat) if matches!(self.position, Position::Head) => {
                let StatementKind::If(branch) = ir[stat].kind else {
                    return None;
                };
                ir[branch.head_exprents?]
                    .first()
                    .copied()
                    .map(Object::Expression)
            }
            Object::Statement(stat) => {
                let expressions = &ir[ir[stat].exprents?];
                self.position
                    .select(index, expressions.len())
                    .map(|i| Object::Expression(expressions[i]))
            }
            Object::Expression(expr) if !self.statement => {
                let mut children = Expr::children(ir, expr);
                let selected = match self.position {
                    Position::Next => index,
                    position => position.select(index, Expr::children(ir, expr).count())?,
                };
                children.nth(selected).map(Object::Expression)
            }
            Object::Expression(_) => None,
        }
    }
}

fn variable(value: &str) -> bool {
    value.starts_with('$') && value.ends_with('$')
}

impl Rule {
    fn matches(&self, cx: &Cx, object: Object, captures: &mut Captures) -> bool {
        if let Self::Capture(name) = self {
            return captures.bind(cx, name, Capture::Object(object));
        }
        match object {
            Object::Statement(id) => {
                let stat = &cx.ir[id];
                match self {
                    Self::Type(name) => matches!(
                        (*name, &stat.kind),
                        ("if", StatementKind::If(_))
                            | ("do", StatementKind::Do)
                            | ("switch", StatementKind::Switch(_))
                            | ("trycatch", StatementKind::Catch { .. })
                            | ("basicblock", StatementKind::BasicBlock { .. })
                            | ("sequence", StatementKind::Sequence)
                    ),
                    Self::Statements(size) => stat.stats.len() == *size,
                    Self::Expressions(size) => {
                        stat.exprents.map_or(-1, |list| cx.ir[list].len() as isize) == *size
                    }
                    Self::IfElse(has_else) => {
                        !matches!(stat.kind, StatementKind::If(branch) if branch.has_else != *has_else)
                    }
                    _ => true,
                }
            }
            Object::Expression(id) => {
                let kind = &cx.ir[id].kind;
                match (self, kind) {
                    (Self::Type(name), kind) => matches!(
                        (*name, kind),
                        ("array", ExprKind::Array { .. })
                            | ("assignment", ExprKind::Assignment { .. })
                            | ("constant", ExprKind::Constant { .. })
                            | ("exit", ExprKind::Exit { .. })
                            | ("field", ExprKind::Field(_))
                            | ("function", ExprKind::Function { .. })
                            | ("if", ExprKind::If { .. })
                            | ("invocation", ExprKind::Invocation(_))
                            | ("monitor", ExprKind::Monitor { .. })
                            | ("new", ExprKind::New { .. })
                            | ("switchhead", ExprKind::SwitchHead { .. })
                            | ("var", ExprKind::Variable(_))
                    ),
                    (Self::Function(expected), ExprKind::Function { op, .. }) => op == expected,
                    (Self::Exit(expected), ExprKind::Exit { kind, .. }) => kind == expected,
                    (Self::ConstType(expected), ExprKind::Constant { var_type, .. }) => {
                        var_type == expected
                    }
                    (Self::Value(name), ExprKind::Constant { value, .. }) => {
                        !variable(name) || captures.bind(cx, name, Capture::Value(value.clone()))
                    }
                    (Self::Owner(owner), ExprKind::Invocation(inv)) => {
                        inv.classname.as_deref() == Some(owner)
                    }
                    (Self::Signature(sig), ExprKind::Invocation(inv)) => {
                        sig.strip_prefix(inv.name.as_str()) == Some(inv.descriptor.as_str())
                    }
                    (Self::Parameter(i, name), ExprKind::Invocation(inv)) => {
                        !variable(name)
                            || inv.parameters.get(*i).is_some_and(|&expr| {
                                captures.bind(cx, name, Capture::Object(Object::Expression(expr)))
                            })
                    }
                    (Self::Name(name), ExprKind::Invocation(inv)) => inv.name == *name,
                    (Self::Name(name), ExprKind::Field(field)) if variable(name) => captures.bind(
                        cx,
                        name,
                        Capture::Value(ConstantValue::String(field.name.clone().into())),
                    ),
                    (Self::Name(name), ExprKind::Field(field)) => field.name == *name,
                    (Self::Index(name), ExprKind::Variable(var)) if variable(name) => {
                        captures.bind(cx, name, Capture::Value(ConstantValue::Integer(var.index)))
                    }
                    (Self::Index(value), ExprKind::Variable(var)) => {
                        value.parse::<i32>() == Ok(var.index)
                    }
                    _ => true,
                }
            }
        }
    }
}
