//! Kotlin's late replacements and its method-body objects. The arena holds
//! actual replacements, including fresh counters and redirected statement
//! edges. Kotlin-only subclass state is keyed by those replacement handles.

mod allocation;
mod expression;
mod loops;
mod passes;
mod statement;

use std::io;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::decompiler::exps::{Expr, ExprKind};
use crate::decompiler::ir::{ExprId, IrNode, StatId};
use crate::engine::{Cx, method_processor::ExpressionMethod};
use crate::types::{CodeType, VarType};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Declaration {
    Definition,
    Usage,
    ForLoopVariable,
    Exception,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum KotlinFunction {
    IdentityEquals,
    Elvis,
    GetKClass,
    StringTemplate,
}

#[derive(Clone, Debug)]
pub(crate) enum InvocationStyle {
    Property {
        name: String,
        method: Option<crate::kotlin::members::PropertyMethod>,
    },
    Infix {
        name: String,
        extension: bool,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum KotlinExpr {
    Constant { unsigned: Option<CodeType> },
    Variable(Declaration),
    Function(Option<KotlinFunction>),
    Invocation(Option<InvocationStyle>),
    Field,
    SwitchHead,
    New { in_annotation: bool },
    Exit { lambda_name: Option<String> },
}

/// Language-specific state follows the lifetime of the IR node used as its key.
#[derive(Default)]
pub(crate) struct KotlinBody {
    statements: FxHashSet<StatId>,
    expressions: FxHashMap<ExprId, KotlinExpr>,
}

impl KotlinBody {
    pub(crate) fn retain_ir_nodes(&mut self, live: impl Fn(IrNode) -> bool) {
        self.statements.retain(|&stat| live(stat.into()));
        self.expressions.retain(|&expr, _| live(expr.into()));
    }
}

impl Cx {
    fn kotlin_body_mut(&mut self) -> &mut KotlinBody {
        self.kotlin_body.get_or_insert_with(Default::default)
    }

    pub(crate) fn kotlin_expr(&self, expr: ExprId) -> Option<&KotlinExpr> {
        self.kotlin_body.as_ref()?.expressions.get(&expr)
    }

    fn set_kotlin_expr(&mut self, expr: ExprId, kind: KotlinExpr) {
        self.kotlin_body_mut().expressions.insert(expr, kind);
    }
}

/// Run the Kotlin plugin's final passes after SetVarDefinitions.
pub fn prepare(cx: &mut Cx, method: &mut ExpressionMethod) -> io::Result<()> {
    let cx = &mut *cx.enter_method(&method.flow.counters);
    let root = method.root;
    let counters = &mut method.flow.counters;
    passes::replace_statements(cx, counters, root);
    passes::replace_expressions(cx, counters, root)?;
    passes::resugar(cx, counters, root)?;
    if cx.options.kt_collapse_string_concat {
        passes::collapse_string_concat(cx, root);
    }
    crate::decompiler::labels::finish::replace_continue_with_break(&mut cx.ir, root);
    Ok(())
}

pub(crate) fn function_type(cx: &Cx, expr: ExprId) -> Option<VarType> {
    let KotlinExpr::Function(Some(op)) = cx.kotlin_expr(expr)? else {
        return None;
    };
    Some(match op {
        KotlinFunction::IdentityEquals => VarType::VARTYPE_BOOLEAN,
        KotlinFunction::Elvis => {
            let ExprKind::Function { operands, .. } = &cx.ir[expr].kind else {
                unreachable!()
            };
            let lhs = Expr::expr_type(cx, operands[0]);
            let rhs = Expr::expr_type(cx, operands[1]);
            VarType::join(cx, &lhs, &rhs).unwrap_or(VarType::VARTYPE_OBJECT)
        }
        KotlinFunction::GetKClass => VarType::VARTYPE_CLASS,
        KotlinFunction::StringTemplate => VarType::VARTYPE_STRING,
    })
}

pub(crate) fn set_lambda_name(cx: &mut Cx, exit: ExprId, name: String) {
    let Some(KotlinExpr::Exit { lambda_name }) = cx
        .kotlin_body
        .as_mut()
        .and_then(|body| body.expressions.get_mut(&exit))
    else {
        unreachable!("Expected a Kotlin exit expression")
    };
    *lambda_name = Some(name);
}

pub fn set_in_annotation(cx: &mut Cx, expr: ExprId) {
    if let Some(KotlinExpr::New { in_annotation }) = cx
        .kotlin_body
        .as_mut()
        .and_then(|body| body.expressions.get_mut(&expr))
    {
        *in_annotation = true;
    }
}

/// Record a Kotlin unsigned constant type after translating metadata's JVM type.
pub fn set_unsigned_type(cx: &mut Cx, expr: ExprId, ty: CodeType) {
    if let Some(KotlinExpr::Constant { unsigned }) = cx
        .kotlin_body
        .as_mut()
        .and_then(|body| body.expressions.get_mut(&expr))
    {
        *unsigned = Some(ty);
    }
}

pub(crate) use expression::{precedence, write_expression};
pub(crate) use passes::copy_expression;

pub use statement::statement;
pub(crate) use statement::{is_kotlin_statement, write_statement};

pub use crate::decompiler::exps::write::to_java as expression;

/// Create the Kotlin wrapper for an expression supplied by a class writer.
pub fn replace_expression(cx: &mut Cx, expr: ExprId) -> io::Result<ExprId> {
    let mut counters = ambient_counters(cx);
    passes::wrap(cx, &mut counters, expr)
}

/// Allocate a Kotlin wrapper for a parsed scalar stored outside the IR.
pub(super) fn new_scalar(cx: &mut Cx, mut kind: ExprKind) -> ExprId {
    let wrapper = scalar_wrapper(&mut kind);
    let expr = Expr::new_ambient(cx, kind, None);
    cx.set_kotlin_expr(expr, wrapper);
    expr
}

fn scalar_wrapper(kind: &mut ExprKind) -> KotlinExpr {
    match kind {
        ExprKind::Constant { was_condy, .. } => {
            *was_condy = false;
            KotlinExpr::Constant { unsigned: None }
        }
        ExprKind::Field(field) => {
            field.force_qualified = false;
            field.was_condy = false;
            KotlinExpr::Field
        }
        _ => unreachable!("Expected a Kotlin scalar expression"),
    }
}

fn ambient_counters(cx: &Cx) -> crate::engine::counter_container::CounterContainer {
    crate::engine::counter_container::CounterContainer::with_expression_ids(
        cx.expression_ids.clone(),
    )
}

fn copy_ambient(cx: &mut Cx, expr: ExprId) -> ExprId {
    let mut counters = ambient_counters(cx);
    Expr::copy(cx, &mut counters, expr)
}
