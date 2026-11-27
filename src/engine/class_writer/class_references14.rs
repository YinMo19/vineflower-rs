//! Recover class literals emitted by pre-Java-5 compilers.

use std::io;
use std::sync::Once;

use indexmap::{IndexMap, IndexSet};

use crate::code::code_constants::{ACC_STATIC, INIT_NAME};
use crate::decompiler::exps::{
    ConstantValue, ExitType, Expr, ExprKind, FunctionType, Invocation, InvocationFunction,
};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::engine::class_nodes::ClassNodeId;
use crate::engine::class_wrapper::MethodSlot;
use crate::structs::StructMember;
use crate::types::{CodeType, MethodDescriptor, VarType};
use crate::util::interpreter_util::make_unique_key;
use crate::util::java_str::JavaString;

const CLASS_LOADER_DESCRIPTOR: &str = "(Ljava/lang/String;)Ljava/lang/Class;";
const CLASS_NOT_FOUND: &str = "java/lang/ClassNotFoundException";
const NO_CLASS_DEF_FOUND: &str = "java/lang/NoClassDefFoundError";

// The first invocation in a JVM initializes the template expressions. Rust
// matches their shapes directly, but reserves the same ambient IDs once.
static REFERENCE_TEMPLATES: Once = Once::new();
const TEMPLATE_EXPRESSIONS: usize = 8;

pub(super) fn process(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    REFERENCE_TEMPLATES.call_once(|| {
        for _ in 0..TEMPLATE_EXPRESSIONS {
            cx.expression_ids.next();
        }
    });

    // Java keys the helpers by wrapper identity. Owners are unique and a
    // candidate can only match the owner of its cached field.
    let mut loaders = IndexMap::new();
    find_loaders(cx, node, &mut loaders)?;
    if loaders.is_empty() {
        return Ok(());
    }

    let mut found = IndexSet::new();
    replace_class_references(cx, node, &loaders, &mut found)?;
    for owner in found {
        let method = &loaders[&owner].get(cx).method;
        let key = make_unique_key(&method.name, &method.descriptor);
        cx.class_nodes[owner].hidden_members.insert(key);
    }
    Ok(())
}

fn find_loaders(
    cx: &Cx,
    node: ClassNodeId,
    loaders: &mut IndexMap<ClassNodeId, MethodSlot>,
) -> io::Result<()> {
    let owner = wrapper_owner(cx, node)?;
    let wrapper = cx.class_nodes[owner].wrapper.as_ref().unwrap();
    for (index, method) in wrapper.methods.iter().enumerate() {
        if (cx.options.synthetic_not_set || method.method.is_synthetic())
            && method.method.descriptor == CLASS_LOADER_DESCRIPTOR
            && method.method.has_modifier(ACC_STATIC)
            && method.root().is_some_and(|root| is_class_loader(cx, root))
        {
            loaders.insert(owner, MethodSlot { node: owner, index });
            break;
        }
    }
    for &child in &cx.class_nodes[node].nested {
        find_loaders(cx, child, loaders)?;
    }
    Ok(())
}

fn is_class_loader(cx: &Cx, root: StatId) -> bool {
    let ir = &cx.ir;
    let Some(first) = ir[root].first else {
        return false;
    };
    let StatementKind::Catch { vars, .. } = &ir[first].kind else {
        return false;
    };
    let Some(&exception) = vars.first() else {
        return false;
    };
    if ir[first].stats.len() != 2
        || Expr::expr_type(cx, exception)
            != VarType::with_value(CodeType::Object, 0, CLASS_NOT_FOUND)
    {
        return false;
    }

    let Some(body) = ir[first]
        .first
        .and_then(|body| block_exit(ir, body, ExitType::Return))
    else {
        return false;
    };
    let Some(handler) = block_exit(ir, ir[first].stats[1], ExitType::Throw) else {
        return false;
    };
    let ExprKind::Invocation(load) = &ir[body].kind else {
        return false;
    };
    let ExprKind::Invocation(throw) = &ir[handler].kind else {
        return false;
    };
    call_matches(
        load,
        "java/lang/Class",
        "forName",
        CLASS_LOADER_DESCRIPTOR,
        true,
    ) && load.instance.is_none()
        && matches!(load.parameters.as_slice(), [name] if template_var(cx, *name, 0, &VarType::VARTYPE_STRING))
        && call_matches(
            throw,
            NO_CLASS_DEF_FOUND,
            "initCause",
            "(Ljava/lang/Throwable;)Ljava/lang/Throwable;",
            false,
        )
        && matches!(throw.parameters.as_slice(), [error] if template_var(cx, *error, 2, &VarType::with_value(CodeType::Object, 0, CLASS_NOT_FOUND)))
        && throw
            .instance
            .is_some_and(|expr| is_error_allocation(ir, expr))
}

fn block_exit(ir: &Ir, stat: StatId, expected: ExitType) -> Option<ExprId> {
    if !matches!(ir[stat].kind, StatementKind::BasicBlock { .. }) {
        return None;
    }
    let [expr] = ir[ir[stat].exprents?].as_slice() else {
        return None;
    };
    match ir[*expr].kind {
        ExprKind::Exit { kind, value, .. } if kind == expected => value,
        _ => None,
    }
}

fn call_matches(
    call: &Invocation,
    owner: &str,
    name: &str,
    descriptor: &str,
    is_static: bool,
) -> bool {
    let function = if name == INIT_NAME {
        InvocationFunction::Init
    } else {
        InvocationFunction::General
    };
    call.classname.as_deref() == Some(owner)
        && call.name == name
        && call.is_static == is_static
        && call.function == function
        && *call.descriptor == MethodDescriptor::parse_descriptor(descriptor)
}

fn template_var(cx: &Cx, expr: ExprId, index: i32, ty: &VarType) -> bool {
    Expr::variable(&cx.ir, expr)
        .is_some_and(|var| var.index == index && var.version == 0 && &var.expr_type(cx) == ty)
}

fn is_error_allocation(ir: &Ir, expr: ExprId) -> bool {
    let ExprKind::New {
        new_type,
        dimensions,
        constructor: Some(constructor),
        array_elements,
        direct_array_init,
        ..
    } = &ir[expr].kind
    else {
        return false;
    };
    new_type.ty == CodeType::Object
        && new_type.array_dim == 0
        && new_type.value.as_deref() == Some(NO_CLASS_DEF_FOUND)
        && dimensions.is_empty()
        && array_elements.is_empty()
        && !direct_array_init
        && matches!(&ir[*constructor].kind, ExprKind::Invocation(call)
            if call_matches(call, NO_CLASS_DEF_FOUND, INIT_NAME, "()V", false)
                && call.instance.is_none() && call.parameters.is_empty())
}

fn replace_class_references(
    cx: &mut Cx,
    node: ClassNodeId,
    loaders: &IndexMap<ClassNodeId, MethodSlot>,
    found: &mut IndexSet<ClassNodeId>,
) -> io::Result<()> {
    let owner = wrapper_owner(cx, node)?;
    let wrapper = cx.class_nodes[owner].wrapper.as_ref().unwrap();
    for index in 0..wrapper.methods.len() {
        let slot = MethodSlot { node: owner, index };
        if slot.get(cx).root().is_none() {
            continue;
        }
        for list in cx.wrapper_expr_lists(slot) {
            for i in 0..cx.ir[list].len() {
                let expr = cx.ir[list][i];
                for &loader in loaders.values() {
                    if replace_calls(cx, expr, loader)? {
                        found.insert(loader.node);
                    }
                }
            }
        }
    }

    for static_field in [true, false] {
        let len = initializers(cx, owner, static_field).len();
        for index in 0..len {
            for &loader in loaders.values() {
                let expr = initializers(cx, owner, static_field)[index];
                if replace_calls(cx, expr, loader)? {
                    found.insert(loader.node);
                }
                if let Some(class) = literal_class(cx, expr, loader)? {
                    let literal = class_literal(cx, expr, class);
                    let wrapper = cx.class_nodes[owner].wrapper.as_mut().unwrap();
                    let table = if static_field {
                        &mut wrapper.static_field_initializers
                    } else {
                        &mut wrapper.dynamic_field_initializers
                    };
                    table[index] = literal;
                    found.insert(loader.node);
                }
            }
        }
    }

    for index in 0..cx.class_nodes[node].nested.len() {
        let child = cx.class_nodes[node].nested[index];
        replace_class_references(cx, child, loaders, found)?;
    }
    Ok(())
}

fn initializers(cx: &Cx, owner: ClassNodeId, static_field: bool) -> &[ExprId] {
    let wrapper = cx.class_nodes[owner].wrapper.as_ref().unwrap();
    if static_field {
        &wrapper.static_field_initializers
    } else {
        &wrapper.dynamic_field_initializers
    }
}

fn replace_calls(cx: &mut Cx, expr: ExprId, loader: MethodSlot) -> io::Result<bool> {
    let mut replaced = false;
    loop {
        let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
        let mut changed_child = false;
        for child in children {
            if let Some(class) = literal_class(cx, child, loader)? {
                let literal = class_literal(cx, child, class);
                Expr::replace(&mut cx.ir, expr, child, literal);
                changed_child = true;
                replaced = true;
                break;
            }
            replaced |= replace_calls(cx, child, loader)?;
        }
        if !changed_child {
            return Ok(replaced);
        }
    }
}

fn literal_class(cx: &mut Cx, expr: ExprId, loader: MethodSlot) -> io::Result<Option<JavaString>> {
    let Some((field_key, argument)) = match_literal(cx, expr, loader) else {
        return Ok(None);
    };
    // Upstream hides the cache field before looking up the constant value.
    cx.class_nodes[loader.node].hidden_members.insert(field_key);
    let ExprKind::Constant { value, .. } = &cx.ir[argument].kind else {
        unreachable!("Class literal cache calls must have a constant argument");
    };
    value
        .java_string()
        .map(Some)
        .ok_or_else(|| invalid("Null class literal name"))
}

fn match_literal(cx: &Cx, expr: ExprId, loader: MethodSlot) -> Option<(String, ExprId)> {
    let ir = &cx.ir;
    let ExprKind::Function {
        op: FunctionType::Ternary,
        operands,
        ..
    } = &ir[expr].kind
    else {
        return None;
    };
    let [test, populate, cached] = operands.as_slice() else {
        return None;
    };
    let ExprKind::Function {
        op: FunctionType::Eq,
        operands,
        ..
    } = &ir[*test].kind
    else {
        return None;
    };
    let [field, missing] = operands.as_slice() else {
        return None;
    };
    let ExprKind::Field(cache) = &ir[*field].kind else {
        return None;
    };
    let ExprKind::Constant { var_type, .. } = &ir[*missing].kind else {
        return None;
    };
    if *var_type != VarType::VARTYPE_NULL {
        return None;
    }

    let class = &cx.class_nodes[loader.node].class;
    let field_owner = cx.class_nodes.get(cache.classname.as_deref()?)?;
    if field_owner.class.qualified_name != class.qualified_name {
        return None;
    }
    let field_key = make_unique_key(&cache.name, &cache.descriptor.descriptor_string);
    let declaration = class.fields.get_with_key(field_key.as_str())?;
    if !declaration.has_modifier(ACC_STATIC)
        || !(declaration.is_synthetic() || cx.options.synthetic_not_set)
    {
        return None;
    }

    let (lhs, rhs) = ir[*populate].as_assignment()?;
    if !Expr::equals(cx, *cached, *field) || !Expr::equals(cx, lhs, *field) {
        return None;
    }
    let ExprKind::Invocation(call) = &ir[rhs].kind else {
        return None;
    };
    let target = &loader.get(cx).method;
    if call.classname.as_ref() != Some(&class.qualified_name)
        || call.name != target.name
        || call.descriptor.as_str() != target.descriptor.as_str()
    {
        return None;
    }

    let argument = *call.parameters.first()?;
    matches!(ir[argument].kind, ExprKind::Constant { .. }).then_some((field_key, argument))
}

fn class_literal(cx: &mut Cx, expr: ExprId, name: JavaString) -> ExprId {
    let internal_name = JavaString::from_utf16(
        name.utf16()
            .map(|unit| {
                if unit == u16::from(b'.') {
                    u16::from(b'/')
                } else {
                    unit
                }
            })
            .collect(),
    );
    let offsets = cx.ir[expr].bytecode.clone();
    Expr::new_ambient(
        cx,
        Expr::constant(
            VarType::VARTYPE_CLASS,
            ConstantValue::String(internal_name),
            false,
        ),
        offsets,
    )
}

fn wrapper_owner(cx: &Cx, node: ClassNodeId) -> io::Result<ClassNodeId> {
    cx.class_nodes
        .wrapper_owner(node)
        .filter(|&owner| cx.class_nodes[owner].wrapper.is_some())
        .ok_or_else(|| invalid("Missing class wrapper for Java 1.4 references"))
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
