//! CondyHelper's recognition of java.lang.invoke.ConstantBootstraps methods.

use std::{io, sync::Arc};

use arcstr::ArcStr;

use super::{block, get_cast_type_name};
use crate::code::code_constants::OPC_LDC;
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, Field, Invocation, InvocationType};
use crate::decompiler::ir::ExprId;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::{
    StructClass,
    consts::{PooledConstant, PrimitiveConstant},
};
use crate::types::{CodeType, FieldDescriptor, MethodDescriptor, VarType};

const METHOD_HANDLES: &str = "java/lang/invoke/MethodHandles";
const LOOKUP: &str = "java/lang/invoke/MethodHandles$Lookup";

pub(super) fn simplify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    class: &StructClass,
    invocation: ExprId,
) -> io::Result<ExprId> {
    CondyHelper {
        cx,
        counters,
        class,
        expanding: Vec::new(),
    }
    .simplify(invocation)
}

struct CondyHelper<'a> {
    cx: &'a mut Cx,
    counters: &'a mut CounterContainer,
    class: &'a StructClass,
    // Nested dynamic constants may refer back to a bootstrap already in use.
    expanding: Vec<(i32, i32)>,
}

impl CondyHelper<'_> {
    fn simplify(&mut self, expr: ExprId) -> io::Result<ExprId> {
        let ExprKind::Invocation(invocation) = &self.cx.ir[expr].kind else {
            unreachable!()
        };
        let Some(bootstrap) = &invocation.bootstrap_method else {
            return Ok(expr);
        };
        if invocation.kind != InvocationType::ConstantDynamic
            || bootstrap.classname.as_deref() != Some("java/lang/invoke/ConstantBootstraps")
        {
            return Ok(expr);
        }

        let name = invocation.name.clone();
        let method = bootstrap.elementname.clone();
        let ret = invocation.descriptor.ret.clone();
        let arguments = invocation.bootstrap_arguments.clone();
        let args = arguments.as_deref().unwrap_or_default();
        Ok(match method.as_str() {
            "nullConstant" => self.constant(VarType::VARTYPE_NULL, ConstantValue::Null, true),
            "primitiveClass" if name.len() == 1 && "ZCBSIJFDV".contains(name.as_str()) => {
                self.class_literal(&name, true)?
            }
            "enumConstant" => {
                let descriptor = format!("L{};", ret.name());
                self.field(name, ret.value, &descriptor)
            }
            "getStaticFinal" => {
                let owner = match args {
                    [Some(PooledConstant::Primitive(owner))] => Some(owner_name(owner)?),
                    [_] => return Ok(expr),
                    _ if ret.ty == CodeType::Object => ret.value.clone(),
                    _ => return Ok(expr),
                };
                self.field(name, owner, ret.name())
            }
            "fieldVarHandle" | "staticFieldVarHandle"
                if self.cx.options.decompile_complex_constant_dynamic =>
            {
                let [Some(PooledConstant::Primitive(owner)), ty] = args else {
                    return Ok(expr);
                };
                let lookup = self.call(
                    METHOD_HANDLES,
                    "lookup",
                    "()Ljava/lang/invoke/MethodHandles$Lookup;",
                    None,
                    Vec::new(),
                    false,
                );
                let owner = self.class_literal(string_value(owner)?, false)?;
                let field = self.constant(
                    VarType::VARTYPE_STRING,
                    ConstantValue::String(name.into()),
                    false,
                );
                let ty = self.class_argument(ty.as_ref())?;
                let name = if method == "staticFieldVarHandle" {
                    "findStaticVarHandle"
                } else {
                    "findVarHandle"
                };
                self.call(LOOKUP, name, "(Ljava/lang/Class;Ljava/lang/String;Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;", Some(lookup), vec![owner, field, ty], true)
            }
            "arrayVarHandle" if self.cx.options.decompile_complex_constant_dynamic => {
                let [ty] = args else { return Ok(expr) };
                // Java constructs the invocation before expanding its argument.
                let call = self.call(
                    METHOD_HANDLES,
                    "arrayElementVarHandle",
                    "(Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;",
                    None,
                    Vec::new(),
                    true,
                );
                let ty = self.class_argument(ty.as_ref())?;
                let ExprKind::Invocation(invocation) = &mut self.cx.ir[call].kind else {
                    unreachable!()
                };
                invocation.parameters.push(ty);
                call
            }
            _ => expr,
        })
    }

    fn class_argument(&mut self, arg: Option<&PooledConstant>) -> io::Result<ExprId> {
        match arg {
            Some(PooledConstant::Primitive(constant)) => {
                self.class_literal(string_value(constant)?, false)
            }
            Some(PooledConstant::Link(link)) => {
                let key = (link.index1, link.index2);
                if self.expanding.contains(&key) {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "cyclic constant-dynamic bootstrap argument",
                    ));
                }
                self.expanding.push(key);
                let call = block::invocation(
                    self.cx,
                    self.counters,
                    self.class,
                    OPC_LDC,
                    link,
                    &mut Vec::new(),
                    None,
                )?;
                let arg = self.simplify(call)?;
                self.expanding.pop();
                if let ExprKind::Constant { was_condy, .. } = &mut self.cx.ir[arg].kind {
                    *was_condy = false;
                }
                Ok(arg)
            }
            None => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "missing constant-dynamic bootstrap argument",
            )),
        }
    }

    fn constant(&mut self, ty: VarType, value: ConstantValue, was_condy: bool) -> ExprId {
        Expr::new(
            &mut self.cx.ir,
            self.counters,
            Expr::constant(ty, value, was_condy),
            None,
        )
    }

    fn class_literal(&mut self, descriptor: &str, was_condy: bool) -> io::Result<ExprId> {
        let ty = VarType::try_from_signature_cl(descriptor, false)?;
        let name = get_cast_type_name(self.cx, &ty);
        Ok(self.constant(
            VarType::VARTYPE_CLASS,
            ConstantValue::String(name.into()),
            was_condy,
        ))
    }

    fn field(&mut self, name: ArcStr, classname: Option<ArcStr>, descriptor: &str) -> ExprId {
        let field = Field {
            name,
            classname,
            descriptor: FieldDescriptor::parse_descriptor(descriptor),
            instance: None,
            force_qualified: false,
            was_condy: true,
        };
        Expr::new(
            &mut self.cx.ir,
            self.counters,
            ExprKind::Field(Box::new(field)),
            None,
        )
    }

    fn call(
        &mut self,
        owner: &str,
        name: &str,
        descriptor: &str,
        instance: Option<ExprId>,
        parameters: Vec<ExprId>,
        lazy: bool,
    ) -> ExprId {
        let mut call = Invocation::new(
            name.into(),
            Some(owner.into()),
            Arc::new(MethodDescriptor::parse_descriptor(descriptor)),
        );
        call.is_static = instance.is_none();
        call.instance = instance;
        call.parameters = parameters;
        call.was_lazy_condy = lazy;
        Expr::new(
            &mut self.cx.ir,
            self.counters,
            ExprKind::Invocation(Box::new(call)),
            None,
        )
    }
}

fn string_value(c: &PrimitiveConstant) -> io::Result<&ArcStr> {
    match &c.value {
        ConstantValue::String(s) => Ok(s.as_utf8_lossy()),
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "expected a class name in a constant bootstrap",
        )),
    }
}

fn owner_name(c: &PrimitiveConstant) -> io::Result<ArcStr> {
    Ok(match &c.value {
        ConstantValue::String(s) => s.as_utf8_lossy().clone(),
        ConstantValue::Integer(n) => n.to_string().into(),
        ConstantValue::Long(n) => n.to_string().into(),
        ConstantValue::Float(n) => format!("{n:?}").into(),
        ConstantValue::Double(n) => format!("{n:?}").into(),
        ConstantValue::Null => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "null field owner in constant bootstrap",
            ));
        }
    })
}
