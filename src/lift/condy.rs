// Based on Vineflower's CondyHelper (Apache-2.0).
use std::borrow::Cow;

use crate::{classfile::Constant, descriptor::Type, source_text::Document};

use super::{
    LiftError, Machine,
    expr::{Expr, PRIMARY},
    string_literal,
};

const BOOTSTRAPS: &str = "java/lang/invoke/ConstantBootstraps";
const HANDLES: &str = "java/lang/invoke/MethodHandles";
const HANDLE: &str = "java/lang/invoke/VarHandle";
const CLASS: &str = "Ljava/lang/Class;";
const LOOKUP: &str = "()Ljava/lang/invoke/MethodHandles$Lookup;";
const FIELD_BOOTSTRAP: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/Class;Ljava/lang/Class;Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;";
const ARRAY_BOOTSTRAP: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/Class;Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;";
const ARRAY_FACTORY: &str = "(Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;";
const PRIMITIVE_BOOTSTRAP: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/Class;)Ljava/lang/Class;";
const WARNING: &str = "/* $VF: constant dynamic replaced with non-lazy method call */ ";

impl Machine<'_, '_> {
    pub(super) fn var_handle_constant(
        &self,
        bootstrap: &str,
        signature: &str,
        name: &str,
        ty: Type,
        args: &[u16],
    ) -> Result<Expr, LiftError> {
        if !self.options.decompile_complex_constant_dynamic {
            return Err(self.unsupported("dynamic constant bootstrap requires lazy, cached JVM linkage"));
        }
        if !matches!(&ty, Type::Object(name) if name == HANDLE)
            || name.is_empty()
            || name.contains(['.', ';', '[', '/'])
            || matches!(name, "<init>" | "<clinit>")
        {
            return Err(self.invalid_operand("invalid VarHandle constant name or result type"));
        }

        let mut text = Document::from(WARNING);
        match (bootstrap, signature, args) {
            ("fieldVarHandle" | "staticFieldVarHandle", FIELD_BOOTSTRAP, &[owner, field_type]) => {
                let (owner, _) = self.var_handle_class(owner)?;
                let Type::Object(owner) = owner else {
                    return Err(self.invalid_operand("field VarHandle needs a declaring class"));
                };
                let (field_type, binary) = self.var_handle_class(field_type)?;
                let name = if let Some(renames) = self.renames.filter(|_| self.options.rename_members) {
                    let descriptor = match field_type {
                        Type::Object(_) => Cow::Owned(format!("L{binary};")),
                        _ => Cow::Borrowed(binary),
                    };
                    renames.field_name(&owner, name, &descriptor)
                } else {
                    name
                };
                let name = string_literal(&name.encode_utf16().collect::<Vec<_>>(), self.options.ascii_strings).into();
                let mut lookup = self.class_reference(HANDLES);
                lookup.push('.');
                self.append_method_reference(&mut lookup, "lookup", HANDLES, "lookup", LOOKUP);
                lookup.push_str("()");
                let handle = self.var_handle_class_literal(&ty);
                let owner = self.var_handle_class_literal(&Type::Object(owner));
                let field = self.var_handle_class_literal(&field_type);
                // Invoke the exact standard bootstrap rather than emitting a
                // checked Lookup.find*VarHandle call into an arbitrary method.
                text.append(self.class_reference(BOOTSTRAPS));
                text.push('.');
                self.append_method_reference(&mut text, bootstrap, BOOTSTRAPS, bootstrap, FIELD_BOOTSTRAP);
                text.append_relative_arguments([&lookup, &name, &handle, &owner, &field]);
            }
            ("arrayVarHandle", ARRAY_BOOTSTRAP, &[array]) => {
                let (array, _) = self.var_handle_class(array)?;
                if !matches!(array, Type::Array(_)) {
                    return Err(self.invalid_operand("array VarHandle needs an array class"));
                }
                let array = self.var_handle_class_literal(&array);
                text.append(self.class_reference(HANDLES));
                text.push('.');
                let name = "arrayElementVarHandle";
                self.append_method_reference(&mut text, name, HANDLES, name, ARRAY_FACTORY);
                text.append_relative_arguments([&array]);
            }
            _ => return Err(self.invalid_operand("invalid VarHandle bootstrap descriptor or arity")),
        };
        Ok(Expr {
            statement: true,
            ..self.expression(ty, text, PRIMARY, [], true)?
        })
    }

    /// A VarHandle argument is a CONSTANT_Class or exactly a nested
    /// ConstantBootstraps.primitiveClass. Never interpret arbitrary linkage.
    fn var_handle_class(&self, index: u16) -> Result<(Type, &str), LiftError> {
        let pool = &self.class.pool;
        match *pool.get(index)? {
            Constant::Class(name) => {
                let binary = pool.utf8(name)?;
                let ty = if binary.starts_with('[') {
                    Type::parse(binary)?
                } else {
                    if binary.split('/').any(|part| part.is_empty() || part.contains(['.', ';', '['])) {
                        return Err(self.invalid_operand("invalid VarHandle class argument"));
                    }
                    Type::Object(binary.into())
                };
                Ok((ty, binary))
            }
            Constant::Dynamic { bootstrap_index, name_and_type_index } => {
                let invalid = || self.invalid_operand("VarHandle class argument is not a verified primitiveClass constant");
                let method = self.bootstrap.as_deref().and_then(|methods| methods.get(usize::from(bootstrap_index)))
                    .ok_or_else(invalid)?;
                let Constant::MethodHandle { reference_kind: 6, reference_index } = *pool.get(method.method_ref)? else {
                    return Err(invalid());
                };
                let (name, ty) = pool.name_and_type(name_and_type_index)?;
                if !matches!(pool.get(reference_index)?, Constant::Methodref { .. })
                    || pool.member_ref(reference_index)? != (BOOTSTRAPS, "primitiveClass", PRIMITIVE_BOOTSTRAP)
                    || !method.arguments.is_empty()
                    || ty != CLASS
                    || !matches!(name, "Z" | "B" | "C" | "S" | "I" | "J" | "F" | "D")
                {
                    return Err(invalid());
                }
                // void.class is a valid primitiveClass but not a field type.
                Ok((Type::parse(name)?, name))
            }
            _ => Err(self.invalid_operand("VarHandle bootstrap argument is not a class constant")),
        }
    }

    fn var_handle_class_literal(&self, ty: &Type) -> Document {
        let mut text = self.type_reference(ty);
        text.push_str(".class");
        text
    }
}
