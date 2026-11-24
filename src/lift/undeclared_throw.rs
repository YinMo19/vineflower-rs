use crate::{classfile::find_attribute, descriptor::Type, source_text::Document};

use super::{DynamicHelper, LiftError, Machine, expr::Expr};

impl Machine<'_, '_> {
    pub(super) fn throw_expression(&self, mut value: Expr) -> Result<Document, LiftError> {
        // JVM languages need not declare checked exceptions. For a newly
        // allocated checked base type in a private static method without
        // local handlers, preserve the object without changing the method's
        // declared throws clause or making a Java catch unreachable.
        if let Some(helpers) = &self.dynamic_helpers
            && self.normalized.is_none()
            && self.method.access_flags & 0x000a == 0x000a
            && self.code.exceptions.is_empty()
            && matches!(&value.ty, Type::Object(name) if name == "java/lang/Exception" || name == "java/lang/Throwable")
            && value.order.is_some_and(|order| self.code.bytes.get(order.first as usize) == Some(&0xbb))
            && find_attribute(&self.method.attributes, &self.class.pool, "Exceptions")?.is_none()
        {
            let mut name = String::from("$vf$rethrow");
            while self.current_member_named(&name, true)? {
                name.push('$');
            }
            value.text.surround(&format!("{name}("), ")");
            helpers.borrow_mut().insert(DynamicHelper::Rethrow(name));
        }
        Ok(value.text)
    }
}
