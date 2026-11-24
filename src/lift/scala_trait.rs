// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::{
    bytecode::Instruction,
    classfile::{ClassError, ClassFile, Code, Constant, ConstantPool, Member, find_attribute},
    source_text::Document,
};

use super::{
    Effect, LiftError, Machine,
    expr::{Expr, Source},
};

const PUBLIC: u16 = 0x0001;
const STATIC: u16 = 0x0008;
const INTERFACE: u16 = 0x0200;
const SYNTHETIC: u16 = 0x1000;
const DEFAULT_DESCRIPTOR: &str = "()I";

impl Machine<'_, '_> {
    pub(super) fn scala_trait_invocation(
        &mut self,
        op: &Instruction,
        index: u16,
        (owner, name, descriptor): (&str, &str, &str),
        receiver: Expr,
    ) -> Result<Option<Effect>, LiftError> {
        if self.lambda_depth != 0
            || op.offset != 1
            || !self.stack.is_empty()
            || !matches!(receiver.source, Source::Local(0))
            || descriptor != DEFAULT_DESCRIPTOR
            || bridge_call(self.code) != Some(index)
            || bridge_target(self.class, self.method, owner)? != Some(name)
        {
            return Ok(None);
        }
        let Some(value) = constant_default(self.class, name)? else {
            return Ok(None);
        };

        // Java cannot express an interface-super call on a parameter. The
        // proved default returns a literal without using its receiver, so only
        // the JVM's implicit null check must precede that result. Do not use
        // virtual dispatch, even when the receiver overrides the default.
        let order = self.order_of([&receiver], true)?;
        self.before_statement(order)?;
        let mut check = Document::from("if (");
        check.append(receiver.text);
        check.push_str(" == null) ");
        self.anchor_member(&mut check, op);
        check.push_str("throw null;");
        self.push(Expr::integer(value))?;
        Ok(Some(Effect::Statement(check)))
    }
}

/// A proved Scala bridge remains a callable static entry point even when it
/// carries the Synthetic flag or attribute.
pub(crate) fn keep_synthetic_bridge(
    class: &ClassFile<'_>,
    bridge: &Member<'_>,
) -> Result<bool, ClassError> {
    if class.access_flags & INTERFACE == 0 || bridge.access_flags & STATIC == 0 {
        return Ok(false);
    }
    let pool = &class.pool;
    let owner = pool.class_name(class.this_class)?;
    let Some(target) = bridge_target(class, bridge, owner)? else {
        return Ok(false);
    };
    let Some(index) = bridge.code(pool)?.as_ref().and_then(bridge_call) else {
        return Ok(false);
    };
    Ok(matches!(pool.get(index)?, Constant::InterfaceMethodref { .. })
        && pool.member_ref(index)? == (owner, target, DEFAULT_DESCRIPTOR)
        && constant_default(class, target)?.is_some())
}

fn bridge_target<'c>(
    class: &'c ClassFile<'_>,
    bridge: &Member<'_>,
    owner: &str,
) -> Result<Option<&'c str>, ClassError> {
    if class.access_flags & INTERFACE == 0
        || class.major_version < 52
        || bridge.access_flags & !SYNTHETIC != (PUBLIC | STATIC)
    {
        return Ok(None);
    }
    let pool = &class.pool;
    let Some(target) = pool.utf8(bridge.name_index)?.strip_suffix('$') else {
        return Ok(None);
    };
    let receiver = pool
        .utf8(bridge.descriptor_index)?
        .strip_prefix("(L")
        .and_then(|descriptor| descriptor.strip_suffix(";)I"));
    if target.is_empty()
        || target.starts_with('<')
        || receiver != Some(owner)
        || !matches!(find_attribute(&class.attributes, pool, "Scala")?, Some([]))
    {
        return Ok(None);
    }
    Ok(Some(target))
}

fn bridge_call(code: &Code<'_>) -> Option<u16> {
    let &[0x2a, 0xb7, high, low, 0xac] = code.bytes else {
        return None;
    };
    (code.max_stack >= 1 && code.max_locals >= 1 && code.exceptions.is_empty())
        .then_some(u16::from_be_bytes([high, low]))
}

fn constant_default(class: &ClassFile<'_>, name: &str) -> Result<Option<i32>, ClassError> {
    let pool = &class.pool;
    let mut target = None;
    for method in &class.methods {
        if pool.utf8(method.name_index)? != name
            || pool.utf8(method.descriptor_index)? != DEFAULT_DESCRIPTOR
        {
            continue;
        }
        if target.replace(method).is_some() {
            return Ok(None);
        }
    }
    let Some(method) = target else {
        return Ok(None);
    };
    if method.access_flags != PUBLIC
        || find_attribute(&method.attributes, pool, "Synthetic")?.is_some()
    {
        return Ok(None);
    }
    let Some(code) = method.code(pool)? else {
        return Ok(None);
    };
    if code.max_stack < 1 || code.max_locals < 1 || !code.exceptions.is_empty() {
        return Ok(None);
    }
    constant_int_return(pool, code.bytes)
}

fn constant_int_return(pool: &ConstantPool<'_>, bytes: &[u8]) -> Result<Option<i32>, ClassError> {
    let index = match *bytes {
        [op @ 0x02..=0x08, 0xac] => return Ok(Some(i32::from(op) - 3)),
        [0x10, value, 0xac] => return Ok(Some(i32::from(value as i8))),
        [0x11, high, low, 0xac] => return Ok(Some(i32::from(i16::from_be_bytes([high, low])))),
        [0x12, index, 0xac] => u16::from(index),
        [0x13, high, low, 0xac] => u16::from_be_bytes([high, low]),
        _ => return Ok(None),
    };
    Ok(match pool.get(index)? {
        Constant::Integer(value) => Some(*value),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Scala-marked interface with a synthetic value$ bridge and a constant default.
    const TRAIT: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x0d\
        \x01\0\x10pkg/ExampleTrait\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
        \x01\0\x06value$\x01\0\x15(Lpkg/ExampleTrait;)I\x01\0\x05value\x01\0\x03()I\
        \x0c\0\x07\0\x08\x0b\0\x02\0\x09\x01\0\x04Code\x01\0\x05Scala\
        \x06\x01\0\x02\0\x04\0\0\0\0\0\x02\
        \x10\x09\0\x05\0\x06\0\x01\0\x0b\0\0\0\x11\0\x01\0\x01\0\0\0\x05\x2a\xb7\0\x0a\xac\0\0\0\0\
        \0\x01\0\x07\0\x08\0\x01\0\x0b\0\0\0\x0e\0\x01\0\x01\0\0\0\x02\x08\xac\0\0\0\0\
        \0\x01\0\x0c\0\0\0\0";

    #[test]
    fn retains_the_bridge_without_virtual_dispatch() {
        let source = crate::decompile(TRAIT, &crate::Options::default()).unwrap().text;
        assert!(source.contains("static int value$(ExampleTrait var0)"), "{source}");
        assert!(source.contains("if (var0 == null) throw null;"), "{source}");
        assert_eq!(source.matches("return 5;").count(), 2, "{source}");
        assert!(!source.contains("var0.value()"), "{source}");
    }

    #[test]
    fn rejects_lifting_the_same_instructions_without_a_scala_marker() {
        let mut ordinary = TRAIT.to_vec();
        let marker = ordinary
            .windows(5)
            .position(|bytes| bytes == b"Scala")
            .unwrap();
        ordinary[marker] = b'X';
        let options = crate::Options {
            remove_synthetic: false,
            ..crate::Options::default()
        };
        let error = crate::decompile(&ordinary, &options).unwrap_err();
        assert!(error.to_string().contains("nonvirtual invokespecial"), "{error}");
    }

    #[test]
    fn rejects_a_default_that_can_call_the_receiver() {
        let mut class = ClassFile::parse(TRAIT).unwrap();
        // aload_0; invokeinterface value:()I; ireturn
        class.methods[1].attributes[0].data = b"\0\x01\0\x01\0\0\0\x07\x2a\xb9\0\x0a\x01\0\xac\0\0\0\0";
        assert!(!keep_synthetic_bridge(&class, &class.methods[0]).unwrap());
    }
}
