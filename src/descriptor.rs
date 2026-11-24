// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! JVM descriptors (JVMS §4.3) and generic signatures (JVMS §4.7.9.1).

mod signature;

pub use signature::{
    ClassSignature, ClassType, FieldSignature, GenericType, MethodSignature, NestedType,
    TypeArgument, TypeParameter, render_type_parameters,
};

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum DescriptorError {
    #[error("expected {expected} at byte {offset}")]
    Expected {
        expected: &'static str,
        offset: usize,
    },
    #[error("unexpected trailing input at byte {offset}")]
    TrailingInput { offset: usize },
    #[error("array has more than 255 dimensions at byte {offset}")]
    ArrayDimensions { offset: usize },
    #[error("method parameters occupy more than 255 slots at byte {offset}")]
    ParameterSlots { offset: usize },
    #[error("generic type argument nesting is too deep at byte {offset}")]
    SignatureDepth { offset: usize },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Primitive {
    Boolean,
    Byte,
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
}

impl Primitive {
    fn from_tag(tag: u8) -> Option<Self> {
        Some(match tag {
            b'Z' => Self::Boolean,
            b'B' => Self::Byte,
            b'C' => Self::Char,
            b'S' => Self::Short,
            b'I' => Self::Int,
            b'J' => Self::Long,
            b'F' => Self::Float,
            b'D' => Self::Double,
            _ => return None,
        })
    }

    pub const fn java_name(self) -> &'static str {
        match self {
            Self::Boolean => "boolean",
            Self::Byte => "byte",
            Self::Char => "char",
            Self::Short => "short",
            Self::Int => "int",
            Self::Long => "long",
            Self::Float => "float",
            Self::Double => "double",
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    Primitive(Primitive),
    Object(String),
    Array(Box<Type>),
    Void,
}

impl Type {
    /// Parses a field descriptor. `void` is only valid as a method return type.
    pub fn parse(descriptor: &str) -> Result<Self, DescriptorError> {
        let mut parser = Parser::new(descriptor);
        let field_type = parse_field_type(&mut parser)?;
        parser.finish()?;
        Ok(field_type)
    }

    pub const fn slots(&self) -> u16 {
        match self {
            Self::Primitive(Primitive::Long | Primitive::Double) => 2,
            Self::Void => 0,
            _ => 1,
        }
    }

    /// Renders Java syntax, passing each internal class name to `map`.
    pub fn render(&self, mut map: impl FnMut(&str) -> String) -> String {
        let mut element = self;
        let mut dimensions = 0;
        while let Self::Array(component) = element {
            dimensions += 1;
            element = component;
        }
        let mut result = match element {
            Self::Primitive(primitive) => primitive.java_name().to_owned(),
            Self::Object(name) => map(name),
            Self::Void => String::from("void"),
            Self::Array(_) => unreachable!(),
        };
        append_array_suffix(&mut result, dimensions);
        result
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct MethodDescriptor {
    pub parameters: Vec<Type>,
    pub return_type: Type,
}

impl MethodDescriptor {
    pub fn parse(descriptor: &str) -> Result<Self, DescriptorError> {
        let mut parser = Parser::new(descriptor);
        parser.expect(b'(', "'('")?;
        let mut parameters = Vec::new();
        let mut slots = 0;
        while !parser.consume(b')') {
            let offset = parser.position;
            let parameter = parse_field_type(&mut parser)?;
            slots += parameter.slots();
            if slots > 255 {
                return Err(DescriptorError::ParameterSlots { offset });
            }
            parameters.push(parameter);
        }
        let return_type = if parser.consume(b'V') {
            Type::Void
        } else {
            parse_field_type(&mut parser)?
        };
        parser.finish()?;
        Ok(Self {
            parameters,
            return_type,
        })
    }
}

fn parse_field_type(parser: &mut Parser<'_>) -> Result<Type, DescriptorError> {
    let dimensions = parser.array_dimensions()?;
    let mut element = if let Some(primitive) = parser.primitive() {
        Type::Primitive(primitive)
    } else if parser.consume(b'L') {
        let start = parser.position;
        loop {
            parser.identifier(b".;[/", "class name component")?;
            if !parser.consume(b'/') {
                break;
            }
        }
        let name = &parser.source[start..parser.position];
        parser.expect(b';', "';' after class name")?;
        Type::Object(name.to_owned())
    } else {
        return Err(parser.expected("field type"));
    };
    for _ in 0..dimensions {
        element = Type::Array(Box::new(element));
    }
    Ok(element)
}

fn append_array_suffix(out: &mut String, dimensions: usize) {
    out.reserve(2 * dimensions);
    for _ in 0..dimensions {
        out.push_str("[]");
    }
}

struct Parser<'a> {
    source: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            position: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.source.as_bytes().get(self.position).copied()
    }

    fn consume(&mut self, byte: u8) -> bool {
        if self.peek() != Some(byte) {
            return false;
        }
        self.position += 1;
        true
    }

    fn expect(&mut self, byte: u8, expected: &'static str) -> Result<(), DescriptorError> {
        if self.consume(byte) {
            Ok(())
        } else {
            Err(self.expected(expected))
        }
    }

    fn expected(&self, expected: &'static str) -> DescriptorError {
        DescriptorError::Expected {
            expected,
            offset: self.position,
        }
    }

    fn identifier_end(&self, delimiters: &[u8]) -> usize {
        self.source.as_bytes()[self.position..]
            .iter()
            .position(|byte| delimiters.contains(byte))
            .map_or(self.source.len(), |offset| self.position + offset)
    }

    fn identifier(
        &mut self,
        delimiters: &[u8],
        expected: &'static str,
    ) -> Result<&'a str, DescriptorError> {
        let end = self.identifier_end(delimiters);
        if end == self.position {
            return Err(self.expected(expected));
        }
        let name = &self.source[self.position..end];
        self.position = end;
        Ok(name)
    }

    fn primitive(&mut self) -> Option<Primitive> {
        let primitive = Primitive::from_tag(self.peek()?)?;
        self.position += 1;
        Some(primitive)
    }

    fn array_dimensions(&mut self) -> Result<u8, DescriptorError> {
        let start = self.position;
        while self.consume(b'[') {
            if self.position - start > usize::from(u8::MAX) {
                return Err(DescriptorError::ArrayDimensions {
                    offset: self.position - 1,
                });
            }
        }
        Ok((self.position - start) as u8)
    }

    fn finish(&self) -> Result<(), DescriptorError> {
        if self.position == self.source.len() {
            Ok(())
        } else {
            Err(DescriptorError::TrailingInput {
                offset: self.position,
            })
        }
    }
}

/// Vineflower's integer inference lattice, distinct from descriptor primitives.
/// `ByteChar` and `ShortChar` retain ambiguity between integral and char values.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IntType {
    Boolean,
    ByteChar,
    ShortChar,
    Byte,
    Short,
    Char,
    Int,
}

impl IntType {
    /// Returns the least type that can represent either input in the lattice.
    pub const fn join(self, other: Self) -> Self {
        use IntType::*;
        if self.contains(other) {
            self
        } else if other.contains(self) {
            other
        } else if matches!((self, other), (Byte, ShortChar) | (ShortChar, Byte)) {
            Short
        } else {
            Int
        }
    }

    const fn contains(self, other: Self) -> bool {
        use IntType::*;
        match self {
            Boolean => matches!(other, Boolean),
            ByteChar => matches!(other, Boolean | ByteChar),
            Byte => matches!(other, Boolean | ByteChar | Byte),
            ShortChar => matches!(other, Boolean | ByteChar | ShortChar),
            Short => matches!(other, Boolean | ByteChar | Byte | ShortChar | Short),
            Char => matches!(other, Boolean | ByteChar | ShortChar | Char),
            Int => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn method_descriptors_and_slots() {
        let descriptor =
            MethodDescriptor::parse("(ZBCSIDFJ[[J[Lpkg/Ω;)Ljava/lang/String;").unwrap();
        let names = descriptor
            .parameters
            .iter()
            .map(|ty| ty.render(|name| name.replace('/', ".")));
        assert!(names.eq([
            "boolean", "byte", "char", "short", "int", "double", "float", "long", "long[][]",
            "pkg.Ω[]",
        ]));
        assert_eq!(
            descriptor.parameters.iter().map(Type::slots).sum::<u16>(),
            12
        );
        assert_eq!(
            descriptor.return_type.render(|_| String::from("String")),
            "String"
        );
        assert_eq!(
            MethodDescriptor::parse("()V").unwrap().return_type.slots(),
            0
        );
        assert_eq!(
            Type::parse("Lpkg/A(B)C;").unwrap(),
            Type::Object(String::from("pkg/A(B)C"))
        );
    }

    #[test]
    fn descriptor_grammar_rejects_void_fields_and_malformed_names() {
        for input in [
            "",
            "V",
            "[V",
            "L;",
            "Lpkg//Bar;",
            "L/Bar;",
            "Lpkg/;",
            "Lpkg.Bar;",
            "Lpkg/Bar",
            "II",
            "Tn;",
        ] {
            assert!(Type::parse(input).is_err(), "accepted {input:?}");
        }
        for input in [
            "", "I)V", "(I", "(V)V", "([V)V", "()", "()VV", "()V;", "()TV;",
        ] {
            assert!(
                MethodDescriptor::parse(input).is_err(),
                "accepted {input:?}"
            );
        }
    }

    #[test]
    fn limits_for_descriptors() {
        assert!(Type::parse(&format!("{}I", "[".repeat(255))).is_ok());
        assert_eq!(
            Type::parse(&format!("{}I", "[".repeat(256))),
            Err(DescriptorError::ArrayDimensions { offset: 255 }),
        );
        assert!(MethodDescriptor::parse(&format!("({}I)V", "J".repeat(127))).is_ok());
        assert_eq!(
            MethodDescriptor::parse(&format!("({}J)V", "J".repeat(127))),
            Err(DescriptorError::ParameterSlots { offset: 128 }),
        );
    }

    #[test]
    fn int_joins() {
        use IntType::*;
        // Vineflower's TypesTest.intJoins: each lower integer type joins to int.
        for lower in [ByteChar, ShortChar, Char, Short, Byte] {
            assert_eq!(Int.join(lower), Int);
        }
    }

    #[test]
    fn integer_join_is_a_least_upper_bound() {
        use IntType::*;
        let types = [Boolean, ByteChar, Byte, ShortChar, Short, Char, Int];
        for a in types {
            for b in types {
                let joined = a.join(b);
                assert_eq!(joined, b.join(a));
                assert!(joined.contains(a) && joined.contains(b));
                for upper in types {
                    if upper.contains(a) && upper.contains(b) {
                        assert!(upper.contains(joined));
                    }
                }
            }
        }
        assert_eq!(Byte.join(ShortChar), Short);
        assert_eq!(ShortChar.join(Char), Char);
        assert_eq!(Byte.join(Char), Int);
    }
}
