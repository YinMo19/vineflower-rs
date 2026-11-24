// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{
    ClassName, Classifier, KotlinError, Type, TypeArgument, TypeParameter, Variance, Visibility,
};

pub(super) const INDENT: &str = "   ";

pub(super) fn plain_identifier(name: &str) -> bool {
    let mut chars = name.bytes();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == b'_')
        && !name.bytes().all(|c| c == b'_')
        && !matches!(
            name,
            "as" | "break"
                | "class"
                | "continue"
                | "do"
                | "else"
                | "false"
                | "for"
                | "fun"
                | "if"
                | "in"
                | "interface"
                | "is"
                | "null"
                | "object"
                | "package"
                | "return"
                | "super"
                | "this"
                | "throw"
                | "true"
                | "try"
                | "typealias"
                | "typeof"
                | "val"
                | "var"
                | "when"
                | "while"
        )
}

pub(super) fn identifier(
    out: &mut String,
    name: &str,
    declaration: &str,
) -> Result<(), KotlinError> {
    if plain_identifier(name) {
        out.push_str(name);
    } else {
        if name.is_empty()
            || name.chars().any(|c| {
                c.is_control()
                    || matches!(
                        c,
                        '`' | '.'
                            | ';'
                            | '['
                            | ']'
                            | '/'
                            | '<'
                            | '>'
                            | ':'
                            | '\\'
                            | '\u{2028}'
                            | '\u{2029}'
                    )
            })
        {
            return Err(KotlinError::unsupported(
                declaration,
                "identifier cannot be expressed in Kotlin/JVM",
            ));
        }
        out.push('`');
        out.push_str(name);
        out.push('`');
    }
    Ok(())
}

pub(super) fn qualified(
    out: &mut String,
    name: &str,
    declaration: &str,
) -> Result<(), KotlinError> {
    for (index, part) in name.split(['/', '.']).enumerate() {
        if index != 0 {
            out.push('.');
        }
        identifier(out, part, declaration)?;
    }
    Ok(())
}

pub(super) fn visibility(visibility: Visibility) -> Result<&'static str, KotlinError> {
    Ok(match visibility {
        Visibility::Public => "public ",
        Visibility::Internal => "internal ",
        Visibility::Protected => "protected ",
        Visibility::Private | Visibility::PrivateToThis => "private ",
        Visibility::Local => {
            return Err(KotlinError::Metadata(
                "local visibility on source declaration",
            ));
        }
    })
}

pub(super) struct Types<'a> {
    pub declaration: &'a str,
    pub package: &'a str,
    pub owner: Option<&'a ClassName>,
    pub owner_parameters: &'a [TypeParameter],
    pub local_parameters: &'a [TypeParameter],
}

impl Types<'_> {
    pub fn local<'a>(&'a self, declaration: &'a str, parameters: &'a [TypeParameter]) -> Types<'a> {
        Types {
            declaration,
            local_parameters: parameters,
            ..*self
        }
    }

    pub fn write(&self, out: &mut String, ty: &Type) -> Result<(), KotlinError> {
        if ty.raw || ty.flexible.is_some() || ty.suspend {
            return Err(self.unsupported("raw, flexible or suspend type"));
        }
        if let Some(abbreviated) = &ty.abbreviated {
            if abbreviated.nullable != ty.nullable || !ty.annotations.is_empty() {
                return Err(self.unsupported("annotated or differently nullable type abbreviation"));
            }
            return self.write(out, abbreviated);
        }
        if let Some(arity) = ty
            .class_id()
            .and_then(|id| id.strip_prefix("kotlin/Function"))
            .and_then(|arity| arity.parse::<usize>().ok())
        {
            return self.function(out, ty, arity);
        }
        if !ty.annotations.is_empty() {
            return Err(self.unsupported("type-use annotations"));
        }
        match &ty.classifier {
            Classifier::Class(name) | Classifier::TypeAlias(name) => {
                if ty.definitely_not_null {
                    return Err(self.unsupported("definitely non-null class type"));
                }
                if let Some(outer) = &ty.outer {
                    self.write(out, outer)?;
                    out.push('.');
                    let (_, short) = name
                        .relative_name()
                        .rsplit_once('.')
                        .ok_or_else(|| self.unsupported("outer type for non-nested class"))?;
                    identifier(out, short, self.declaration)?;
                } else {
                    self.class(out, name)?;
                }
            }
            Classifier::TypeParameter(_) | Classifier::TypeParameterName(_) => {
                if !ty.arguments.is_empty() || ty.outer.is_some() {
                    return Err(self.unsupported("arguments or outer type on type parameter"));
                }
                let param = self
                    .local_parameters
                    .iter()
                    .chain(self.owner_parameters)
                    .find(|parameter| match &ty.classifier {
                        Classifier::TypeParameter(id) => parameter.id == *id,
                        Classifier::TypeParameterName(name) => parameter.name == *name,
                        _ => unreachable!(),
                    })
                    .ok_or_else(|| self.unsupported("unknown type parameter"))?;
                identifier(out, &param.name, self.declaration)?;
                if ty.definitely_not_null {
                    if ty.nullable {
                        return Err(self.unsupported("conflicting type nullability"));
                    }
                    out.push_str(" & Any");
                }
            }
        }
        if !ty.arguments.is_empty() {
            out.push('<');
            for (index, argument) in ty.arguments.iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                match argument {
                    TypeArgument::Star => out.push('*'),
                    TypeArgument::Type(variance, ty) => {
                        out.push_str(variance_prefix(*variance));
                        self.write(out, ty)?;
                    }
                }
            }
            out.push('>');
        }
        if ty.nullable {
            out.push('?');
        }
        Ok(())
    }

    fn class(&self, out: &mut String, name: &ClassName) -> Result<(), KotlinError> {
        if name.local {
            return Err(self.unsupported("local class in type"));
        }
        let relative = name.relative_name();
        let first = relative.split('.').next().unwrap_or_default();
        let shadowed = self
            .owner
            .is_some_and(|owner| owner.relative_name() == first && owner != name)
            || self
                .local_parameters
                .iter()
                .chain(self.owner_parameters)
                .any(|parameter| parameter.name == first);
        let default_import = matches!(
            name.package(),
            "kotlin"
                | "kotlin/annotation"
                | "kotlin/collections"
                | "kotlin/comparisons"
                | "kotlin/io"
                | "kotlin/ranges"
                | "kotlin/sequences"
                | "kotlin/text"
                | "java/lang"
                | "kotlin/jvm"
        );
        qualified(
            out,
            if !shadowed && (name.package() == self.package || default_import) {
                relative
            } else {
                &name.id
            },
            self.declaration,
        )
    }

    fn function(&self, out: &mut String, ty: &Type, arity: usize) -> Result<(), KotlinError> {
        let extension = matches!(ty.annotations.as_slice(), [annotation] if annotation.id == "kotlin/ExtensionFunctionType");
        if ty.outer.is_some()
            || ty.definitely_not_null
            || (!extension && !ty.annotations.is_empty())
        {
            return Err(self.unsupported("annotated or malformed function type"));
        }
        let Some((returns, parameters)) = ty.arguments.split_last() else {
            return Err(self.unsupported("function type arguments"));
        };
        if parameters.len() != arity {
            return Err(self.unsupported("function type arity"));
        }
        let mut parameters = parameters.iter();
        if ty.nullable {
            out.push('(');
        }
        if extension {
            let receiver = parameters
                .next()
                .ok_or_else(|| self.unsupported("missing function type receiver"))?;
            self.receiver(out, function_argument(receiver, self.declaration)?)?;
            out.push('.');
        }
        out.push('(');
        for (index, param) in parameters.enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            self.write(out, function_argument(param, self.declaration)?)?;
        }
        out.push_str(") -> ");
        self.write(out, function_argument(returns, self.declaration)?)?;
        if ty.nullable {
            out.push_str(")?");
        }
        Ok(())
    }

    pub fn receiver(&self, out: &mut String, ty: &Type) -> Result<(), KotlinError> {
        let grouped = ty.nullable
            || ty
                .class_id()
                .is_some_and(|id| id.starts_with("kotlin/Function"));
        if grouped {
            out.push('(');
        }
        self.write(out, ty)?;
        if grouped {
            out.push(')');
        }
        Ok(())
    }

    pub fn unsupported(&self, feature: &'static str) -> KotlinError {
        KotlinError::unsupported(self.declaration, feature)
    }
}

fn function_argument<'a>(
    argument: &'a TypeArgument,
    declaration: &str,
) -> Result<&'a Type, KotlinError> {
    match argument {
        TypeArgument::Type(Variance::Invariant, ty) => Ok(ty),
        _ => Err(KotlinError::unsupported(
            declaration,
            "projected function type argument",
        )),
    }
}

pub(super) fn variance_prefix(variance: Variance) -> &'static str {
    match variance {
        Variance::In => "in ",
        Variance::Out => "out ",
        Variance::Invariant => "",
    }
}
