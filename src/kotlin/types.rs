//! Kotlin metadata classifier names, JVM descriptors and source type spelling.

use std::io;

use crate::{decompiler::expr_processor::get_cast_type_name, engine::Cx, types::VarType};

const JVM_FUNCTION: &str = "kotlin/jvm/functions/Function";

// The collector must reserve every mapped Kotlin name, including the mutable
// and read-only names that share one erased JVM type.
macro_rules! class_mappings {
    ($($kotlin:literal => $java:literal),* $(,)?) => {
        pub(crate) const MAPPED_CLASSES: &[&str] = &[$($kotlin),*];

        fn mapped_class(name: &str) -> Option<&'static str> {
            match name {
                $($kotlin => Some($java),)*
                _ => None,
            }
        }
    };
}

class_mappings! {
    "kotlin/Any" => "java/lang/Object",
    "kotlin/Boolean" => "java/lang/Boolean",
    "kotlin/Byte" => "java/lang/Byte",
    "kotlin/Char" => "java/lang/Character",
    "kotlin/CharSequence" => "java/lang/CharSequence",
    "kotlin/Comparable" => "java/lang/Comparable",
    "kotlin/Double" => "java/lang/Double",
    "kotlin/Enum" => "java/lang/Enum",
    "kotlin/Float" => "java/lang/Float",
    "kotlin/Int" => "java/lang/Integer",
    "kotlin/Long" => "java/lang/Long",
    "kotlin/Nothing" => "java/lang/Void",
    "kotlin/Number" => "java/lang/Number",
    "kotlin/Short" => "java/lang/Short",
    "kotlin/String" => "java/lang/String",
    "kotlin/Throwable" => "java/lang/Throwable",
    "kotlin/collections/MutableIterable" => "java/lang/Iterable",
    "kotlin/collections/Iterable" => "java/lang/Iterable",
    "kotlin/collections/MutableCollection" => "java/util/Collection",
    "kotlin/collections/MutableMap" => "java/util/Map",
    "kotlin/collections/MutableList" => "java/util/List",
    "kotlin/collections/MutableSet" => "java/util/Set",
    "kotlin/collections/MutableIterator" => "java/util/Iterator",
    "kotlin/collections/MutableListIterator" => "java/util/ListIterator",
    "kotlin/collections/MutableMap$MutableEntry" => "java/util/Map$Entry",
    "kotlin/collections/Collection" => "java/util/Collection",
    "kotlin/collections/Map" => "java/util/Map",
    "kotlin/collections/List" => "java/util/List",
    "kotlin/collections/ListIterator" => "java/util/ListIterator",
    "kotlin/collections/Set" => "java/util/Set",
    "kotlin/collections/Iterator" => "java/util/Iterator",
    "kotlin/collections/Map$Entry" => "java/util/Map$Entry",
}

fn primitive_descriptor(name: &str) -> Option<&'static str> {
    Some(match name {
        "Int" => "I",
        "Long" => "J",
        "Short" => "S",
        "Byte" => "B",
        "Boolean" => "Z",
        "Char" => "C",
        "Float" => "F",
        "Double" => "D",
        "Unit" => "V",
        _ => return None,
    })
}

/// Translate a classifier from Kotlin metadata into the descriptor used for member lookup.
pub fn java_signature(name: &str, nullable: bool) -> String {
    let name = name
        .strip_prefix('L')
        .and_then(|s| s.strip_suffix(';'))
        .unwrap_or(name);
    let binary = name.replace('.', "$");
    if let Some(simple) = binary.strip_prefix("kotlin/") {
        if !nullable && let Some(primitive) = primitive_descriptor(simple) {
            return primitive.to_owned();
        }
        if simple.ends_with("$Companion")
            && primitive_descriptor(&simple.replace("$Companion", "")).is_some()
        {
            let primitive = simple.split('$').next().unwrap();
            return format!("Lkotlin/jvm/internal/{primitive}CompanionObject;");
        }
        if simple.ends_with("Array")
            && let Some(primitive) = primitive_descriptor(&simple.replace("Array", ""))
        {
            return format!("[{primitive}");
        }
        if let Some(java) = mapped_class(&binary) {
            return format!("L{java};");
        }
        if let Some(arity) = simple.strip_prefix("Function")
            && let Ok(count) = arity.parse::<i32>()
        {
            let suffix = if count > 22 { "N" } else { arity };
            return format!("L{JVM_FUNCTION}{suffix};");
        }
    }
    format!("L{binary};")
}

fn generic_collection(internal: &str) -> Option<&'static str> {
    Some(match internal {
        "java/util/Map" => "MutableMap",
        "java/util/HashMap" => "HashMap",
        "java/util/List" => "MutableList",
        "java/util/ArrayList" => "ArrayList",
        "java/util/Set" => "MutableSet",
        "java/util/HashSet" => "HashSet",
        "java/util/Collection" => "MutableCollection",
        "java/util/Iterator" => "MutableIterator",
        "java/util/Map$Entry" => "MutableMap.MutableEntry",
        "java/lang/Iterable" => "MutableIterable",
        _ => return None,
    })
}

/// Spell a JVM type in Kotlin source, collecting imports in the enclosing class.
pub fn kotlin_type(
    cx: &mut Cx,
    ty: Option<&VarType>,
    include_outer_classes: bool,
) -> io::Result<String> {
    let Some(ty) = ty else {
        return Ok("*".to_owned());
    };
    let internal = ty
        .value
        .as_deref()
        .ok_or_else(|| io::Error::other("Kotlin type has no classifier"))?;
    let element = if let Some(arity) = internal.strip_prefix(JVM_FUNCTION) {
        function_type(cx, ty, arity)?
    } else if internal == "java/lang/Integer" {
        "Int".to_owned()
    } else if internal == "java/lang/Object" {
        "Any".to_owned()
    } else if let Some(name) = generic_collection(internal).filter(|_| ty.is_generic()) {
        let args = ty
            .arguments()
            .iter()
            .map(|arg| kotlin_type(cx, arg.as_ref(), true))
            .collect::<io::Result<Vec<_>>>()?;
        if args.is_empty() {
            name.to_owned()
        } else {
            format!("{name}<{}>", args.join(", "))
        }
    } else {
        let cast = get_cast_type_name(cx, ty);
        let cast = if cast == "<undefinedtype>" {
            "Any"
        } else {
            &cast
        };
        let cast = if include_outer_classes {
            cast
        } else {
            cast.rsplit('.').next().unwrap()
        };
        return Ok(map_java_type(cast));
    };
    let rank = usize::try_from(ty.array_dim)
        .map_err(|_| io::Error::other("Negative Kotlin array rank"))?;
    Ok(format!(
        "{}{element}{}",
        "Array<".repeat(rank),
        ">".repeat(rank)
    ))
}

fn function_type(cx: &mut Cx, ty: &VarType, arity: &str) -> io::Result<String> {
    if arity == "N" || !ty.is_generic_type() {
        let cast = get_cast_type_name(cx, ty);
        return Ok(if cast == "<undefinedtype>" {
            "Any".to_owned()
        } else {
            map_java_type(&cast)
        });
    }
    let count = arity
        .parse::<usize>()
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    let args = ty.arguments();
    let result = args
        .get(count)
        .ok_or_else(|| io::Error::other("Kotlin function type is missing a return type"))?;
    let mut argument = |ty: Option<&VarType>| -> io::Result<String> {
        let ty =
            ty.ok_or_else(|| io::Error::other("Missing type argument in Kotlin function type"))?;
        let name = kotlin_type(cx, Some(ty), true)?;
        Ok(if ty.name().starts_with(JVM_FUNCTION) {
            format!("({name})")
        } else {
            name
        })
    };
    let mut params = Vec::with_capacity(count);
    for param in &args[..count] {
        params.push(format!("{}?", argument(param.as_ref())?));
    }
    Ok(format!(
        "({}) -> {}",
        params.join(", "),
        argument(result.as_ref())?
    ))
}

fn primitive_name(java: &str) -> Option<&'static str> {
    Some(match java {
        "boolean" => "Boolean",
        "byte" => "Byte",
        "char" => "Char",
        "short" => "Short",
        "int" => "Int",
        "long" => "Long",
        "float" => "Float",
        "double" => "Double",
        _ => return None,
    })
}

fn map_java_type(name: &str) -> String {
    if name == "?" {
        return "*".to_owned();
    }
    if let Some(bound) = name.strip_prefix("? extends ") {
        return format!("out {bound}");
    }
    if let Some(bound) = name.strip_prefix("? super ") {
        return format!("in {bound}");
    }
    if let Some(element) = name.strip_suffix("[]") {
        return match primitive_name(element) {
            Some(simple) => format!("{simple}Array"),
            None => format!("Array<{}>", map_java_type(element)),
        };
    }
    if let Some(simple) = primitive_name(name) {
        return simple.to_owned();
    }
    if name == "void" {
        return "Unit".to_owned();
    }
    // KTypes applies its greedy generic-name pattern to each dotted component.
    crate::util::java_str::split(name, ".")
        .into_iter()
        .map(|part| {
            if let Some((base, args)) = part.strip_suffix('>').and_then(|s| s.rsplit_once('<'))
                && !base.is_empty()
                && !args.is_empty()
            {
                let args: Vec<_> = crate::util::java_str::split(args, ",")
                    .into_iter()
                    .map(|arg| map_java_type(arg.trim_matches(|c| c <= '\u{20}')))
                    .collect();
                format!("{}<{}>", map_java_type(base), args.join(", "))
            } else {
                part.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(".")
}
