use std::fmt::Write;

use super::{DynamicHelper, LiftError, Machine};

pub(crate) const CALL_SITE: &str = "org/codehaus/groovy/runtime/callsite/CallSite";
const ADAPTER: &str = "org/codehaus/groovy/runtime/ScriptBytecodeAdapter";
const OBJECT: &str = "Ljava/lang/Object;";
const ARRAY: &str = "[Ljava/lang/Object;";
const CLASS: &str = "Ljava/lang/Class;";
const GROOVY_OBJECT: &str = "Lgroovy/lang/GroovyObject;";
const STRING: &str = "Ljava/lang/String;";

#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct GroovyDispatch {
    pub(crate) member: u16,
    pub(crate) name: String,
    pub(crate) catches: Vec<u16>,
}

impl Machine<'_, '_> {
    pub(super) fn groovy_dispatch(
        &self,
        index: u16,
        (owner, method, descriptor): (&str, &str, &str),
        opcode: u8,
    ) -> Result<Option<GroovyDispatch>, LiftError> {
        if self.dynamic_helpers.is_none()
            || !matches!((opcode, owner), (0xb8, ADAPTER) | (0xb9, CALL_SITE))
            || !throws_throwable(owner, method, descriptor)
        {
            return Ok(None);
        }
        // Unchecked inference alone would make a Java catch of a specific checked
        // subtype unreachable. Keep those catches in the bridge's static throws
        // contract. Catch-all/finally and the broad types already remain reachable.
        let offset = self.debug_offset(self.offset);
        let pool = &self.class.pool;
        let mut catches = Vec::new();
        for handler in &self.code.exceptions {
            let catch = handler.catch_type;
            if catch != 0
                && (u32::from(handler.start_pc)..u32::from(handler.end_pc)).contains(&offset)
                && !matches!(
                    pool.class_name(catch)?,
                    "java/lang/Throwable"
                        | "java/lang/Exception"
                        | "java/lang/RuntimeException"
                        | "java/lang/Error"
                )
            {
                catches.push(catch);
            }
        }
        catches.sort_unstable();
        catches.dedup();
        let mut name = format!("$vf$groovy${method}${index}");
        for catch in &catches {
            write!(name, "${catch}").unwrap();
        }
        while self.current_member_named(&name, true)? {
            name.push('$');
        }
        Ok(Some(GroovyDispatch { member: index, name, catches }))
    }

    pub(super) fn record_groovy_dispatch(&self, bridge: GroovyDispatch) {
        if let Some(helpers) = &self.dynamic_helpers {
            helpers.borrow_mut().insert(DynamicHelper::GroovyDispatch(bridge));
        }
    }
}

// The runtime is usually not supplied as a decompiler input. Use the exact
// checked dispatch signatures of these two Groovy runtime types, not a Java-
// wide rule or a prefix match that also changes their nonthrowing methods.
fn throws_throwable(owner: &str, method: &str, descriptor: &str) -> bool {
    let Some((parameters, result)) = descriptor
        .strip_prefix('(')
        .and_then(|ty| ty.split_once(')'))
    else {
        return false;
    };
    let signature = |args: &[&str], ret| result == ret && has_parameters(parameters, args);
    if owner == CALL_SITE {
        if result != OBJECT {
            return false;
        }
        let head = match method {
            "call" | "callSafe" | "callConstructor" => OBJECT,
            "callCurrent" => GROOVY_OBJECT,
            "callStatic" => CLASS,
            "getProperty" | "callGetProperty" | "callGetPropertySafe"
            | "callGroovyObjectGetProperty" | "callGroovyObjectGetPropertySafe" => {
                return parameters == OBJECT;
            }
            _ => return false,
        };
        return parameters.strip_prefix(head).is_some_and(|tail| {
            tail == ARRAY
                || tail.len() <= 4 * OBJECT.len()
                    && tail.len().is_multiple_of(OBJECT.len())
                    && tail
                        .as_bytes()
                        .chunks_exact(OBJECT.len())
                        .all(|part| part == OBJECT.as_bytes())
        });
    }

    let base = method.strip_suffix("SpreadSafe").or_else(|| method.strip_suffix("Safe"));
    match base.unwrap_or(method) {
        "invokeMethodN" => signature(&[CLASS, OBJECT, STRING, ARRAY], OBJECT),
        "invokeMethod0" if base.is_some() => signature(&[CLASS, OBJECT, STRING, ARRAY], OBJECT),
        "invokeMethod0" => signature(&[CLASS, OBJECT, STRING], OBJECT),
        "invokeMethodOnCurrentN" | "invokeMethodOnSuperN" => {
            signature(&[CLASS, GROOVY_OBJECT, STRING, ARRAY], OBJECT)
        }
        "invokeMethodOnCurrent0" | "invokeMethodOnSuper0" if base.is_some() => {
            signature(&[CLASS, GROOVY_OBJECT, STRING, ARRAY], OBJECT)
        }
        "invokeMethodOnCurrent0" | "invokeMethodOnSuper0" => {
            signature(&[CLASS, GROOVY_OBJECT, STRING], OBJECT)
        }
        "getField" | "getFieldOnSuper" | "getProperty" => signature(&[CLASS, OBJECT, STRING], OBJECT),
        "setField" | "setFieldOnSuper" | "setProperty" => signature(&[OBJECT, CLASS, OBJECT, STRING], "V"),
        "getGroovyObjectField" | "getGroovyObjectProperty" | "getPropertyOnSuper" => {
            signature(&[CLASS, GROOVY_OBJECT, STRING], OBJECT)
        }
        "setGroovyObjectField" | "setGroovyObjectProperty" | "setPropertyOnSuper" => {
            signature(&[OBJECT, CLASS, GROOVY_OBJECT, STRING], "V")
        }
        _ if base.is_some() => false,
        "invokeStaticMethodN" => signature(&[CLASS, CLASS, STRING, ARRAY], OBJECT),
        "invokeStaticMethod0" => signature(&[CLASS, CLASS, STRING], OBJECT),
        "invokeNewN" => signature(&[CLASS, CLASS, OBJECT], OBJECT),
        "invokeNew0" => signature(&[CLASS, CLASS], OBJECT),
        "selectConstructorAndTransformArguments" => signature(&[ARRAY, "I", CLASS], "I"),
        "invokeClosure" => signature(&[OBJECT, ARRAY], OBJECT),
        "castToType" | "asType" => signature(&[OBJECT, CLASS], OBJECT),
        "createRange" => signature(&[OBJECT, OBJECT, "Z"], "Ljava/util/List;"),
        "isCase" | "isNotCase" => signature(&[OBJECT, OBJECT], "Z"),
        "findRegex" => signature(&[OBJECT, OBJECT], "Ljava/util/regex/Matcher;"),
        "unaryMinus" | "unaryPlus" | "bitwiseNegate" => signature(&[OBJECT], OBJECT),
        _ => false,
    }
}

fn has_parameters(mut parameters: &str, expected: &[&str]) -> bool {
    for &ty in expected {
        let Some(rest) = parameters.strip_prefix(ty) else {
            return false;
        };
        parameters = rest;
    }
    parameters.is_empty()
}
