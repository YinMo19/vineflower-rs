// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::descriptor::Type as JvmType;

use crate::kotlin::{ClassDeclaration, ClassKind, MemberKind, Modality};

use super::{Bytecode, KotlinError, Plan, error};

/// Recover the source construct that produces component/copy/equality helpers.
/// A data flag alone is insufficient: every primary parameter must have been
/// proven to initialize its matching property and each component read must
/// agree with that mapping. User-written overrides are ordinary declarations.
pub(super) fn validate(
    bytecode: &Bytecode<'_, '_>,
    declaration: &ClassDeclaration,
    plan: &Plan<'_, '_, '_>,
) -> Result<(), KotlinError> {
    let unsupported = |reason| error(bytecode.owner, reason);
    if declaration.kind != ClassKind::Class
        || declaration.flags.modality() != Modality::Final
        || plan.promoted.is_empty()
        || plan.promoted.iter().any(Option::is_none)
    {
        return Err(unsupported(
            "data class requires a primary constructor of verified properties",
        ));
    }
    let fields = plan
        .promoted
        .iter()
        .map(|&index| {
            let property = &plan.properties[index.expect("data-class promotion verified")];
            (
                property
                    .property
                    .signature
                    .field
                    .as_ref()
                    .expect("promoted property has a JVM field"),
                property
                    .field
                    .expect("promoted property has a backing field"),
            )
        })
        .collect::<Vec<_>>();
    let mut found = vec![false; fields.len()];
    let mut copy = false;
    for function in &declaration.members.functions {
        if function.flags.member_kind() != MemberKind::Synthesized {
            continue;
        }
        let signature = function
            .signature
            .as_ref()
            .ok_or_else(|| unsupported("data class helper has no JVM signature"))?;
        let method = bytecode
            .find_method(signature)?
            .filter(|method| method.access_flags & crate::kotlin::body::STATIC == 0)
            .ok_or_else(|| unsupported("missing instance data class helper implementation"))?;
        if function.name != signature.name {
            return Err(unsupported("renamed data class helper"));
        }
        match signature.name.as_str() {
            "copy" => {
                if copy
                    || !matches!(&signature.descriptor.return_type, JvmType::Object(owner) if owner == bytecode.owner)
                    || function.parameters.len() != plan.parameters.len()
                    || function
                        .parameters
                        .iter()
                        .zip(plan.parameters)
                        .any(|(copy, primary)| {
                            !copy.flags.has(1) || copy.name != primary.name || copy.ty != primary.ty
                        })
                    || !signature
                        .descriptor
                        .parameters
                        .iter()
                        .eq(fields.iter().map(|(signature, _)| &signature.descriptor))
                {
                    return Err(unsupported(
                        "data class copy signature disagrees with primary properties",
                    ));
                }
                super::body::verify_copy(bytecode, signature, &function.parameters)?;
                let signatures = fields
                    .iter()
                    .map(|&(field, member)| {
                        Ok((field, bytecode.class.pool.utf8(member.descriptor_index)?))
                    })
                    .collect::<Result<Vec<_>, KotlinError>>()?;
                super::body::verify_copy_defaults(
                    bytecode,
                    signature,
                    &function.parameters,
                    &signatures,
                )?;
                copy = true;
            }
            "equals" | "hashCode" | "toString" => {
                if !super::overrides_any(&signature.name, &signature.descriptor) {
                    return Err(unsupported(
                        "data class Any override has unexpected JVM signature",
                    ));
                }
            }
            name => {
                let Some(index) = name
                    .strip_prefix("component")
                    .and_then(|id| id.parse::<usize>().ok())
                    .and_then(|id| id.checked_sub(1))
                else {
                    return Err(unsupported("unrecognized synthesized data class member"));
                };
                let Some(&(field, backing)) = fields.get(index) else {
                    return Err(unsupported("data class component has no matching property"));
                };
                if found[index]
                    || !function.flags.has(8)
                    || !signature.descriptor.parameters.is_empty()
                    || signature.descriptor.return_type != field.descriptor
                {
                    return Err(unsupported(
                        "data class component signature disagrees with primary property",
                    ));
                }
                let descriptor = bytecode.class.pool.utf8(backing.descriptor_index)?;
                bytecode.default_getter(method, field, descriptor, name)?;
                found[index] = true;
            }
        }
    }
    if found.contains(&false) || !copy {
        return Err(unsupported("missing synthesized data class members"));
    }
    Ok(())
}
