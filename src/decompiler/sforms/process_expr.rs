// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The expression-specific `processSforms` transfers.

use crate::decompiler::exps::{Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, Ir};
use crate::types::CodeType;

use super::maps::VarMapHolder;
use super::{Transfer, Version, VersionAnalysis, variable};

impl<A: VersionAnalysis> Transfer<'_, A> {
    pub(super) fn process(&mut self, ir: &mut Ir, id: ExprId, maps: &mut VarMapHolder) {
        match &ir[id].kind {
            ExprKind::Variable(_) => self.var_read(ir, id, maps),
            ExprKind::Assignment {
                left,
                right,
                compound,
            } => {
                self.process_assignment(ir, *left, *right, compound.is_some(), maps);
            }
            ExprKind::If { condition } => {
                // This wrapper keeps the condition's true and false maps.
                self.process(ir, *condition, maps);
            }
            ExprKind::Function {
                op: FunctionType::BoolNot,
                operands,
            } => {
                self.process(ir, operands[0], maps);
                maps.swap();
            }
            ExprKind::Function {
                op: FunctionType::InstanceOf,
                operands,
            } => {
                self.process(ir, operands[0], maps);
                maps.to_normal();
            }
            ExprKind::Field(field) => {
                if let Some(instance) = field.instance {
                    self.process(ir, instance, maps);
                }
                self.field_read(ir, id, maps.normal_mut());
            }
            kind => {
                let dirty_fields = matches!(kind, ExprKind::Invocation(_))
                    || matches!(kind, ExprKind::New { new_type, .. } if new_type.ty == CodeType::Object);
                // Keep handles independently of the arena while visiting mutable children.
                let children: Vec<_> = Expr::children(ir, id).collect();
                for child in children {
                    self.process(ir, child, maps);
                    maps.to_normal();
                }
                if A::TRACK_FIELDS && dirty_fields {
                    maps.normal_mut().clear_fields();
                }
            }
        }
    }

    fn process_assignment(
        &mut self,
        ir: &mut Ir,
        left: ExprId,
        right: ExprId,
        compound: bool,
        maps: &mut VarMapHolder,
    ) {
        match &ir[left].kind {
            ExprKind::Variable(_) if compound => {
                self.process(ir, left, maps);
                self.process(ir, right, maps);
                let normal = maps.to_normal();
                let phantom = self.analysis.phantom(variable(ir, left));
                normal.set_current(phantom.var, phantom.version);
            }
            ExprKind::Variable(_) => {
                self.process(ir, right, maps);
                self.assign(ir, left, maps.to_normal());
                if A::TRACK_DIRECT_ASSIGNMENTS {
                    let right_version = match &ir[right].kind {
                        ExprKind::Variable(_) => Some(variable(ir, right)),
                        ExprKind::Field(_) => {
                            Some(Version::new(self.analysis.field_index(ir[right].id), 0))
                        }
                        _ => None,
                    };
                    if let Some(right_version) = right_version {
                        self.analysis
                            .mark_assignment(variable(ir, left), right_version);
                    }
                }
            }
            kind => {
                let writes_field = matches!(kind, ExprKind::Field(_));
                self.process(ir, left, maps);
                assert!(
                    maps.is_normal(),
                    "Left side of assignment must have a normal variable map"
                );
                self.process(ir, right, maps);
                let normal = maps.to_normal();
                if writes_field {
                    normal.clear_fields();
                }
            }
        }
    }
}
