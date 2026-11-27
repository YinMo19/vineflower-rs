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
                op: FunctionType::Ternary,
                operands,
                ..
            } => {
                let [test, then_arm, else_arm] = operands[..] else {
                    unreachable!()
                };
                self.process(ir, test, maps);
                let mut then_maps = VarMapHolder::normal(maps.take_alternative(false));
                self.process(ir, then_arm, &mut then_maps);
                self.process(ir, else_arm, maps);
                maps.merge_ternary(then_maps);
            }
            ExprKind::Function {
                op: op @ (FunctionType::BoolAnd | FunctionType::BoolOr),
                operands,
                ..
            } => {
                let [left, right] = operands[..] else {
                    unreachable!()
                };
                let evaluate_on_true = *op == FunctionType::BoolAnd;
                self.process(ir, left, maps);
                let skipped = maps.take_alternative(evaluate_on_true);
                self.process(ir, right, maps);
                maps.merge_outcome(!evaluate_on_true, &skipped);
            }
            ExprKind::Function {
                op: FunctionType::Ppi | FunctionType::Ipp | FunctionType::Mmi | FunctionType::Imm,
                operands,
                ..
            } => {
                let value = operands[0];
                self.process(ir, value, maps);
                match ir[value].kind {
                    ExprKind::Variable(_) => {
                        let phantom = self.analysis.phantom(variable(ir, value));
                        maps.normal_mut().set_current(phantom.var, phantom.version);
                    }
                    ExprKind::Field(_) => maps.normal_mut().clear_fields(),
                    _ => {}
                }
            }
            ExprKind::Function {
                op: FunctionType::BoolNot,
                operands,
                ..
            } => {
                self.process(ir, operands[0], maps);
                maps.swap();
            }
            ExprKind::Function {
                op: FunctionType::InstanceOf,
                operands,
                ..
            } => {
                let operand = operands[0];
                let pattern = (operands.len() == 3).then(|| operands[2]);
                self.process(ir, operand, maps);
                maps.merge_branches();
                if let Some(pattern) = pattern {
                    let if_true = maps.true_branch_mut();
                    for variable in Expr::pattern_vars(ir, pattern) {
                        self.assign(ir, variable, if_true);
                    }
                }
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
                    maps.merge_branches();
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
                let normal = maps.merge_branches();
                let phantom = self.analysis.phantom(variable(ir, left));
                normal.set_current(phantom.var, phantom.version);
            }
            ExprKind::Variable(_) => {
                self.process(ir, right, maps);
                self.assign(ir, left, maps.merge_branches());
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
                let normal = maps.merge_branches();
                if writes_field {
                    normal.clear_fields();
                }
            }
        }
    }
}
