//! Recover Java type and enum switches from the SwitchBootstraps call.

mod bootstrap;
mod guards;

use std::io;
use std::sync::Arc;

use super::{switch, switch_mut};
use crate::code::code_constants::CONSTANT_CLASS;
use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, FunctionType, InvocationType};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::patterns::record;
use crate::decompiler::stats::{StatementKind, stat_edge::EdgeType};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::consts::PooledConstant;
use crate::types::VarType;

pub(crate) fn process(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    variables: VarProcessorId,
) -> io::Result<bool> {
    if !root
        .method(&cx.ir)
        .bytecode_version
        .has_switch_pattern_match()
        || !cx.options.pattern_matching
    {
        return Ok(false);
    }
    let changed = process_rec(cx, counters, root, variables, root)?;
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn process_rec(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    variables: VarProcessorId,
    stat: StatId,
) -> io::Result<bool> {
    let mut changed = false;
    let children = cx.ir[stat].stats.to_vec();
    for child in children {
        changed |= process_rec(cx, counters, root, variables, child)?;
    }
    if matches!(cx.ir[stat].kind, StatementKind::Switch(_))
        && let Some(pattern) = PatternSwitch::read(&cx.ir, stat)?
    {
        changed |= pattern.recover(cx, counters, root, variables)?;
    }
    Ok(changed)
}

struct PatternSwitch {
    stat: StatId,
    head: ExprId,
    selector: ExprId,
    restart: ExprId,
    bootstrap: Option<Arc<[Option<PooledConstant>]>>,
    is_enum: bool,
}

impl PatternSwitch {
    fn read(ir: &Ir, stat: StatId) -> io::Result<Option<Self>> {
        if ir[stat].phantom {
            return Ok(None);
        }
        let head = switch(ir, stat)
            .head_exprents
            .and_then(|list| ir[list].first().copied())
            .ok_or_else(|| invalid("Switch has no expression header"))?;
        let ExprKind::SwitchHead { value, .. } = ir[head].kind else {
            unreachable!("Switch header must be a SwitchHeadExprent");
        };
        let ExprKind::Invocation(invoke) = &ir[value].kind else {
            return Ok(None);
        };
        if invoke.kind != InvocationType::Dynamic
            || !matches!(invoke.name.as_str(), "typeSwitch" | "enumSwitch")
        {
            return Ok(None);
        }
        let &[selector, restart, ..] = invoke.parameters.as_slice() else {
            return Err(invalid(
                "Pattern switch has no selector or restart argument",
            ));
        };
        Ok(Some(Self {
            stat,
            head,
            selector,
            restart,
            bootstrap: invoke.bootstrap_arguments.clone(),
            is_enum: invoke.name == "enumSwitch",
        }))
    }

    fn recover(
        self,
        cx: &mut Cx,
        counters: &mut CounterContainer,
        root: StatId,
        variables: VarProcessorId,
    ) -> io::Result<bool> {
        let Some(guards) = guards::recover(cx, counters, root, self.stat, self.restart)? else {
            return Ok(false);
        };
        let mut default = None;
        for (index, guard) in guards.entries.into_iter().enumerate() {
            if switch(&cx.ir, self.stat).cases[index]
                .values
                .contains(&None)
            {
                default = Some(index);
            }
            self.recover_case(cx, counters, index, guard)?;
        }
        if let Some(default) = default {
            move_default_to_end(&mut cx.ir, self.stat, default);
        }
        bootstrap::install_labels(
            cx,
            counters,
            &self,
            variables,
            self.bootstrap.as_deref().unwrap_or_default(),
        )?;

        let (replacement, parent) = switch_region(&cx.ir, self.stat);
        if guards.guarded
            && let Some(loop_stat) = parent
            && matches!(cx.ir[loop_stat].kind, StatementKind::Do(_))
        {
            loop_stat.replace_with(&mut cx.ir, replacement);
            for edge in self
                .stat
                .get_predecessor_edges(&cx.ir, EdgeType::Continue.mask())
            {
                edge.change_type(&mut cx.ir, EdgeType::Break);
            }
        }
        self.inline_selector(cx, root, replacement);
        Ok(true)
    }

    fn recover_case(
        &self,
        cx: &mut Cx,
        counters: &mut CounterContainer,
        index: usize,
        guard: Option<ExprId>,
    ) -> io::Result<()> {
        let case = &switch(&cx.ir, self.stat).cases[index];
        let first = *case
            .values
            .first()
            .ok_or_else(|| invalid("Empty pattern switch case"))?;
        let Some(label) = first else { return Ok(()) };
        let mut case_stat = case.statement;
        if let Some(guard) = guard {
            let guards = &mut switch_mut(&mut cx.ir, self.stat).case_guards;
            if index >= guards.len() {
                guards.resize(index + 1, None);
            }
            guards[index] = Some(guard);
        }

        if matches!(cx.ir[label].kind, ExprKind::Constant { .. })
            && int_constant(&cx.ir, label).ok_or_else(|| invalid("Noninteger switch case index"))?
                == -1
        {
            let ir = &mut cx.ir;
            switch_mut(ir, self.stat).cases[index].values.remove(0);
            let null = constant(ir, counters, VarType::VARTYPE_NULL, ConstantValue::Null);
            let values = &mut switch_mut(ir, self.stat).cases[index].values;
            let before_default = values
                .iter()
                .position(Option::is_none)
                .unwrap_or(values.len());
            values.insert(before_default, Some(null));
        }

        if matches!(cx.ir[case_stat].kind, StatementKind::Sequence) {
            let sequence = case_stat;
            case_stat = cx.ir[sequence].stats[0];
            if cx.ir[sequence].stats.len() == 1 {
                sequence.replace_with(&mut cx.ir, case_stat);
            }
        }
        let pattern = switch(&cx.ir, self.stat)
            .case_guards
            .get(index)
            .copied()
            .flatten();
        let pattern = if let Some(pattern) = pattern
            && matches!(cx.ir[pattern].kind, ExprKind::Pattern(_))
        {
            switch_mut(&mut cx.ir, self.stat).case_guards[index] = None;
            Some(pattern)
        } else {
            let current_case = switch(&cx.ir, self.stat).cases[index].statement;
            identify_record(cx, counters, self.stat, current_case, false)?
        };
        if let Some(pattern) = pattern {
            let ty = Expr::expr_type(cx, pattern);
            let ty = constant(&mut cx.ir, counters, ty, ConstantValue::Null);
            let test = Expr::function(
                &mut cx.ir,
                counters,
                FunctionType::InstanceOf,
                vec![self.selector, ty, pattern],
                None,
            );
            switch_mut(&mut cx.ir, self.stat).cases[index].values[0] = Some(test);
        } else {
            self.recover_cast(cx, counters, case_stat, index, label)?;
        }
        Ok(())
    }

    fn recover_cast(
        &self,
        cx: &mut Cx,
        counters: &mut CounterContainer,
        case_stat: StatId,
        index: usize,
        label: ExprId,
    ) -> io::Result<()> {
        let ir = &cx.ir;
        let head = case_stat.get_basic_head(ir);
        let list = ir[head]
            .exprents
            .expect("Switch case head has no expressions");
        let Some(&first) = ir[list].first() else {
            return Ok(());
        };
        let Some((binding, value)) = ir[first].as_assignment() else {
            return Ok(());
        };
        if Expr::variable(ir, binding).is_none()
            || !is_pattern_cast_assignment(ir, self.head, value)
        {
            return Ok(());
        }

        let (checked, ty) = match &ir[value].kind {
            ExprKind::Variable(_) => {
                let Some(label) = int_constant(ir, label) else {
                    return Ok(());
                };
                let args = self.bootstrap.as_deref().unwrap_or_default();
                let argument = if label == -1 {
                    args.len().checked_sub(1)
                } else {
                    usize::try_from(label).ok()
                }
                .and_then(|argument| args.get(argument))
                .ok_or_else(|| {
                    invalid("Pattern switch case index is outside bootstrap arguments")
                })?;
                let Some(PooledConstant::Primitive(primitive)) = argument else {
                    return Ok(());
                };
                if primitive.ty != CONSTANT_CLASS {
                    return Ok(());
                }
                let ty = constant(
                    &mut cx.ir,
                    counters,
                    VarType::VARTYPE_CLASS,
                    primitive.value.clone(),
                );
                let switch = switch_mut(&mut cx.ir, self.stat);
                let case = &mut switch.cases[index];
                if let Some(default) = case.values.iter().position(Option::is_none) {
                    switch.default_edge = None;
                    case.values.remove(default);
                    case.edges.remove(default);
                }
                (value, ty)
            }
            ExprKind::Function { operands, .. } => (operands[0], operands[1]),
            _ => unreachable!("A pattern assignment must copy or cast the selector"),
        };
        let test = Expr::function(
            &mut cx.ir,
            counters,
            FunctionType::InstanceOf,
            vec![checked, ty, binding],
            None,
        );
        cx.ir[list].remove(0);
        switch_mut(&mut cx.ir, self.stat).cases[index].values[0] = Some(test);
        Ok(())
    }

    fn inline_selector(&self, cx: &mut Cx, root: StatId, replacement: StatId) {
        let labels: Vec<_> = switch(&cx.ir, self.stat)
            .cases
            .iter()
            .flat_map(|case| case.values.iter().flatten().copied())
            .collect();
        let selector =
            find_inline_selector(cx, root, self.stat, replacement, self.selector, &labels)
                .unwrap_or(self.selector);
        if selector != self.selector {
            for label in labels {
                if let Some(checked) = checked_operand(&cx.ir, label)
                    && Expr::equals(cx, checked, self.selector)
                {
                    let ExprKind::Function { operands, .. } = &mut cx.ir[label].kind else {
                        unreachable!();
                    };
                    operands[0] = selector;
                }
            }
        }
        let ExprKind::SwitchHead { value, .. } = &mut cx.ir[self.head].kind else {
            unreachable!();
        };
        *value = selector;
    }
}

fn find_inline_selector(
    cx: &mut Cx,
    root: StatId,
    stat: StatId,
    replacement: StatId,
    selector: ExprId,
    labels: &[ExprId],
) -> Option<ExprId> {
    let ir = &cx.ir;
    let mut list = ir[stat.get_basic_head(ir)]
        .exprents
        .expect("Switch head has no expressions");
    if ir[list].is_empty()
        && let [edge] = replacement
            .get_predecessor_edges(ir, EdgeType::Regular.mask())
            .as_slice()
        && matches!(ir[ir[*edge].source].kind, StatementKind::BasicBlock { .. })
    {
        list = ir[ir[*edge].source].exprents?;
    }
    Expr::variable(ir, selector)?;
    let (assigned, value) = ir[*ir[list].last()?].as_assignment()?;
    Expr::variable(ir, assigned)?;
    if !Expr::equals(cx, selector, assigned) {
        return None;
    }
    let mut allowed = vec![assigned];
    allowed.extend(labels.iter().filter_map(|&label| {
        let checked = checked_operand(ir, label)?;
        (Expr::variable(ir, checked).is_some() && Expr::equals(cx, checked, selector))
            .then_some(checked)
    }));
    if Expr::is_var_referenced_in_stat(ir, selector, root, &allowed) {
        return None;
    }
    cx.ir[list].pop();
    Some(value)
}

fn switch_region(ir: &Ir, stat: StatId) -> (StatId, Option<StatId>) {
    if let Some(parent) = ir[stat].parent
        && matches!(ir[parent].kind, StatementKind::Sequence)
        && let [first, tail] = &ir[parent].stats[..]
        && *first == stat
        && matches!(ir[*tail].kind, StatementKind::BasicBlock { .. })
        && let Some(list) = ir[*tail].exprents
        && let [expr] = ir[list].as_slice()
        && matches!(ir[*expr].kind, ExprKind::Exit { value: Some(_), .. })
    {
        (parent, ir[parent].parent)
    } else {
        (stat, ir[stat].parent)
    }
}

fn move_default_to_end(ir: &mut Ir, stat: StatId, index: usize) {
    let switch = switch_mut(ir, stat);
    let case = switch.cases.remove(index);
    switch.cases.push(case);
    if index < switch.case_guards.len() {
        if switch.case_guards[index].is_some() {
            if switch.case_guards.len() < switch.cases.len() {
                switch.case_guards.resize(switch.cases.len(), None);
            }
            let guard = switch.case_guards.remove(index);
            switch.case_guards.push(guard);
        } else {
            switch.case_guards.remove(index);
        }
    }
}

fn is_pattern_cast_assignment(ir: &Ir, head: ExprId, value: ExprId) -> bool {
    let checked = match &ir[value].kind {
        ExprKind::Variable(_) => value,
        ExprKind::Function {
            op: FunctionType::Cast,
            operands,
            ..
        } if operands.len() >= 2 && matches!(ir[operands[1]].kind, ExprKind::Constant { .. }) => {
            operands[0]
        }
        _ => return false,
    };
    Expr::variable(ir, checked).is_some_and(|var| Expr::contains_var(ir, head, var.pair()))
}

fn checked_operand(ir: &Ir, label: ExprId) -> Option<ExprId> {
    match &ir[label].kind {
        ExprKind::Function {
            op: FunctionType::InstanceOf,
            operands,
            ..
        } => Some(operands[0]),
        _ => None,
    }
}

fn identify_record(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    case: StatId,
    simulate: bool,
) -> io::Result<Option<ExprId>> {
    let ir = &cx.ir;
    let head = case.get_basic_head(ir);
    let Some(list) = ir[head].exprents else {
        return Ok(None);
    };
    let Some((store, _)) = ir[list].first().and_then(|&expr| ir[expr].as_assignment()) else {
        return Ok(None);
    };
    if Expr::variable(ir, store).is_none() {
        return Ok(None);
    }
    let ty = Expr::expr_type(cx, store);
    let pattern = record::identify(cx, counters, stat, case, store, ty, simulate)?;
    if pattern.is_some() && !simulate {
        cx.ir[list].remove(0);
    }
    Ok(pattern)
}

fn int_constant(ir: &Ir, expr: ExprId) -> Option<i32> {
    match ir[expr].kind {
        ExprKind::Constant {
            value: ConstantValue::Integer(value),
            ..
        } => Some(value),
        _ => None,
    }
}

fn constant(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    ty: VarType,
    value: ConstantValue,
) -> ExprId {
    Expr::new(ir, counters, Expr::constant(ty, value, false), None)
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
