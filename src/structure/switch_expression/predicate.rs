use std::{
    cell::RefCell,
    collections::{BTreeMap, btree_map::Entry},
    mem,
    ops::RangeInclusive,
};

use crate::{bytecode::Instruction, cfg::ControlFlowGraph, lift::Machine, source_text::Document};

use super::{CaseLabel, Rule, RuleResult, SwitchExpression, surrounded};
use crate::structure::{
    Condition, Emitter, Line, Region, StructureError, assertions, flow::Layout, protected::Exceptions,
};

const MAX_BLOCKS: usize = 128;

pub(in crate::structure) struct Cut {
    pub(in crate::structure) header: usize,
    owners: BTreeMap<usize, usize>,
    pub(in crate::structure) outcomes: [usize; 2],
}

impl Cut {
    /// Each target owns a disjoint subgraph. Stop at the first two blocks
    /// shared by different rules, without swallowing either continuation.
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        header: usize,
        join: Option<usize>,
    ) -> Option<Self> {
        let cfg = &graph.blocks;
        let dispatch = &cfg[header];
        if dispatch.successors.len() < 2 || !dispatch.exception_predecessors.is_empty() {
            return None;
        }
        let same_handlers = |block: usize| {
            cfg[block].exception_predecessors.is_empty()
                && cfg[block].exception_successors == dispatch.exception_successors
        };
        let mut frontier: BTreeMap<usize, Option<usize>> = dispatch.successors.iter()
            .map(|&target| (target, Some(target)))
            .collect();
        let mut owners = BTreeMap::new();
        while owners.len() < MAX_BLOCKS {
            if frontier.len() == 2 && frontier.values().all(Option::is_none) {
                let mut exits = frontier.into_keys();
                let outcomes = [exits.next()?, exits.next()?];
                let (&last, _) = owners.last_key_value()?;
                if outcomes[0] <= last || outcomes.iter().any(|&block| {
                    !same_handlers(block) || (join != Some(block)
                        && cfg[block].predecessors.iter().any(|pred| !owners.contains_key(pred)))
                }) || owners.iter().any(|(&block, &owner)| {
                    cfg[block].predecessors.iter().any(|&pred| {
                        owners.get(&pred) != Some(&owner) && !(block == owner && pred == header)
                    })
                }) {
                    return None;
                }
                return Some(Self { header, owners, outcomes });
            }
            let (block, owner) = frontier.pop_first()?;
            let owner = owner?;
            let body = &cfg[block];
            if block <= header || !same_handlers(block) || (body.successors.is_empty()
                && instructions[body.instructions.end - 1].opcode != 0xbf)
            {
                return None;
            }
            owners.insert(block, owner);
            for &next in &body.successors {
                if let Some(&previous) = owners.get(&next) {
                    if previous != owner {
                        return None;
                    }
                } else {
                    match frontier.entry(next) {
                        Entry::Vacant(entry) => { entry.insert(Some(owner)); }
                        Entry::Occupied(mut entry) if *entry.get() != Some(owner) => {
                            entry.insert(None);
                        }
                        Entry::Occupied(_) => {}
                    }
                }
            }
        }
        None
    }

    pub(in crate::structure) fn owns(&self, block: usize) -> bool {
        self.owners.contains_key(&block)
    }
}

/// A predicate yield inside a natural loop is a lexical transfer, not a
/// second loop continuation. Retry layout only when ordinary classification
/// cannot handle the graph and a closed switch cut proves such transfers.
pub(in crate::structure) fn loop_layout(
    graph: &ControlFlowGraph,
    instructions: &[Instruction],
    assertions: Option<&assertions::Sites>,
    exceptions: &Exceptions,
    original: StructureError,
) -> Result<Layout, StructureError> {
    if !matches!(original, StructureError::Flow { .. }) {
        return Err(original);
    }
    let dispatches = graph.blocks.iter().enumerate().filter(|(_, block)| {
        matches!(instructions[block.instructions.end - 1].opcode, 0xaa | 0xab)
    });
    let mut dispatches = dispatches.peekable();
    if dispatches.peek().is_none() {
        return Err(original);
    }
    let joins = graph.immediate_postdominators();
    let cuts: Vec<_> = dispatches.filter_map(|(header, _)| {
        Cut::prove(instructions, graph, header, joins[header])
    }).collect();
    if cuts.is_empty() {
        return Err(original);
    }
    Layout::with_predicate_cuts(graph, instructions, assertions, exceptions, &cuts)
}

pub(in crate::structure) struct Scope<'r, 'a, 'c> {
    pub(in crate::structure) cut: &'r Cut,
    exits: RefCell<[Vec<Machine<'a, 'c>>; 2]>,
}

impl Scope<'_, '_, '_> {
    pub(in crate::structure) fn outcome(&self, block: usize) -> Option<usize> {
        self.cut.outcomes.iter().position(|&outcome| outcome == block)
    }
}

#[derive(Debug)]
pub(in crate::structure) struct Edge {
    outcome: usize,
    index: usize,
}

struct Outcome<'a, 'c> {
    state: Machine<'a, 'c>,
    declarations: Vec<Document>,
    copies: Vec<Vec<Document>>,
}

impl Emitter<'_> {
    pub(in crate::structure) fn predicate_exit<'a, 'c>(
        &mut self,
        scope: &Scope<'_, 'a, 'c>,
        outcome: usize,
        machine: &Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<(), StructureError> {
        self.require_empty_stack(machine, scope.cut.outcomes[outcome])?;
        let mut exits = scope.exits.borrow_mut();
        let index = exits[outcome].len();
        exits[outcome].push(machine.clone());
        let text = if outcome == 0 { "yield true;" } else { "yield false;" };
        let mut line = Line::new(depth, text, mem::take(pending));
        line.predicate_edge = Some(Edge { outcome, index });
        self.lines.push(line);
        Ok(())
    }

    pub(in crate::structure) fn try_complex_predicate_switch<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &Document,
        groups: &BTreeMap<usize, Vec<CaseLabel>>,
        default: usize,
        offsets: &mut Vec<u32>,
        control: &RangeInclusive<u32>,
    ) -> Result<Option<Option<usize>>, StructureError> {
        if !machine.supports_switch_expressions() || !machine.stack_is_empty()
            || !machine.this_is_initialized() || region.predicate.is_some()
            || self.assertion_starts(header)
        {
            return Ok(None);
        }
        let join = self.layout.normal_join(header, region).or(region.stop);
        let Some(cut) = Cut::prove(self.instructions, self.graph, header, join) else {
            return Ok(None);
        };
        if groups.keys().any(|&head| !cut.owns(head) || !self.layout.inside(head, region))
            || cut.owners.keys().any(|&block| !self.plain_switch_block(header, region, block))
            || cut.outcomes.iter().any(|&block| {
                self.emitted[block] || region.loop_transfer(block).is_some()
                    || (region.stop != Some(block)
                        && (!self.layout.inside(block, region)
                            || !self.exceptions.contains(region.exception_arm, block)))
            })
        {
            return Ok(None);
        }
        let Ok(entry) = machine.switch_arm_entry(control) else { return Ok(None); };
        let names = machine.local_name_checkpoint();
        let sites = machine.switch_anonymous_checkpoint();
        let start = self.lines.len();
        let scope = Scope { cut: &cut, exits: RefCell::default() };
        let recovered = (|| {
            let mut ranges = Vec::with_capacity(groups.len());
            let body = region.predicate_body(&scope);
            for &head in groups.keys() {
                let arm = self.branch_arm(head, body, &entry, depth + 2).ok()?;
                if arm.exit.is_some() {
                    return None;
                }
                ranges.push(arm.end - arm.start);
            }
            if !cut.owners.keys().all(|&block| self.emitted[block]) {
                return None;
            }
            let [yes, no] = scope.exits.take();
            let [yes_at, no_at] = cut.outcomes;
            let mut merge = |target, exits: &[Machine<'a, 'c>]| {
                if exits.is_empty() {
                    return None;
                }
                let mut state = entry.clone();
                let inputs: Vec<_> = exits.iter().collect();
                let local = state.merge_locals(&inputs, self.offset(target), |slot| {
                    self.local_is_live(target, slot)
                }).ok()?;
                let copies = local.arms.into_iter().map(|arm| {
                    arm.into_iter().map(|copy| copy.statement).collect()
                }).collect();
                Some(Outcome { state, declarations: local.declarations, copies })
            };
            Some((ranges, [merge(yes_at, &yes)?, merge(no_at, &no)?]))
        })();
        let Some((sizes, mut outcomes)) = recovered else {
            self.lines.truncate(start);
            for &block in cut.owners.keys() {
                self.emitted[block] = false;
            }
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(sites);
            return Ok(None);
        };
        let native = outcomes.iter().all(|outcome| {
            outcome.state.same_locals(machine) && outcome.declarations.is_empty()
                && outcome.copies.iter().all(Vec::is_empty)
        });
        let labeled = (!native).then(|| {
            let label = format!("predicate{}", self.offset(header));
            let labels = [format!("{label}True"), format!("{label}False")];
            (label, labels)
        });
        let mut body = self.lines.drain(start..);
        let rules = groups.iter().zip(sizes).map(|((&head, keys), size)| {
            let statements = body.by_ref().take(size).flat_map(|mut line| {
                let mut copies = Vec::new();
                if let Some(Edge { outcome, index }) = line.predicate_edge.take()
                    && let Some((_, labels)) = &labeled
                {
                    line.text = format!("break {};", labels[outcome]).into();
                    copies = mem::take(&mut outcomes[outcome].copies[index]);
                }
                let level = line.depth;
                copies.into_iter().map(move |text| Line::new(level, text, Vec::new())).chain([line])
            }).collect();
            Rule {
                labels: keys,
                default: (head == default).into(),
                statements,
                trailing_offsets: Vec::new(),
                result: RuleResult::Abrupt { inline_throw: false },
            }
        }).collect();
        drop(body);
        let dispatch = SwitchExpression { selector, rules, depth }.render();
        if let Some((label, labels)) = labeled {
            let result = self.emit_predicate_labels(
                region, machine, depth, &label, &labels, cut.outcomes, outcomes, join, dispatch, offsets,
            );
            if result.is_ok() {
                machine.commit_switch_dynamic_helpers(&entry);
            }
            return result.map(Some);
        }
        machine.commit_switch_dynamic_helpers(&entry);
        let [fallthrough, taken] = cut.outcomes;
        let when_true = surrounded(dispatch.clone(), "!(", ")");
        let condition = Condition { taken, fallthrough, when_true, when_false: dispatch };
        let (&last, _) = cut.owners.last_key_value().expect("closed predicate switch has rules");
        let end = self.instructions[self.graph.blocks[last].instructions.end - 1].offset;
        self.emit_if(header, region, machine, depth, condition, None, offsets, *control.start()..=end).map(Some)
    }

    /// Keep the two outcomes lexically distinct. A boolean temporary loses
    /// Java's definite-assignment relation between a successful predicate
    /// edge and a local read in that continuation.
    fn emit_predicate_labels<'a, 'c>(
        &mut self,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        label: &str,
        labels: &[String; 2],
        [yes_at, no_at]: [usize; 2],
        [yes, no]: [Outcome<'a, 'c>; 2],
        join: Option<usize>,
        mut dispatch: Document,
        offsets: &mut Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        for declaration in yes.declarations.into_iter().chain(no.declarations) {
            self.push(depth, declaration, Vec::new());
        }
        let start = self.lines.len();
        self.syntax(depth, &format!("{label}: {{"));
        self.syntax(depth + 1, &format!("{}: {{", labels[0]));
        dispatch.insert_str(0, &format!("{}: ", labels[1]));
        self.push(depth + 2, dispatch, mem::take(offsets));
        let arms = region.branch(join);
        let no = self.branch_arm(no_at, arms, &no.state, depth + 2)?;
        if no.exit.is_some() {
            self.syntax(depth + 2, &format!("break {label};"));
        }
        self.syntax(depth + 1, "}");
        let yes = self.branch_arm(yes_at, arms, &yes.state, depth + 1)?;
        self.syntax(depth, "}");
        let active = match (no.exit.is_some(), yes.exit.is_some()) {
            (true, true) => 0..2,
            (true, false) => 0..1,
            (false, true) => 1..2,
            (false, false) => return Ok(None),
        };
        let continuations = [&no, &yes];
        let join = join.expect("predicate continuations meet at their stop");
        let (declarations, copies) = self.merge_arms(machine, join, &continuations[active.clone()])?;
        let levels = [depth + 2, depth + 1];
        for ((arm, &level), copies) in continuations[active.clone()].iter().zip(&levels[active]).zip(copies).rev() {
            self.lines.splice(arm.end..arm.end, copies.into_iter().map(|text| Line::new(level, text, Vec::new())));
        }
        self.lines.splice(start..start, declarations.into_iter().map(|text| Line::new(depth, text, Vec::new())));
        Ok(Some(join))
    }
}
