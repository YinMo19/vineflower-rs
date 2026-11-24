// Based on Vineflower SwitchStatement.sortEdgesAndNodes (Apache-2.0).

use std::collections::BTreeMap;

use super::switch_expression::CaseLabel;

pub(super) struct Arm {
    pub(super) target: usize,
    pub(super) labels: Vec<CaseLabel>,
    pub(super) fallthrough: Option<usize>,
    first_key: Option<i32>,
}

#[derive(Clone, Copy)]
pub(super) enum Keys {
    DenseIntegers,
    SparseIntegers,
    Projected,
}

pub(super) fn order(
    groups: BTreeMap<usize, Vec<CaseLabel>>,
    cases: &[(i32, u32)],
    default: u32,
    keys: Keys,
    offset: impl Fn(usize) -> u32,
    falls_through: impl Fn(usize, usize) -> bool,
) -> Vec<Arm> {
    let dense = matches!(keys, Keys::DenseIntegers);
    let projected = matches!(keys, Keys::Projected);
    let mut groups = groups.into_iter().peekable();
    let mut arms = Vec::with_capacity(groups.len());
    while let Some((target, labels)) = groups.next() {
        let fallthrough = groups
            .peek()
            .map(|&(next, _)| next)
            .filter(|&next| falls_through(target, next));
        arms.push(Arm {
            target,
            labels,
            fallthrough,
            first_key: None,
        });
    }

    // Decode only actual table entries, not the gaps in a lookupswitch. An
    // alias between two real labels also fits their Java selector's type,
    // even if the selector was byte, short or char rather than int.
    let span = dense.then(|| {
        let mut matched = cases
            .iter()
            .filter_map(|&(key, target)| (target != default).then_some(key));
        matched.next().map(|low| low..=matched.next_back().unwrap_or(low))
    }).flatten();
    for &(key, target) in cases {
        let alias = target == default;
        if alias && !projected
            && (!dense
                || !((0..=127).contains(&key)
                    || span.as_ref().is_some_and(|span| span.contains(&key))))
        {
            continue;
        }
        let index = arms
            .binary_search_by_key(&target, |arm| offset(arm.target))
            .expect("every dispatch target has a case group");
        let arm = &mut arms[index];
        arm.first_key.get_or_insert(key);
        if alias && !projected {
            arm.labels.push(CaseLabel {
                text: key.to_string().into(),
                offsets: Vec::new(),
            });
        }
    }

    // Upstream first sorts by dispatch edge (numeric keys before a bare
    // default), then places each fallthrough destination after its predecessor.
    // Keep the proven physical chains intact and rank them by their first arm,
    // not by a possibly smaller key on a later arm in that chain.
    let mut head_key = None;
    let mut starts_chain = true;
    for arm in &mut arms {
        if starts_chain {
            head_key = arm.first_key;
        }
        arm.first_key = head_key;
        starts_chain = arm.fallthrough.is_none();
    }
    arms.sort_unstable_by_key(|arm| (arm.first_key.map_or(i64::MAX, i64::from), arm.target));
    arms
}
