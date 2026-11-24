use super::ControlFlowGraph;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NaturalLoop {
    pub header: usize,
    /// Block indices in ascending order. Each latch has a normal edge to the header.
    pub latches: Vec<usize>,
    pub blocks: Vec<usize>,
}

impl ControlFlowGraph {
    /// Whether each block is reachable from entry via normal or exceptional control flow.
    pub fn reachable(&self) -> Vec<bool> {
        let mut seen = vec![false; self.blocks.len()];
        if !seen.is_empty() {
            seen[0] = true;
            let mut pending = vec![0];
            while let Some(source) = pending.pop() {
                let block = &self.blocks[source];
                for &destination in block.successors.iter().chain(&block.exception_successors) {
                    if !seen[destination] {
                        seen[destination] = true;
                        pending.push(destination);
                    }
                }
            }
        }
        seen
    }

    /// Immediate dominator of each block, using both normal and exceptional edges.
    /// Entry and unreachable blocks have no immediate dominator.
    pub fn immediate_dominators(&self) -> Vec<Option<usize>> {
        dominators(
            self.blocks.len(),
            0,
            |node| {
                let block = &self.blocks[node];
                block
                    .successors
                    .iter()
                    .chain(&block.exception_successors)
                    .copied()
            },
            |node| {
                let block = &self.blocks[node];
                block
                    .predecessors
                    .iter()
                    .chain(&block.exception_predecessors)
                    .copied()
            },
        )
    }

    /// Immediate postdominator on normal edges, with all normal terminals
    /// connected to a virtual exit. A virtual-exit parent or inability to
    /// reach an exit is represented by `None`.
    pub fn immediate_postdominators(&self) -> Vec<Option<usize>> {
        let exit = self.blocks.len();
        let terminals: Vec<_> = self
            .blocks
            .iter()
            .enumerate()
            .filter_map(|(node, block)| block.successors.is_empty().then_some(node))
            .collect();
        let mut result = dominators(
            exit + 1,
            exit,
            |node| {
                let successors = if node == exit {
                    &terminals
                } else {
                    &self.blocks[node].predecessors
                };
                successors.iter().copied()
            },
            |node| {
                let successors = &self.blocks[node].successors;
                let incoming = if successors.is_empty() {
                    std::slice::from_ref(&exit)
                } else {
                    successors.as_slice()
                };
                incoming.iter().copied()
            },
        );
        result.truncate(exit);
        for parent in &mut result {
            if *parent == Some(exit) {
                *parent = None;
            }
        }
        result
    }

    /// Strongly connected components on normal edges, including unreachable blocks.
    /// Components close in Tarjan pop order; members appear in reverse discovery order.
    pub fn strongly_connected_components(&self) -> Vec<Vec<usize>> {
        let len = self.blocks.len();
        let mut components = Vec::new();
        let mut indices = vec![usize::MAX; len];
        let mut low = vec![0; len];
        let mut active = vec![false; len];
        let mut stack = Vec::new();
        let mut dfs = Vec::new();
        let mut index = 0;
        // Try entry, then blocks without a normal predecessor, then any remaining cycles.
        let roots = (0..len.min(1))
            .chain((1..len).filter(|&node| self.blocks[node].predecessors.is_empty()))
            .chain(1..len);
        for root in roots {
            if indices[root] != usize::MAX {
                continue;
            }
            dfs.push((root, 0));
            while let Some(&mut (node, ref mut next)) = dfs.last_mut() {
                if indices[node] == usize::MAX {
                    indices[node] = index;
                    low[node] = index;
                    index += 1;
                    active[node] = true;
                    stack.push(node);
                }
                if let Some(&destination) = self.blocks[node].successors.get(*next) {
                    *next += 1;
                    if indices[destination] == usize::MAX {
                        dfs.push((destination, 0));
                    } else if active[destination] {
                        low[node] = low[node].min(indices[destination]);
                    }
                    continue;
                }
                dfs.pop();
                if let Some(&(parent, _)) = dfs.last() {
                    low[parent] = low[parent].min(low[node]);
                }
                if low[node] == indices[node] {
                    let mut component = Vec::new();
                    loop {
                        let member = stack.pop().unwrap();
                        active[member] = false;
                        component.push(member);
                        if member == node {
                            break;
                        }
                    }
                    components.push(component);
                }
            }
        }
        components
    }

    /// Natural loops from reachable normal back edges, grouped by dominating header.
    /// Exceptional entries are considered when testing dominance, but are not loop edges.
    pub fn natural_loops(&self) -> Vec<NaturalLoop> {
        let len = self.blocks.len();
        if len == 0 {
            return Vec::new();
        }
        let mut children = vec![Vec::new(); len];
        for (node, parent) in self.immediate_dominators().into_iter().enumerate() {
            if let Some(parent) = parent {
                children[parent].push(node);
            }
        }
        // A dominator tree subtree is a contiguous interval in tree preorder.
        let mut start = vec![usize::MAX; len];
        let mut end = vec![0; len];
        let mut dfs = vec![(0, 0)];
        let mut index = 1;
        start[0] = 0;
        while let Some((node, next)) = dfs.last_mut() {
            if let Some(&child) = children[*node].get(*next) {
                *next += 1;
                start[child] = index;
                index += 1;
                dfs.push((child, 0));
            } else {
                end[*node] = index;
                dfs.pop();
            }
        }
        let mut result = Vec::new();
        let mut seen = vec![usize::MAX; len];
        let mut pending = Vec::new();
        for (header, block) in self.blocks.iter().enumerate() {
            let dominates = |node: usize| start[node] >= start[header] && start[node] < end[header];
            let latches: Vec<_> = block
                .predecessors
                .iter()
                .copied()
                .filter(|&node| dominates(node))
                .collect();
            if latches.is_empty() {
                continue;
            }
            seen[header] = header;
            let mut members = vec![header];
            for &latch in &latches {
                if latch != header {
                    seen[latch] = header;
                    pending.push(latch);
                }
            }
            while let Some(node) = pending.pop() {
                members.push(node);
                for &pred in &self.blocks[node].predecessors {
                    if seen[pred] != header && dominates(pred) {
                        seen[pred] = header;
                        pending.push(pred);
                    }
                }
            }
            members.sort_unstable();
            result.push(NaturalLoop {
                header,
                latches,
                blocks: members,
            });
        }
        result
    }
}

fn dominators<I: Iterator<Item = usize>, J: Iterator<Item = usize>>(
    len: usize,
    root: usize,
    successors: impl Fn(usize) -> I,
    predecessors: impl Fn(usize) -> J,
) -> Vec<Option<usize>> {
    let mut idom = vec![None; len];
    if len == 0 {
        return idom;
    }
    let mut order = Vec::new();
    let mut rank = vec![usize::MAX; len];
    rank[root] = 0;
    let mut dfs = vec![(root, successors(root))];
    while let Some((node, edges)) = dfs.last_mut() {
        if let Some(destination) = edges.next() {
            if rank[destination] == usize::MAX {
                rank[destination] = 0;
                dfs.push((destination, successors(destination)));
            }
        } else {
            order.push(*node);
            dfs.pop();
        }
    }
    order.reverse();
    for (i, &node) in order.iter().enumerate() {
        rank[node] = i;
    }
    // Cooper–Harvey–Kennedy iteration in reverse postorder. Every node
    // except the root has a DFS tree predecessor processed earlier.
    idom[root] = Some(root);
    loop {
        let mut changed = false;
        for &node in &order[1..] {
            let mut incoming = predecessors(node).filter(|&pred| idom[pred].is_some());
            let first = incoming.next().unwrap();
            let parent = incoming.fold(first, |mut left, mut right| {
                while left != right {
                    if rank[left] > rank[right] {
                        left = idom[left].unwrap();
                    } else {
                        right = idom[right].unwrap();
                    }
                }
                left
            });
            if idom[node] != Some(parent) {
                idom[node] = Some(parent);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    idom[root] = None;
    idom
}
