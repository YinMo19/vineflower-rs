use super::*;
use crate::bytecode::decode;

fn graph(code: &[u8], handlers: &[ExceptionHandler]) -> ControlFlowGraph {
    ControlFlowGraph::build(&decode(code).unwrap(), handlers).unwrap()
}

#[test]
fn diamond_has_normal_and_exception_predecessors() {
    let g = graph(
        &[0x99, 0, 6, 0xa7, 0, 4, 0, 0xb1, 0xbf],
        &[
            ExceptionHandler {
                start_pc: 3,
                end_pc: 7,
                handler_pc: 8,
                catch_type: 1,
            },
            ExceptionHandler {
                start_pc: 6,
                end_pc: 7,
                handler_pc: 8,
                catch_type: 0,
            },
        ],
    );
    assert_eq!(g.blocks.len(), 5);
    assert_eq!(g.blocks[0].successors, [2, 1]);
    assert_eq!(g.blocks[1].successors, [3]);
    assert_eq!(g.blocks[2].successors, [3]);
    assert_eq!(g.blocks[3].predecessors, [1, 2]);
    assert!(g.blocks[3].successors.is_empty());
    assert!(g.blocks[4].predecessors.is_empty());
    assert_eq!(g.blocks[1].exception_successors, [4]);
    assert_eq!(g.blocks[2].exception_successors, [4]);
    assert_eq!(g.blocks[4].exception_predecessors, [1, 2]);
    assert_eq!(g.reachable(), [true; 5]);
    assert_eq!(
        g.immediate_dominators(),
        [None, Some(0), Some(0), Some(0), Some(0)]
    );
    assert_eq!(
        g.immediate_postdominators(),
        [Some(3), Some(3), Some(3), None, None]
    );
    assert!(g.natural_loops().is_empty());
}

#[test]
fn protected_ranges_split_straight_line_and_accept_code_end() {
    let g = graph(
        &[0, 0, 0, 0xb1, 0xbf],
        &[
            ExceptionHandler {
                start_pc: 1,
                end_pc: 2,
                handler_pc: 4,
                catch_type: 1,
            },
            ExceptionHandler {
                start_pc: 4,
                end_pc: 5,
                handler_pc: 4,
                catch_type: 0,
            },
        ],
    );
    let ranges: Vec<_> = g.blocks.iter().map(|b| b.instructions.clone()).collect();
    assert_eq!(ranges, [0..1, 1..2, 2..4, 4..5]);
    assert_eq!(g.block_at(2), Some(2));
    assert_eq!(g.block_at(3), None);
    assert_eq!(g.blocks[1].exception_successors, [3]);
    assert!(g.blocks[2].exception_successors.is_empty());
    assert_eq!(g.blocks[3].exception_successors, [3]);
    assert_eq!(g.blocks[3].exception_predecessors, [1, 3]);
    assert_eq!(g.immediate_dominators(), [None, Some(0), Some(1), Some(1)]);
    assert!(g.natural_loops().is_empty());
}

#[test]
fn switch_deduplicates_targets_and_has_no_implicit_fallthrough() {
    let g = graph(
        &[
            0xab, 0, 0, 0, // lookupswitch and alignment
            0, 0, 0, 29, 0, 0, 0, 2, // default and pair count
            0, 0, 0, 4, 0, 0, 0, 30, // case 4
            0, 0, 0, 5, 0, 0, 0, 29, // case 5 shares the default
            0xb1, 0xb1, 0xbf,
        ],
        &[],
    );
    assert_eq!(g.blocks[0].successors, [2, 3]);
    assert_eq!(g.blocks[2].predecessors, [0]);
    assert_eq!(g.reachable(), [true, false, true, true]);
    assert_eq!(g.immediate_dominators(), [None, None, Some(0), Some(0)]);
    assert_eq!(g.immediate_postdominators(), [None; 4]);
}

#[test]
fn upstream_scc_fixture_has_partition_including_dead_components() {
    // Vineflower StronglyConnectedComponentsTest: 0 <-> 1 and 2 entering
    // the disconnected 3 -> 4 -> 5 -> 6 -> 7 -> 3 cycle.
    let g = graph(
        &[
            0xa7, 0, 3, 0xa7, 0xff, 0xfd, 0xa7, 0, 3, 0xa7, 0, 3, 0xa7, 0, 3, 0xa7, 0, 3, 0xa7, 0,
            3, 0xa7, 0xff, 0xf4,
        ],
        &[],
    );
    let mut sccs = g.strongly_connected_components();
    // SCC membership is invariant; the starting member of a cycle is not.
    sccs[0].sort_unstable();
    assert_eq!(sccs, [vec![0, 1], vec![7, 6, 5, 4, 3], vec![2]]);
    assert_eq!(
        g.natural_loops(),
        [NaturalLoop {
            header: 0,
            latches: vec![1],
            blocks: vec![0, 1]
        }]
    );
    assert_eq!(g.immediate_postdominators(), [None; 8]);
}

#[test]
fn loops_with_multiple_latches_share_one_header() {
    let g = graph(&[0x99, 0, 6, 0xa7, 0xff, 0xfd, 0xa7, 0xff, 0xfa], &[]);
    assert_eq!(g.immediate_dominators(), [None, Some(0), Some(0)]);
    assert_eq!(
        g.natural_loops(),
        [NaturalLoop {
            header: 0,
            latches: vec![1, 2],
            blocks: vec![0, 1, 2]
        }]
    );
}

#[test]
fn conditional_target_equal_to_fallthrough_is_one_edge() {
    let g = graph(&[0x99, 0, 3, 0xb1], &[]);
    assert_eq!(g.blocks[0].successors, [1]);
    assert_eq!(g.blocks[1].predecessors, [0]);
}

#[test]
fn legacy_subroutine_instructions_report_explicit_errors() {
    for opcode in [0xa8, 0xa9, 0xc9] {
        let i = Instruction {
            offset: 0,
            opcode,
            operand: Operand::None,
            len: 1,
        };
        assert_eq!(
            ControlFlowGraph::build(&[i], &[]).unwrap_err(),
            CfgError::LegacySubroutine { offset: 0, opcode }
        );
    }
}

#[test]
fn invalid_targets_and_missing_fallthrough_are_rejected() {
    let jump = Instruction {
        offset: 0,
        opcode: 0xa7,
        operand: Operand::Branch(1),
        len: 3,
    };
    assert_eq!(
        ControlFlowGraph::build(&[jump], &[]).unwrap_err(),
        CfgError::InvalidTarget { offset: 1 }
    );
    let code = decode(&[0]).unwrap();
    assert_eq!(
        ControlFlowGraph::build(&code, &[]).unwrap_err(),
        CfgError::MissingFallthrough { offset: 0 }
    );
}

#[test]
fn irreducible_cycle_is_not_a_natural_loop() {
    let g = graph(&[0x99, 0, 6, 0xa7, 0, 3, 0xa7, 0xff, 0xfd], &[]);
    assert_eq!(g.immediate_dominators(), [None, Some(0), Some(0)]);
    assert_eq!(g.strongly_connected_components(), [vec![1, 2], vec![0]]);
    assert!(g.natural_loops().is_empty());
}

#[test]
fn invalid_exception_boundaries_are_rejected() {
    let instructions = decode(&[0x11, 0, 0, 0xb1]).unwrap();
    let mut handler = ExceptionHandler {
        start_pc: 1,
        end_pc: 4,
        handler_pc: 3,
        catch_type: 0,
    };
    assert_eq!(
        ControlFlowGraph::build(&instructions, &[handler]).unwrap_err(),
        CfgError::InvalidTarget { offset: 1 }
    );
    handler = ExceptionHandler {
        start_pc: 3,
        end_pc: 3,
        handler_pc: 3,
        catch_type: 0,
    };
    assert_eq!(
        ControlFlowGraph::build(&instructions, &[handler]).unwrap_err(),
        CfgError::InvalidProtectedRange { start: 3, end: 3 }
    );
}

#[test]
fn empty_instruction_slice_has_no_entry() {
    let g = ControlFlowGraph::build(&[], &[]).unwrap();
    assert!(g.blocks.is_empty());
    assert!(g.reachable().is_empty());
    assert!(g.immediate_dominators().is_empty());
    assert!(g.immediate_postdominators().is_empty());
    assert!(g.strongly_connected_components().is_empty());
    assert!(g.natural_loops().is_empty());
}
