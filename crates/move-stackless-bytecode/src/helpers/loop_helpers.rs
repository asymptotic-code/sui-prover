use std::collections::BTreeMap;

use move_model::model::FunctionEnv;

use crate::{
    function_target::{FunctionData, FunctionTarget},
    graph::{Graph, NaturalLoop},
    stackless_bytecode::{Bytecode, Label},
    stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph},
};

pub fn find_loops_headers(
    func_env: &FunctionEnv,
    data: &FunctionData,
) -> BTreeMap<Label, Vec<NaturalLoop<u16>>> {
    // build for natural loops
    let func_target = FunctionTarget::new(func_env, data);
    let code = func_target.get_bytecode();
    let cfg = StacklessControlFlowGraph::new_forward(code);
    let entry = cfg.entry_block();
    let nodes = cfg.blocks();
    let edges: Vec<(BlockId, BlockId)> = nodes
        .iter()
        .flat_map(|x| {
            cfg.successors(*x)
                .iter()
                .map(|y| (*x, *y))
                .collect::<Vec<(BlockId, BlockId)>>()
        })
        .collect();
    let graph = Graph::new(entry, nodes, edges);
    let natural_loops = graph
        .compute_reducible()
        .expect("A well-formed Move function is expected to have a reducible control-flow graph");

    // collect shared headers from loops
    let mut fat_headers = BTreeMap::new();
    for single_loop in natural_loops {
        let label = match cfg.content(single_loop.loop_header) {
            BlockContent::Dummy => panic!("A loop header should never be a dummy block"),
            BlockContent::Basic { lower, upper: _ } => match code[*lower as usize] {
                Bytecode::Label(_, label) => label,
                _ => panic!("A loop header block is expected to start with a Label bytecode"),
            },
        };

        fat_headers
            .entry(label)
            .or_insert_with(Vec::new)
            .push(single_loop);
    }

    fat_headers
}
