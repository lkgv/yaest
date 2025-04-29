// SPDX-License-Identifier: Apache-2.0

//! Analysis modules for Solang's IR

use std::collections::{ VecDeque, BTreeSet };
use crate::codegen::cfg;

pub mod pointer;

// Add other analysis modules here as needed

struct State {
    pub a: usize
}

impl State {
    pub fn new() -> Self {
        State { a: 0 }
    }

    pub fn set_a(&mut self, a: usize) {
        self.a = a;
    }

    pub fn get_a(&self) -> usize {
        self.a
    }
}


pub fn ownership_analysis(graph: &cfg::ControlFlowGraph) {
    if graph.blocks.len() == 0 {
        return;
    }

    let mut q = VecDeque::new();
    let mut visited = BTreeSet::new();
    q.push_back(&graph.blocks[0]);

    while q.len() > 0 {
        let entry = q.pop_front().unwrap();
        visited.insert(entry.name.as_str());

        println!(" Block: {:?}", entry.name);

        let succs = entry.successors().iter().map(|s| &graph.blocks[*s]).collect::<Vec<_>>();
        println!("  Succs: {:?}", succs.iter().map(|s| s.name.as_str()).collect::<Vec<_>>());

        for succ in succs {
            if visited.get(succ.name.as_str()).is_none() {
                q.push_back(succ);
                visited.insert(succ.name.as_str());
            }
        }
    }

}

