// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control flow reconstruction module
//!
//! This module reconstructs structured control flow (if/else, loops) from
//! stackless bytecode basic blocks using control flow graph analysis.

mod helpers;
mod reconstructor;
mod types;
mod phi_computation;
mod dominance;

pub use types::{StructuredBlock, LoopPhiVariable, IfPhiVariable};
pub use reconstructor::reconstruct_control_flow;
pub use phi_computation::compute_phi_variables;
pub use dominance::PhiPlacement;
