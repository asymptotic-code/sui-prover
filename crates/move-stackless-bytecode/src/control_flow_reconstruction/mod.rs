// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control flow reconstruction module
//!
//! This module reconstructs structured control flow (if/else, loops) from
//! stackless bytecode basic blocks using control flow graph analysis.

mod reconstructor;
mod types;

pub use reconstructor::reconstruct_control_flow;
pub use types::StructuredBlock;
