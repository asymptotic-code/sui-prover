// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Intermediate Theorem Format (TheoremIR)

pub mod analysis;
mod data;
pub mod utils;

pub use analysis::optimize;
pub use data::functions::{FunctionSignature, Parameter, TheoremFunction};
pub use data::ir::{BinOp, Const, IRNode, UnOp, VecOp};
pub use data::structure::{TheoremField, TheoremStruct};
pub use data::types::{TempId, TheoremType};
pub use data::variables::VariableRegistry;
pub use data::{TheoremFunctionID, TheoremModuleID, TheoremStructID};
pub use data::{TheoremModule, TheoremProgram};
