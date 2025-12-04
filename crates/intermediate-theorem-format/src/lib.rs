// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Intermediate Theorem Format (TheoremIR)

pub mod analysis;
mod data;
pub mod utils;

pub use analysis::optimize;
pub use data::functions::{Function, FunctionSignature, Parameter};
pub use data::ir::{BinOp, Const, IRNode, UnOp, VecOp};
pub use data::structure::{Field, Struct};
pub use data::types::{TempId, Type};
pub use data::variables::VariableRegistry;
pub use data::{FunctionID, ModuleID, StructID};
pub use data::{Module, Program};
