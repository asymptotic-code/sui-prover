// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translation utilities for Move bytecode to TheoremIR
//!
//! This module provides specialized translators:
//! - utilities: Shared helper functions (constant/binop conversion, ID resolution)
//! - expression_translator: Bytecode operations → Expression IR
//! - statement_translator: Bytecode instructions → Statement IR
//! - function_translator: Function body translation orchestration

mod utilities;
pub mod expression_translator;
pub mod statement_translator;
pub mod function_translator;

pub use utilities::{convert_constant, convert_binop, resolve_function_id, resolve_struct_id};
