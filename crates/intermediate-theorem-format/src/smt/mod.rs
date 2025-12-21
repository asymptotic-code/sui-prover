// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! SMT solving and simplification for TheoremIR
//!
//! This module provides Z3-based analysis for abort predicates:
//! - Translation from IRNode to Z3 AST
//! - Simplification of boolean predicates
//! - Satisfiability checking for abort conditions

mod translate;
mod simplify;

pub use simplify::{simplify_aborts, simplify_abort_predicate, apply_simplified_aborts, AbortAnalysisResult};
pub use translate::{SmtContext, new_context};
