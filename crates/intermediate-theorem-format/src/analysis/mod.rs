// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Analysis passes for TheoremIR
//!
//! This module contains various analysis and transformation passes
//! that operate on the complete TheoremProgram IR.

mod cleanup;
mod dead_code_removal;
mod dependency_order;
mod guard_clause;
mod import_collection;
mod purity;
mod return_simplification;
mod temp_inlining;

pub use cleanup::cleanup;
pub use dead_code_removal::{remove_dead_code, collect_used_vars};
pub use dependency_order::DependencyOrderPass;
pub use guard_clause::extract_guard_clauses;
pub use import_collection::ImportCollectionPass;
pub use purity::{analyze_purity, PurityMap};
pub use return_simplification::simplify_returns;
pub use temp_inlining::{TempUsageInfo, inline_temps};
