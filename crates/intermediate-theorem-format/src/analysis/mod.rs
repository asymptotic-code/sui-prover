// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Analysis passes for TheoremIR
//!
//! This module contains various analysis and transformation passes
//! that operate on the complete TheoremProgram IR.

mod dependency_order;
mod import_collection;

pub use dependency_order::DependencyOrderPass;
pub use import_collection::ImportCollectionPass;
