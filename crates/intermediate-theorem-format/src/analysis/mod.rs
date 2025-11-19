// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Analysis passes for TheoremIR
//!
//! This module contains various analysis and transformation passes
//! that operate on the complete TheoremProgram IR.

mod dependency_order;

pub use dependency_order::DependencyOrderPass;
