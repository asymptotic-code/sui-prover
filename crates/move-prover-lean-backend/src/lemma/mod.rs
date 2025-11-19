// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lemma management system for reusable proofs

pub mod cache;
pub mod generation;

pub use cache::{CachedLemma, LemmaCache};
pub use generation::LemmaFileGenerator;
