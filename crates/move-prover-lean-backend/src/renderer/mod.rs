// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple Lean renderer - pure translation with ZERO logic
//!
//! This module takes TheoremIR and renders it to Lean syntax.
//! NO analysis, NO variants, NO purity checks - just IR to text.

mod lean_writer;
mod type_renderer;
mod expression_renderer;
mod statement_renderer;
mod function_renderer;
mod struct_renderer;
mod program_renderer;
mod native_impls;

pub use lean_writer::LeanWriter;
pub use statement_renderer::StatementRenderer;
pub use program_renderer::ProgramRenderer;
pub use native_impls::{get_native_impl, is_native_with_impl, get_native_imports};
