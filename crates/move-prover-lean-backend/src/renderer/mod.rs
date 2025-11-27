// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple Lean renderer - pure translation with minimal logic.
//!
//! This module takes TheoremIR and renders it to Lean syntax.
//! The renderer is intentionally "dumb" - it pattern matches IR nodes
//! and emits corresponding Lean text without complex analysis.

mod lean_writer;
mod type_renderer;
mod expression_renderer;
mod statement_renderer;
mod function_renderer;
mod struct_renderer;
mod program_renderer;

pub use lean_writer::LeanWriter;
pub use program_renderer::render_to_directory;
