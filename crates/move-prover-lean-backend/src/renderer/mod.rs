// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple Lean renderer - pure translation with minimal logic.
//!
//! This module takes TheoremIR and renders it to Lean syntax.
//! The renderer is intentionally "dumb" - it pattern matches IR nodes
//! and emits corresponding Lean text without complex analysis.

mod context;
mod function_renderer;
mod helpers;
mod lean_writer;
mod program_renderer;
mod render;
mod struct_renderer;
mod type_renderer;

pub use lean_writer::LeanWriter;
pub use program_renderer::render_to_directory;
