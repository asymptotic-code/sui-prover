// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple Lean renderer - pure translation with minimal logic.
//!
//! This module takes TheoremIR and renders it to Lean syntax.
//! The renderer is intentionally "dumb" - it pattern matches IR nodes
//! and emits corresponding Lean text without complex analysis.

mod context;
pub mod function_renderer;
mod helpers;
mod lean_writer;
mod program_renderer;
pub mod render;
mod struct_renderer;
pub mod type_renderer;

pub use lean_writer::LeanWriter;
pub use program_renderer::render_to_directory;

use intermediate_theorem_format::{Function, IRNode, Program};

/// Render an IR expression to a Lean string.
/// Used by layers.rs to render Goal bodies from the IR.
/// Goal bodies are rendered in a different namespace than the functions they call,
/// so we pass None for current_module_namespace to force full qualification.
pub fn render_expression_to_string(ir: &IRNode, func: &Function, program: &Program) -> String {
    let writer = LeanWriter::new(String::new());
    let mut ctx = context::RenderCtx::new(
        program,
        &func.variables,
        func.module_id,
        None, // Force full qualification since goals are in a different namespace
        writer,
    );
    render::render(ir, &mut ctx);
    ctx.into_writer().into_inner()
}

/// Render an IR expression as a Prop (use `=` instead of `==` for equality).
/// Used for Goal definitions which are Props.
pub fn render_prop_to_string(ir: &IRNode, func: &Function, program: &Program) -> String {
    let writer = LeanWriter::new(String::new());
    let mut ctx = context::RenderCtx::new(
        program,
        &func.variables,
        func.module_id,
        None, // Force full qualification since goals are in a different namespace
        writer,
    );
    ctx.with_prop_context();
    render::render(ir, &mut ctx);
    ctx.into_writer().into_inner()
}
