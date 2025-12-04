// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple Lean renderer - pure translation with minimal logic.
//!
//! This module takes TheoremIR and renders it to Lean syntax.
//! The renderer is intentionally "dumb" - it pattern matches IR nodes
//! and emits corresponding Lean text without complex analysis.

mod expression_renderer;
mod function_renderer;
mod lean_writer;
mod program_renderer;
mod statement_renderer;
mod struct_renderer;
mod type_renderer;

pub use lean_writer::LeanWriter;
pub use program_renderer::render_to_directory;

/// Renders a tuple-like structure: empty→`empty`, single→element, multiple→`(a, b, c)`
///
/// - `items`: the elements to render
/// - `empty`: what to emit for empty list (e.g., "()" or "_")
/// - `sep`: separator between elements (e.g., ", " or " × ")
/// - `render`: function to render each element to a string
pub fn render_tuple_like<T, F>(items: &[T], empty: &str, sep: &str, render: F) -> String
where
    F: Fn(&T) -> String,
{
    match items {
        [] => empty.to_string(),
        [single] => render(single),
        multiple => {
            let rendered: Vec<_> = multiple.iter().map(render).collect();
            format!("({})", rendered.join(sep))
        }
    }
}
