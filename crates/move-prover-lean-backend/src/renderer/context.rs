// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Rendering context - shared state during IR rendering

use super::lean_writer::LeanWriter;
use intermediate_theorem_format::{ModuleID, Program, VariableRegistry};
use std::fmt::Write;

/// Rendering context - holds everything needed during rendering
pub struct RenderCtx<'a, W: Write> {
    pub program: &'a Program,
    pub registry: &'a VariableRegistry,
    pub current_module_id: ModuleID,
    pub current_module_namespace: Option<&'a str>,
    pub writer: LeanWriter<W>,
}

impl<'a, W: Write> RenderCtx<'a, W> {
    pub fn new(
        program: &'a Program,
        registry: &'a VariableRegistry,
        current_module_id: ModuleID,
        current_module_namespace: Option<&'a str>,
        writer: LeanWriter<W>,
    ) -> Self {
        Self {
            program,
            registry,
            current_module_id,
            current_module_namespace,
            writer,
        }
    }

    /// Write a string to the writer
    pub fn write(&mut self, s: &str) {
        self.writer.write(s);
    }

    /// Write a line to the writer
    pub fn line(&mut self, s: &str) {
        self.writer.line(s);
    }

    /// Write a newline
    pub fn newline(&mut self) {
        self.writer.newline();
    }

    /// Increase indentation. If `newline` is true, writes a newline before indenting.
    pub fn indent(&mut self, newline: bool) {
        self.writer.indent(newline);
    }

    /// Decrease indentation. If `newline` is true, writes a newline after dedenting.
    pub fn dedent(&mut self, newline: bool) {
        self.writer.dedent(newline);
    }

    /// Check if in inline mode
    pub fn is_inline(&self) -> bool {
        self.writer.is_inline()
    }

    /// Write items with a separator, using a render function
    pub fn sep_with<I, T, F>(&mut self, separator: &str, items: I, mut render: F)
    where
        I: IntoIterator<Item = T>,
        F: FnMut(&mut Self, T),
    {
        let mut first = true;
        for item in items {
            if !first {
                self.write(separator);
            }
            first = false;
            render(self, item);
        }
    }

    /// Write a tuple-like structure: empty→empty_val, single→element, multiple→`(a, b, c)`
    pub fn tuple<I, T, F>(&mut self, items: I, empty_val: &str, mut render: F)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
        F: FnMut(&mut Self, T),
    {
        let iter = items.into_iter();
        let len = iter.len();
        match len {
            0 => self.write(empty_val),
            1 => {
                for item in iter {
                    render(self, item);
                }
            }
            _ => {
                self.write("(");
                self.sep_with(", ", iter, &mut render);
                self.write(")");
            }
        }
    }

    /// Get the underlying writer
    pub fn into_writer(self) -> LeanWriter<W> {
        self.writer
    }
}
