// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Rendering context - shared state during IR rendering

use super::lean_writer::LeanWriter;
use intermediate_theorem_format::{FunctionID, ModuleID, Program, VariableRegistry};
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

    /// Check if a function is monadic (returns Except)
    pub fn is_func_monadic(&self, func_id: FunctionID) -> bool {
        self.program
            .functions
            .get(func_id)
            .signature
            .return_type
            .is_monad()
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
        self.writer.write("\n");
    }

    /// Increase indentation
    pub fn indent(&mut self) {
        self.writer.indent();
    }

    /// Decrease indentation
    pub fn dedent(&mut self) {
        self.writer.dedent();
    }

    /// Check if in inline mode
    pub fn is_inline(&self) -> bool {
        self.writer.is_inline()
    }

    /// Get the underlying writer
    pub fn into_writer(self) -> LeanWriter<W> {
        self.writer
    }
}
