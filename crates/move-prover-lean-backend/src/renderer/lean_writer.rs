// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Writer wrapper for generating Lean code with proper indentation

use move_model::code_writer::CodeWriter;
use move_model::model::Loc;
use intermediate_theorem_format::NameManager;

/// Wrapper around CodeWriter for Lean-specific formatting
/// Holds a reference to the NameManager for type rendering
pub struct LeanWriter<'a> {
    writer: CodeWriter,
    /// Name manager for looking up struct/module names during rendering
    pub name_manager: &'a NameManager,
    /// Current module name (used to avoid redundant qualification)
    pub current_module: Option<String>,
}

impl<'a> LeanWriter<'a> {
    pub fn new(name_manager: &'a NameManager) -> Self {
        // Use a dummy location since we don't track source locations in Lean output
        // FileId is a simple wrapper around u32, safe to construct via MaybeUninit
        let dummy_file_id: codespan::FileId = unsafe {
            let mut file_id = std::mem::MaybeUninit::<codespan::FileId>::uninit();
            // Write a valid u32 value (0) into the FileId
            std::ptr::write(file_id.as_mut_ptr() as *mut u32, 0u32);
            file_id.assume_init()
        };
        let dummy_span = codespan::Span::new(codespan::ByteIndex(0), codespan::ByteIndex(0));
        let dummy_loc = Loc::new(dummy_file_id, dummy_span);
        Self {
            writer: CodeWriter::new(dummy_loc),
            name_manager,
            current_module: None,
        }
    }

    /// Create a writer with a specific current module context
    pub fn with_module(name_manager: &'a NameManager, module: String) -> Self {
        let mut writer = Self::new(name_manager);
        writer.current_module = Some(module);
        writer
    }

    /// Emit a string without newline
    pub fn emit(&self, s: &str) {
        self.writer.emit(s);
    }

    /// Emit a string with newline
    pub fn emit_line(&self, s: &str) {
        self.writer.emit_line(s);
    }

    /// Increase indentation level
    pub fn indent(&self) {
        self.writer.indent();
    }

    /// Decrease indentation level
    pub fn unindent(&self) {
        self.writer.unindent();
    }

    /// Execute a function with increased indentation
    pub fn with_indent<F>(&self, f: F)
    where
        F: FnMut(),
    {
        self.writer.with_indent(f);
    }

    /// Extract the final output
    pub fn extract_result(&self) -> String {
        self.writer.extract_result()
    }
}
