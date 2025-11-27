// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple line-based writer for generating Lean code with proper indentation.

use std::fmt::Write;

/// Writer context for generating Lean code.
/// Tracks indentation and handles line-based output.
/// Supports both multi-line (indented) and inline (semicolon-separated) modes.
pub struct LeanWriter<W: Write> {
    out: W,
    indent: usize,
    at_line_start: bool,
    inline: bool,
}

impl<W: Write> LeanWriter<W> {
    pub fn new(out: W) -> Self {
        Self {
            out,
            indent: 0,
            at_line_start: true,
            inline: false,
        }
    }

    /// Create a new inline writer (semicolon-separated, no indentation).
    pub fn new_inline(out: W) -> Self {
        Self {
            out,
            indent: 0,
            at_line_start: true,
            inline: true,
        }
    }

    /// Check if this writer is in inline mode.
    pub fn is_inline(&self) -> bool {
        self.inline
    }

    /// Write a string, handling indentation at line starts.
    /// In inline mode, newlines become semicolons.
    pub fn write(&mut self, s: &str) {
        for c in s.chars() {
            if c == '\n' {
                if self.inline {
                    write!(self.out, "; ").unwrap();
                    self.at_line_start = false;
                } else {
                    write!(self.out, "\n").unwrap();
                    self.at_line_start = true;
                }
            } else {
                if self.at_line_start && !self.inline {
                    for _ in 0..self.indent {
                        write!(self.out, "  ").unwrap();
                    }
                }
                self.at_line_start = false;
                write!(self.out, "{}", c).unwrap();
            }
        }
    }

    /// Write a complete line (adds newline at end).
    pub fn line(&mut self, s: &str) {
        self.write(s);
        self.write("\n");
    }

    /// Increase indentation for subsequent lines.
    /// No-op in inline mode.
    pub fn indent(&mut self) {
        if !self.inline {
            self.indent += 1;
        }
    }

    /// Decrease indentation for subsequent lines.
    /// No-op in inline mode.
    pub fn dedent(&mut self) {
        if !self.inline && self.indent > 0 {
            self.indent -= 1;
        }
    }

    /// Get the underlying writer (consumes self).
    pub fn into_inner(self) -> W {
        self.out
    }

    /// Write a formatted string using format_args!.
    /// Convenience method to avoid `w.write(&format!(...))`.
    pub fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) {
        self.write(&args.to_string());
    }

    /// Write a formatted line (adds newline at end).
    /// Convenience method to avoid `w.line(&format!(...))`.
    pub fn line_fmt(&mut self, args: std::fmt::Arguments<'_>) {
        self.line(&args.to_string());
    }

    /// Write a space character.
    pub fn space(&mut self) {
        self.write(" ");
    }

    /// Write an empty line (just a newline).
    pub fn newline(&mut self) {
        self.write("\n");
    }
}

/// Render to a string using multi-line mode.
pub fn render_to_string<F>(f: F) -> String
where
    F: FnOnce(&mut LeanWriter<String>),
{
    let mut writer = LeanWriter::new(String::new());
    f(&mut writer);
    writer.into_inner()
}

/// Render to a string using inline mode (semicolon-separated).
pub fn render_to_string_inline<F>(f: F) -> String
where
    F: FnOnce(&mut LeanWriter<String>),
{
    let mut writer = LeanWriter::new_inline(String::new());
    f(&mut writer);
    writer.into_inner()
}
