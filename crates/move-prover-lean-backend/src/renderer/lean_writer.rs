// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simple line-based writer for generating Lean code with proper indentation.

use std::fmt::{Display, Write};

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
                    writeln!(self.out).unwrap();
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
    /// If `newline` is true, writes a newline before indenting (for block starts).
    /// No-op in inline mode.
    pub fn indent(&mut self, newline: bool) {
        if newline {
            self.newline();
        }
        if !self.inline {
            self.indent += 1;
        }
    }

    /// Decrease indentation for subsequent lines.
    /// If `newline` is true, writes a newline after dedenting (for block ends).
    /// No-op in inline mode.
    pub fn dedent(&mut self, newline: bool) {
        if !self.inline && self.indent > 0 {
            self.indent -= 1;
        }
        if newline {
            self.newline();
        }
    }

    /// Get the underlying writer (consumes self).
    pub fn into_inner(self) -> W {
        self.out
    }

    /// Get a mutable reference to the underlying writer.
    pub fn inner_mut(&mut self) -> &mut W {
        &mut self.out
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

    /// Write items separated by a separator string.
    /// Example: `w.sep(", ", &["a", "b", "c"])` writes "a, b, c"
    pub fn sep<I, T>(&mut self, separator: &str, items: I)
    where
        I: IntoIterator<Item = T>,
        T: Display,
    {
        let mut first = true;
        for item in items {
            if !first {
                self.write(separator);
            }
            first = false;
            self.write(&item.to_string());
        }
    }

    /// Write items with a separator, using a custom render function for each item.
    /// Example: `w.sep_with(", ", &items, |w, item| w.write(&item.name))`
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

    /// Write items each on their own line using a render function.
    /// More efficient than building strings and joining.
    pub fn lines_with<I, T, F>(&mut self, items: I, mut render: F)
    where
        I: IntoIterator<Item = T>,
        F: FnMut(&mut Self, T),
    {
        for item in items {
            render(self, item);
            self.newline();
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

    /// Clone this writer's state with a new underlying writer.
    /// Used for rendering to temporary strings while preserving context.
    pub fn clone_with_writer<W2: Write>(&self, writer: W2) -> LeanWriter<W2> {
        LeanWriter {
            out: writer,
            indent: self.indent,
            at_line_start: self.at_line_start,
            inline: self.inline,
        }
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
