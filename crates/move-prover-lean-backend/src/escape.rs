// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Centralized escaping utilities for Lean identifiers and names
//!
//! This module provides functions to escape Move identifiers that conflict
//! with Lean reserved words or built-in types.

/// Escape struct/type names that conflict with Lean built-ins
///
/// Note: Option is intentionally NOT escaped - we use Lean's Option type
pub fn escape_struct_name(name: &str) -> String {
    match name {
        "Result" => "MoveResult".to_string(),
        "List" => "MoveList".to_string(),
        "String" => "MoveString".to_string(),
        "Vector" => "MoveVector".to_string(),
        _ => name.to_string(),
    }
}

/// Escape identifiers (function names, field names, parameter names) that conflict with Lean reserved words
pub fn escape_identifier(name: &str) -> String {
    match name {
        // Basic control flow
        "if" => "if_".to_string(),
        "then" => "then_".to_string(),
        "else" => "else_".to_string(),
        "let" => "let_".to_string(),
        "in" => "in_".to_string(),
        "do" => "do_".to_string(),
        "for" => "for_".to_string(),
        "while" => "while_".to_string(),
        "match" => "match_".to_string(),
        "fun" => "fun_".to_string(),
        "λ" => "lambda_".to_string(),

        // Declaration keywords
        "axiom" => "axiom_".to_string(),
        "theorem" => "theorem_".to_string(),
        "lemma" => "lemma_".to_string(),
        "example" => "example_".to_string(),
        "opaque" => "opaque_".to_string(),
        "def" => "def_".to_string(),
        "abbrev" => "abbrev_".to_string(),

        // Proof keywords
        "by" => "by_".to_string(),
        "done" => "done_".to_string(),
        "from" => "from_".to_string(),
        "using" => "using_".to_string(),
        "have" => "have_".to_string(),
        "show" => "show_".to_string(),
        "suffices" => "suffices_".to_string(),
        "calc" => "calc_".to_string(),
        "mutual" => "mutual_".to_string(),

        // Module/namespace keywords
        "section" => "section_".to_string(),
        "namespace" => "namespace_".to_string(),
        "end" => "end_".to_string(),
        "variable" => "variable_".to_string(),
        "universe" => "universe_".to_string(),

        // Import/export keywords
        "import" => "import_".to_string(),
        "export" => "export_".to_string(),
        "open" => "open_".to_string(),
        "hiding" => "hiding_".to_string(),
        "renaming" => "renaming_".to_string(),
        "extending" => "extending_".to_string(),

        // Visibility/modifiers
        "private" => "private_".to_string(),
        "protected" => "protected_".to_string(),
        "noncomputable" => "noncomputable_".to_string(),
        "partial" => "partial_".to_string(),
        "unsafe" => "unsafe_".to_string(),

        // Type definition keywords
        "inductive" => "inductive_".to_string(),
        "coinductive" => "coinductive_".to_string(),
        "structure" => "structure_".to_string(),
        "class" => "class_".to_string(),
        "instance" => "instance_".to_string(),
        "deriving" => "deriving_".to_string(),
        "extends" => "extends_".to_string(),
        "where" => "where_".to_string(),

        // Notation keywords
        "notation" => "notation_".to_string(),
        "infix" => "infix_".to_string(),
        "prefix" => "prefix_".to_string(),
        "postfix" => "postfix_".to_string(),

        // Metaprogramming keywords
        "macro" => "macro_".to_string(),
        "elab" => "elab_".to_string(),
        "syntax" => "syntax_".to_string(),

        // Other keywords
        "extern" => "extern_".to_string(),
        "constant" => "constant_".to_string(),

        _ => name.to_string(),
    }
}

/// Capitalize first character
pub fn capitalize_first(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

/// Check if a type is a Lean built-in that shouldn't be namespace-qualified
pub fn is_lean_builtin(name: &str) -> bool {
    matches!(name, "Option" | "Integer")
}
