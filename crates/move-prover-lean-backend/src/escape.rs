// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Centralized escaping and naming utilities for Lean code generation
//!
//! This module provides functions to:
//! - Escape Move identifiers that conflict with Lean reserved words
//! - Handle type/struct name conflicts with Lean standard library
//! - Convert module names to Lean namespace conventions

/// Lean standard library types that conflict with Move type names
/// If a Move type matches one of these, we prefix it with "Move"
const LEAN_BUILTIN_TYPES: &[&str] = &[
    // Core types
    "Option", "Result", "List", "Array", "String", "Vector", "Nat", "Int", "Bool", "Unit", "Char",
    "Float", // Common Lean types
    "Sum", "Prod", "Sigma", "Subtype", "Quotient", "IO", "Task", "HashMap", "HashSet", "RBMap",
    "RBSet",
];

/// Lean standard modules/namespaces that conflict with Move module names
/// If a Move module matches one of these, we prefix it with "Move"
const LEAN_BUILTIN_MODULES: &[&str] = &[
    "vector", "option", "string", "list", "array", "nat", "int", "bool", "io", "system", "real",
];

/// Escape struct/type names that conflict with Lean built-ins
/// Prefixes conflicting names with "Move"
pub fn escape_struct_name(name: &str) -> String {
    if LEAN_BUILTIN_TYPES.contains(&name) {
        format!("Move{}", name)
    } else {
        name.to_string()
    }
}

/// Check if a type name is a Lean built-in that we intentionally use directly
/// (without namespace qualification because we're using Lean's type, not Move's)
pub fn is_lean_builtin(name: &str) -> bool {
    // Integer is used for spec-level integers (Lean's Integer type)
    // Note: Option is NOT here because we use Move's Option (MoveOption.MoveOption)
    matches!(name, "Integer")
}

/// Convert a Move module name to a Lean namespace name
/// Handles name conflicts with Lean standard modules and capitalizes
pub fn module_name_to_namespace(module_name: &str) -> String {
    // No special case needed - just capitalize normally
    // The rational module becomes Rational namespace

    if LEAN_BUILTIN_MODULES.contains(&module_name) {
        format!("Move{}", capitalize_first(module_name))
    } else {
        capitalize_first(module_name)
    }
}

/// Capitalize first character of a string
pub fn capitalize_first(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

/// Escape identifiers (function names, field names, parameter names) that conflict with Lean reserved words
pub fn escape_identifier(name: &str) -> String {
    // Handle variant suffixes (like "from.pure" -> "from_.pure")
    // Split on '.' and escape the base name, then rejoin
    if let Some(dot_pos) = name.find('.') {
        let base = &name[..dot_pos];
        let suffix = &name[dot_pos..]; // includes the dot
        let escaped_base = escape_identifier(base);
        return format!("{}{}", escaped_base, suffix);
    }

    // Handle $ prefix (temps like $t0, $t1 etc.) - $ is special in Lean
    // Also handle $ anywhere in the name (like tmp#$1 -> tmp_t_1)
    let name = if name.starts_with('$') {
        format!("t_{}", &name[1..])
    } else {
        name.replace('$', "_t_")
    };

    // Replace # with _ (used in loop variable renaming like sum#1#0)
    let name = name.replace('#', "_");

    // Strip SSA suffixes like _1_0, _2_1, etc. for cleaner output
    // Pattern: ends with _<digit>_<digit> or _<digit>_<digit>_<digit>...
    // BUT preserve suffixes like .ensures_0, .ensures_1 (indexed spec functions)
    let name = if name.contains(".ensures_") || name.contains(".requires_") {
        // Don't strip suffix from indexed spec functions
        name
    } else if let Some(base_pos) = name.rfind(|c: char| !c.is_ascii_digit() && c != '_') {
        let suffix_start = base_pos + 1;
        let suffix = &name[suffix_start..];
        // Check if suffix matches pattern like _1_0 or _2_1_3
        if suffix.starts_with('_')
            && suffix
                .chars()
                .skip(1)
                .all(|c| c.is_ascii_digit() || c == '_')
        {
            // Has SSA suffix, strip it
            name[..suffix_start].to_string()
        } else {
            name
        }
    } else {
        name
    };

    match name.as_str() {
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

        _ => name,
    }
}
