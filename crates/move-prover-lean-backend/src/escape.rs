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
        "from" => "from_".to_string(),
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
        "class" => "class_".to_string(),
        "instance" => "instance_".to_string(),
        "where" => "where_".to_string(),
        "extends" => "extends_".to_string(),
        "import" => "import_".to_string(),
        "export" => "export_".to_string(),
        "namespace" => "namespace_".to_string(),
        "end" => "end_".to_string(),
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
