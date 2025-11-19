// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Native function implementations mapping
//!
//! Maps Move native functions to their Lean implementations from the lemma system.

/// Get the native implementation for a function, if one exists
/// Returns the Lean function name to call instead of rendering the body
pub fn get_native_impl(module_name: &str, function_name: &str) -> Option<String> {
    // Check if this is a known native function
    let key = format!("{}::{}", module_name, function_name);

    match key.as_str() {
        // Vector operations (0x1::vector)
        "0x1::vector::empty" => Some("vector_empty".to_string()),
        "0x1::vector::length" => Some("vector_length".to_string()),
        "0x1::vector::borrow" => Some("vector_borrow".to_string()),
        "0x1::vector::push_back" => Some("vector_push_back".to_string()),
        "0x1::vector::pop_back" => Some("vector_pop_back".to_string()),
        "0x1::vector::swap" => Some("vector_swap".to_string()),
        "0x1::vector::is_empty" => Some("vector_is_empty".to_string()),
        "0x1::vector::contains" => Some("vector_contains".to_string()),
        "0x1::vector::index_of" => Some("vector_index_of".to_string()),
        "0x1::vector::remove" => Some("vector_remove".to_string()),
        "0x1::vector::insert" => Some("vector_insert".to_string()),
        "0x1::vector::swap_remove" => Some("vector_swap_remove".to_string()),
        "0x1::vector::append" => Some("vector_append".to_string()),
        "0x1::vector::reverse" => Some("vector_reverse".to_string()),
        "0x1::vector::singleton" => Some("vector_singleton".to_string()),
        "0x1::vector::destroy_empty" => Some("vector_destroy_empty".to_string()),
        "0x1::vector::borrow_mut" => Some("vector_borrow_mut".to_string()),
        "0x1::vector::take" => Some("vector_take".to_string()),
        "0x1::vector::skip" => Some("vector_skip".to_string()),
        "0x1::vector::flatten" => Some("vector_flatten".to_string()),

        _ => None,
    }
}

/// Get the actual return type for a native function (if it differs from Move signature)
/// Move signatures may declare void functions as returning values due to reference semantics
pub fn get_native_return_type_override(module_name: &str, function_name: &str) -> Option<String> {
    let key = format!("{}::{}", module_name, function_name);

    match key.as_str() {
        // Functions that return Unit but Move declares them as returning other types
        "0x1::vector::push_back" => Some("Unit".to_string()),
        "0x1::vector::swap" => Some("Unit".to_string()),
        "0x1::vector::insert" => Some("Unit".to_string()),
        "0x1::vector::append" => Some("Unit".to_string()),
        "0x1::vector::reverse" => Some("Unit".to_string()),
        "0x1::vector::destroy_empty" => Some("Unit".to_string()),

        // Note: Spec functions (prover::drop_spec, debug_spec::*, event_spec::*)
        // are NOT overridden because they have bytecode bodies that use do notation
        // and must return ProgramState Unit, not bare Unit

        _ => None,
    }
}

/// Check if a function is a native function that should use implementations from lemmas
pub fn is_native_with_impl(module_name: &str, function_name: &str) -> bool {
    get_native_impl(module_name, function_name).is_some()
}

/// Get the set of lemma imports needed for native functions
pub fn get_native_imports() -> Vec<String> {
    vec![
        "Lemmas.Universal.Vector".to_string(),
    ]
}
