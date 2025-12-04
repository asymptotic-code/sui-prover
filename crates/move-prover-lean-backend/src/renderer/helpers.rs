// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Functional helpers for common rendering patterns

use crate::escape;
use intermediate_theorem_format::IRNode;

/// Check if a variable name looks like a compiler-generated temporary
pub fn is_compiler_temp(name: &str) -> bool {
    name.starts_with("tmp__") || name.starts_with("__")
}

/// Render a tuple-like structure: empty→empty_val, single→element, multiple→`(a, b, c)`
pub fn render_tuple_like<T, F>(items: &[T], empty_val: &str, separator: &str, render_fn: F) -> String
where
    F: Fn(&T) -> String,
{
    match items {
        [] => empty_val.to_string(),
        [single] => render_fn(single),
        multiple => {
            let rendered: Vec<_> = multiple.iter().map(render_fn).collect();
            format!("({})", rendered.join(separator))
        }
    }
}

/// Make a binding pattern from variable names
pub fn make_pattern<S: AsRef<str>>(names: &[S]) -> String {
    render_tuple_like(names, "_", ", ", |name| {
        let name = name.as_ref();
        if name == "()" {
            "_".to_string()
        } else {
            escape::escape_identifier(name)
        }
    })
}

/// Render a list with a separator
pub fn join_with<T, F>(items: &[T], separator: &str, render_fn: F) -> String
where
    F: Fn(&T) -> String,
{
    items.iter().map(render_fn).collect::<Vec<_>>().join(separator)
}

/// Check if an IR node needs parentheses when used as an argument
pub fn needs_parens(ir: &IRNode) -> bool {
    !ir.is_atomic()
}

/// Wrap in parens if needed
pub fn with_parens_if_needed(s: String, needs_parens: bool) -> String {
    if needs_parens {
        format!("({})", s)
    } else {
        s
    }
}

/// Render a do block prefix based on monadicity
pub fn do_prefix(is_monadic: bool) -> &'static str {
    if is_monadic {
        "do"
    } else {
        "Id.run do"
    }
}

/// Render a bind operator based on monadicity
pub fn bind_op(is_monadic: bool) -> &'static str {
    if is_monadic {
        "←"
    } else {
        ":="
    }
}

/// Construct a variable tuple from names
pub fn var_tuple(vars: &[String]) -> IRNode {
    match vars {
        [] => IRNode::Tuple(vec![]),
        [single] => IRNode::Var(single.clone()),
        multiple => IRNode::Tuple(multiple.iter().map(|v| IRNode::Var(v.clone())).collect()),
    }
}
