use crate::lean_backend::options::LeanOptions;
use move_model::code_writer::CodeWriter;
use move_model::model::GlobalEnv;
use move_model::ty::{PrimitiveType, Type};
use move_model::{emit, emitln};
use move_stackless_bytecode::mono_analysis;
use std::collections::BTreeSet;
use std::fs;
use tera::{Context, Tera};

pub mod generator;
pub mod generator_options;
mod lean_backend;

const PRELUDE_INTEGER: &'static str = include_str!("lean_backend/prelude/integer.lean");

/// Adds the prelude to the generated output.
pub fn add_prelude(
    env: &GlobalEnv,
    options: &LeanOptions,
    writer: &CodeWriter,
) -> anyhow::Result<()> {
    emit!(writer, "\n-- ** Expanded prelude\n\n");
    emitln!(writer, PRELUDE_INTEGER);
    Ok(())
}
