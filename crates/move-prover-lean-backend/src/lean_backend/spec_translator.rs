// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! This module translates specification conditions to Lean code.
/// This file is nearly identical to Boogie's spec_translator.rs, with minor var name changes.
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[allow(unused_imports)]
use log::{debug, info, warn};

use crate::lean_backend::options::LeanOptions;
use move_model::{
    code_writer::CodeWriter,
    emit,
    model::{DatatypeId, GlobalEnv, Loc, NodeId, QualifiedInstId},
    symbol::Symbol,
    ty::Type,
};
use move_stackless_bytecode::ast::{Exp, ExpData, MemoryLabel, QuantKind, TempIndex};

#[derive(Clone)]
pub struct SpecTranslator<'env> {
    /// The global environment.
    env: &'env GlobalEnv,
    /// Options passed into the translator.
    options: &'env LeanOptions,
    /// The code writer.
    writer: &'env CodeWriter,
    /// If we are translating in the context of a type instantiation, the type arguments.
    type_inst: Vec<Type>,
    /// Counter for creating new variables.
    fresh_var_count: RefCell<usize>,
    /// Information about lifted choice expressions. Each choice expression in the
    /// original program is uniquely identified by the choice expression AST (verbatim),
    /// which includes the node id of the expression.
    ///
    /// This allows us to capture duplication of expressions and map them to the same uninterpreted
    /// choice function. If an expression is duplicated and then later specialized by a type
    /// instantiation, it will have a different node id, but again the same instantiations
    /// map to the same node id, which is the desired semantics.
    lifted_choice_infos: Rc<RefCell<HashMap<(ExpData, Vec<Type>), LiftedChoiceInfo>>>,
}

/// A struct which contains information about a lifted choice expression (like `some x:int: p(x)`).
/// Those expressions are replaced by a call to an axiomatized function which is generated from
/// this info at the end of translation.
#[derive(Clone)]
struct LiftedChoiceInfo {
    id: usize,
    node_id: NodeId,
    kind: QuantKind,
    free_vars: Vec<(Symbol, Type)>,
    used_temps: Vec<(TempIndex, Type)>,
    used_memory: Vec<(QualifiedInstId<DatatypeId>, Option<MemoryLabel>)>,
    var: Symbol,
    range: Exp,
    condition: Exp,
}

impl<'env> SpecTranslator<'env> {
    /// Creates a translator.
    pub fn new(writer: &'env CodeWriter, env: &'env GlobalEnv, options: &'env LeanOptions) -> Self {
        Self {
            env,
            options,
            writer,
            type_inst: vec![],
            fresh_var_count: Default::default(),
            lifted_choice_infos: Default::default(),
        }
    }

    /// Emits a translation error.
    pub fn error(&self, loc: &Loc, msg: &str) {
        self.env.error(loc, &format!("[lean translator] {}", msg));
    }

    /// Sets the location of the code writer from node id.
    fn set_writer_location(&self, node_id: NodeId) {
        self.writer.set_location(&self.env.get_node_loc(node_id));
    }

    /// Generates a fresh variable name.
    fn fresh_var_name(&self, prefix: &str) -> String {
        let mut fvc_ref = self.fresh_var_count.borrow_mut();
        let name_str = format!("${}_{}", prefix, *fvc_ref);
        *fvc_ref = usize::saturating_add(*fvc_ref, 1);
        name_str
    }

    /// Translates a sequence of items separated by `sep`.
    fn translate_seq<T, F>(&self, items: impl Iterator<Item = T>, sep: &str, f: F)
    where
        F: Fn(T),
    {
        let mut first = true;
        for item in items {
            if first {
                first = false;
            } else {
                emit!(self.writer, sep);
            }
            f(item);
        }
    }
}

// Emit any finalization items
// ============================

impl<'env> SpecTranslator<'env> {
    pub(crate) fn finalize(&self) {}
}
