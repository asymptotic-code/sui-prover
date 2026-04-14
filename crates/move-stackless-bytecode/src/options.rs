// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use codespan_reporting::diagnostic::Severity;
use move_model::model::VerificationScope;
use serde::{Deserialize, Serialize};

#[derive(Debug, Copy, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd)]
pub enum AutoTraceLevel {
    Off,
    VerifiedFunction,
    AllFunctions,
}

impl AutoTraceLevel {
    pub fn verified_functions(self) -> bool {
        use AutoTraceLevel::*;
        matches!(self, VerifiedFunction | AllFunctions)
    }
    pub fn functions(self) -> bool {
        use AutoTraceLevel::*;
        matches!(self, AllFunctions)
    }
    pub fn invariants(self) -> bool {
        use AutoTraceLevel::*;
        matches!(self, VerifiedFunction | AllFunctions)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd)]
#[serde(default, deny_unknown_fields)]
pub struct ProverOptions {
    /// Whether to only generate backend code.
    pub generate_only: bool,
    /// Whether to generate stubs for native functions.
    pub native_stubs: bool,
    /// Whether to minimize execution traces in errors.
    pub minimize_execution_trace: bool,
    /// Whether to omit debug information in generated model.
    pub omit_model_debug: bool,
    /// Whether output for e.g. diagnosis shall be stable/redacted so it can be used in test
    /// output.
    pub stable_test_output: bool,
    /// Scope of what functions to verify.
    pub verify_scope: VerificationScope,
    /// [deprecated] Whether to emit global axiom that resources are well-formed.
    pub resource_wellformed_axiom: bool,
    /// Whether to assume wellformedness when elements are read from memory, instead of on
    /// function entry.
    pub assume_wellformed_on_access: bool,
    /// Indicates that we should do any mutations
    pub mutation: bool,
    /// Indicates that we should use the add-subtract mutation on the given block
    pub mutation_add_sub: usize,
    /// Indicates that we should use the subtract-add mutation on the given block
    pub mutation_sub_add: usize,
    /// Indicates that we should use the multiply-divide mutation on the given block
    pub mutation_mul_div: usize,
    /// Indicates that we should use the divide-multiply mutation on the given block
    pub mutation_div_mul: usize,
    /// Whether to use the polymorphic boogie backend.
    pub boogie_poly: bool,
    /// Whether pack/unpack should recurse over the structure.
    pub deep_pack_unpack: bool,
    /// Auto trace level.
    pub auto_trace_level: AutoTraceLevel,
    /// Minimal severity level for diagnostics to be reported.
    pub report_severity: Severity,
    /// Whether to dump the transformed stackless bytecode to a file
    pub dump_bytecode: bool,
    /// Whether to dump the control-flow graphs (in dot format) to files, one per each function
    pub dump_cfg: bool,
    /// Number of Boogie instances to be run concurrently.
    pub num_instances: usize,
    /// Whether to run Boogie instances sequentially.
    pub sequential_task: bool,
    /// Whether to check the inconsistency
    pub check_inconsistency: bool,
    /// Whether to consider a function that abort unconditionally as an inconsistency violation
    pub unconditional_abort_as_inconsistency: bool,
    /// Whether to run the transformation passes for concrete interpretation (instead of proving)
    pub for_interpretation: bool,
    /// Whether to skip loop analysis.
    pub skip_loop_analysis: bool,
    /// Whether to enable conditional merge insertion.
    pub enable_conditional_merge_insertion: bool,
    /// Optional names of native methods (qualified with module name, e.g., m::foo) implementing
    /// mutable borrow semantics
    pub borrow_natives: Vec<String>,
    /// Whether to ban convertion from int to bv at the boogie backend
    pub ban_int_2_bv: bool,
    /// Whether to encode u8/u16/u32/u64/u128/u256 as integer or bitvector
    pub bv_int_encoding: bool,
    /// Skip checking spec functions that do not abort
    pub skip_spec_no_abort: bool,
    /// Skip checking external functions that do not abort
    pub skip_fun_no_abort: bool,
    /// CI mode
    pub ci: bool,
    /// Whether to emit debug trace instructions for counterexample generation
    pub debug_trace: bool,
}

// add custom struct for mutation options

impl Default for ProverOptions {
    fn default() -> Self {
        Self {
            generate_only: false,
            native_stubs: false,
            minimize_execution_trace: true,
            omit_model_debug: false,
            stable_test_output: false,
            verify_scope: VerificationScope::All,
            resource_wellformed_axiom: false,
            assume_wellformed_on_access: false,
            mutation: false,
            mutation_add_sub: 0,
            mutation_sub_add: 0,
            mutation_mul_div: 0,
            mutation_div_mul: 0,
            boogie_poly: false,
            deep_pack_unpack: false,
            auto_trace_level: AutoTraceLevel::Off,
            report_severity: Severity::Warning,
            dump_bytecode: false,
            dump_cfg: false,
            num_instances: 1,
            sequential_task: false,
            check_inconsistency: false,
            unconditional_abort_as_inconsistency: false,
            for_interpretation: false,
            skip_loop_analysis: false,
            enable_conditional_merge_insertion: false,
            borrow_natives: vec![],
            ban_int_2_bv: false,
            bv_int_encoding: true,
            skip_spec_no_abort: false,
            skip_fun_no_abort: false,
            ci: false,
            debug_trace: true,
        }
    }
}
