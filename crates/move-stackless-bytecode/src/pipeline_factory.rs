// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    axiom_function_analysis::AxiomFunctionAnalysisProcessor,
    borrow_analysis::BorrowAnalysisProcessor,
    clean_and_optimize::CleanAndOptimizeProcessor,
    conditional_merge_insertion::ConditionalMergeInsertionProcessor,
    debug_instrumentation::DebugInstrumenter,
    deterministic_analysis::DeterministicAnalysisProcessor,
    dynamic_field_analysis::DynamicFieldAnalysisProcessor,
    eliminate_imm_refs::EliminateImmRefsProcessor,
    function_target_pipeline::{FunctionTargetPipeline, FunctionTargetProcessor},
    inconsistency_check::InconsistencyCheckInstrumenter,
    livevar_analysis::LiveVarAnalysisProcessor,
    loop_analysis::LoopAnalysisProcessor,
    memory_instrumentation::MemoryInstrumentationProcessor,
    mono_analysis::MonoAnalysisProcessor,
    move_loop_invariants::MoveLoopInvariantsProcessor,
    mut_ref_instrumentation::MutRefInstrumenter,
    mutation_tester::MutationTester,
    no_abort_analysis::NoAbortAnalysisProcessor,
    number_operation_analysis::NumberOperationProcessor,
    options::ProverOptions,
    pure_function_analysis::PureFunctionAnalysisProcessor,
    quantifier_iterator_analysis::QuantifierIteratorAnalysisProcessor,
    reaching_def_analysis::ReachingDefProcessor,
    recursion_analysis::RecursionAnalysisProcessor,
    replacement_analysis::ReplacementAnalysisProcessor,
    spec_global_variable_analysis::SpecGlobalVariableAnalysisProcessor,
    spec_instrumentation::SpecInstrumentationProcessor,
    spec_purity_analysis::SpecPurityAnalysis,
    spec_well_formed_analysis::SpecWellFormedAnalysisProcessor,
    type_invariant_analysis::TypeInvariantAnalysisProcessor,
    usage_analysis::UsageProcessor,
    verification_analysis::VerificationAnalysisProcessor,
    well_formed_instrumentation::WellFormedInstrumentationProcessor,
};

pub fn default_pipeline_with_options(options: &ProverOptions) -> FunctionTargetPipeline {
    // NOTE: the order of these processors is import!
    let mut processors: Vec<Box<dyn FunctionTargetProcessor>> = vec![
        VerificationAnalysisProcessor::new(),
        RecursionAnalysisProcessor::new(),
        SpecGlobalVariableAnalysisProcessor::new(),
        SpecPurityAnalysis::new(),
        DebugInstrumenter::new(),
        // transformation and analysis
        EliminateImmRefsProcessor::new(),
        MutRefInstrumenter::new(),
        NoAbortAnalysisProcessor::new(),
        DeterministicAnalysisProcessor::new(),
        DynamicFieldAnalysisProcessor::new(),
        MoveLoopInvariantsProcessor::new(),
        TypeInvariantAnalysisProcessor::new(),
        ReachingDefProcessor::new(),
        LiveVarAnalysisProcessor::new(),
        BorrowAnalysisProcessor::new_borrow_natives(options.borrow_natives.clone()),
        MemoryInstrumentationProcessor::new(),
    ];

    // Rerun liveness analysis and its dependencies after MemoryInstrumentation
    // to ensure fresh liveness annotations for ConditionalMergeInsertion
    processors.push(ReachingDefProcessor::new());
    processors.push(LiveVarAnalysisProcessor::new());
    processors.push(ConditionalMergeInsertionProcessor::new());

    processors.append(&mut vec![
        CleanAndOptimizeProcessor::new(),
        UsageProcessor::new(),
        SpecWellFormedAnalysisProcessor::new(),
        QuantifierIteratorAnalysisProcessor::new(),
        ReplacementAnalysisProcessor::new(),
        PureFunctionAnalysisProcessor::new(),
        AxiomFunctionAnalysisProcessor::new(),
    ]);

    if !options.skip_loop_analysis {
        processors.push(LoopAnalysisProcessor::new());
    }

    processors.append(&mut vec![
        // spec instrumentation
        SpecInstrumentationProcessor::new(),
        // GlobalInvariantAnalysisProcessor::new(),
        // GlobalInvariantInstrumentationProcessor::new(),
        WellFormedInstrumentationProcessor::new(),
        // DataInvariantInstrumentationProcessor::new(),
        // monomorphization
        MonoAnalysisProcessor::new(),
    ]);

    if options.mutation {
        // pass which may do nothing
        processors.push(MutationTester::new());
    }

    // inconsistency check instrumentation should be the last one in the pipeline
    if options.check_inconsistency {
        processors.push(InconsistencyCheckInstrumenter::new());
    }

    if !options.for_interpretation {
        processors.push(NumberOperationProcessor::new());
    }

    let mut res = FunctionTargetPipeline::default();
    for p in processors {
        res.add_processor(p);
    }
    res
}

pub fn default_pipeline() -> FunctionTargetPipeline {
    default_pipeline_with_options(&ProverOptions::default())
}

pub fn experimental_pipeline() -> FunctionTargetPipeline {
    // Enter your pipeline here
    let processors: Vec<Box<dyn FunctionTargetProcessor>> = vec![
        DebugInstrumenter::new(),
        // transformation and analysis
        EliminateImmRefsProcessor::new(),
        MutRefInstrumenter::new(),
        ReachingDefProcessor::new(),
        LiveVarAnalysisProcessor::new(),
        BorrowAnalysisProcessor::new(),
        MemoryInstrumentationProcessor::new(),
        CleanAndOptimizeProcessor::new(),
        LoopAnalysisProcessor::new(),
        // optimization
        MonoAnalysisProcessor::new(),
    ];

    let mut res = FunctionTargetPipeline::default();
    for p in processors {
        res.add_processor(p);
    }
    res
}
