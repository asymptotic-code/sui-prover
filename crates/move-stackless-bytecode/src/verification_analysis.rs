// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! Analysis which computes an annotation for each function on whether this function should be
//! verified or inlined. It also calculates the set of global invariants that are applicable to
//! each function as well as collect information on how these invariants should be handled (i.e.,
//! checked after bytecode, checked at function exit, or deferred to caller).

use std::collections::BTreeSet;
use std::fmt::{self, Formatter};
use move_model::model::{FunctionEnv, GlobalEnv, VerificationScope};

use crate::{
  function_target::{FunctionData, FunctionTarget}, function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant}, options::ProverOptions
};
use move_model::model::{FunId, QualifiedId};

/// The annotation for information about verification.
#[derive(Clone, Default)]
pub struct VerificationInfo {
    /// Whether the function is target of verification.
    pub verified: bool,
    /// Whether the function needs to have an inlined variant since it is called from a verified
    /// function and is not opaque.
    pub inlined: bool,
    /// Whether the function is essential for the verification pipeline (e.g., native functions
    /// needed for compilation) even if not verified or inlined.
    pub essential: bool,
}

/// Get verification information for this function.
pub fn get_info(target: &FunctionTarget<'_>) -> VerificationInfo {
    target
        .get_annotations()
        .get::<VerificationInfo>()
        .cloned()
        .unwrap_or_default()
}

// /// A named tuple for holding the information on how an invariant is relevant to a function.
// pub struct InvariantRelevance {
//     /// Global invariants covering memories that are accessed in a function
//     pub accessed: BTreeSet<GlobalId>,
//     /// Global invariants covering memories that are modified in a function
//     pub modified: BTreeSet<GlobalId>,
//     /// Global invariants covering memories that are directly accessed in a function
//     pub direct_accessed: BTreeSet<GlobalId>,
//     /// Global invariants covering memories that are directly modified in a function
//     pub direct_modified: BTreeSet<GlobalId>,
// }

// /// Analysis info saved for the global_invariant_instrumentation phase
// pub struct InvariantAnalysisData {
//     /// Functions which have invariants checked on return instead of in body
//     pub fun_set_with_inv_check_on_exit: BTreeSet<QualifiedId<FunId>>,
//     /// Functions which invariants checking is turned-off anywhere in the function
//     pub fun_set_with_no_inv_check: BTreeSet<QualifiedId<FunId>>,
//     /// A mapping from function to the set of global invariants used and modified, respectively
//     pub fun_to_inv_map: BTreeMap<QualifiedId<FunId>, InvariantRelevance>,
// }

// The function target processor
pub struct VerificationAnalysisProcessor();

impl VerificationAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for VerificationAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        // This function implements the logic to decide whether to verify this function
        let fun_name = fun_env.get_full_name_str();
        println!("DEBUG: Processing function: {}", fun_name);

        // Rule 0a: mark essential functions that are needed for the verification pipeline
        let info = data.annotations.get_or_default_mut::<VerificationInfo>(true);
        if Self::is_essential_function(fun_env) {
            info.essential = true;
            println!("DEBUG: Marking essential function: {}", fun_name);
        }

        // Rule 0: mark invariant functions as inlined
        if targets
            .get_datatype_by_inv(&fun_env.get_qualified_id())
            .is_some()
        {
            let info = data
                .annotations
                .get_or_default_mut::<VerificationInfo>(true);
            if !info.inlined {
                info.inlined = true;
                Self::mark_callees_inlined(fun_env, targets);
            }
            return data;
        }

        // // Rule 1: never verify if "pragma verify = false;"
        // if !fun_env.is_pragma_true(VERIFY_PRAGMA, || true) {
        //     return data;
        // }

        // Rule 2: verify the function if it is within the target modules
        let env = fun_env.module_env.env;
        let target_modules = env.get_target_modules();

        let is_in_target_module = target_modules
            .iter()
            .any(|menv| menv.get_id() == fun_env.module_env.get_id());
        if is_in_target_module {
            println!("DEBUG: Function {} is in target module", fun_name);
            if targets.is_spec(&fun_env.get_qualified_id())
                && Self::is_within_verification_scope(fun_env)
            {
                println!("DEBUG: Marking function {} as verified", fun_name);
                Self::mark_verified(fun_env, &mut data, targets);
                // let dynamic_loc = Self::find_dynamics_in_function(&self, fun_env, &data);
                // if dynamic_loc.is_some() {
                //     env.diag(
                //         Severity::Error,
                //         &dynamic_loc.unwrap(),
                //         "Function uses unsupported dynamic fields",
                //     );
                // }
            } else {
                println!("DEBUG: Function {} is not a spec or not in verification scope", fun_name);
            }
            return data;
        } else {
            println!("DEBUG: Function {} is not in target module", fun_name);
        }

        // // Rule 3: verify the function if a global invariant (including update invariant) that is
        // // defined in the target modules (a.k.a. a target invariant) need to be checked in the
        // // function, i.e., the function directly modifies some memory that are covered by at least
        // // one of the target invariants.
        // let inv_analysis = env.get_extension::<InvariantAnalysisData>().unwrap();
        // let target_invs: BTreeSet<_> = target_modules
        //     .iter()
        //     .flat_map(|menv| env.get_global_invariants_by_module(menv.get_id()))
        //     .collect();
        // let inv_relevance = inv_analysis
        //     .fun_to_inv_map
        //     .get(&fun_env.get_qualified_id())
        //     .unwrap();
        // if !inv_relevance.direct_modified.is_disjoint(&target_invs) {
        //     if Self::is_within_verification_scope(fun_env) {
        //         Self::mark_verified(fun_env, &mut data, targets);
        //     }
        //     return data;
        // }

        // we don't verify this function
        data
    }

    fn name(&self) -> String {
        "verification_analysis".to_string()
    }

    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // Remove functions that aren't used for verification
        // Keep: verified functions, inlined functions, essential functions, datatype invariant functions
        
        println!("DEBUG: Starting verification analysis finalize");
        println!("DEBUG: Total functions in targets before filtering: {}", targets.get_funs().count());
        
        let mut functions_to_keep = BTreeSet::new();
        
        // Keep all datatype invariant functions (even if not inlined)
        for (_, inv_fun_id) in targets.get_datatype_invs() {
            functions_to_keep.insert(inv_fun_id.clone());
            println!("DEBUG: Keeping datatype invariant function: {}", env.get_function(inv_fun_id.clone()).get_full_name_str());
        }
        
        // Collect all function IDs first to avoid borrowing issues
        let all_function_ids: Vec<QualifiedId<FunId>> = targets.get_funs().collect();
        
        // Keep all functions that are marked as verified, inlined, or essential
        for fun_id in all_function_ids {
            let fun_env = env.get_function(fun_id);
            let fun_name = fun_env.get_full_name_str();
            
            // Check if this function has any variants that are verified or inlined
            let mut should_keep = false;
            for variant in targets.get_target_variants(&fun_env) {
                if let Some(data) = targets.get_data(&fun_id, &variant) {
                    let info = get_info(&FunctionTarget::new(&fun_env, data));
                    if info.verified || info.inlined {
                        should_keep = true;
                        println!("Keeping function {}: verified={}, inlined={}", 
                                fun_name, info.verified, info.inlined);
                        break;
                    }
                }
            }
            
            // Also keep compiler-generated functions (prover and ghost packages only)
            if !should_keep && Self::is_compiler_generated_function(&fun_env) {
                should_keep = true;
                println!("Keeping compiler-generated function: {}", fun_name);
                
                // Mark essential functions as essential in their data annotations
                for variant in targets.get_target_variants(&fun_env) {
                    if let Some(data) = targets.get_data_mut(&fun_id, &variant) {
                        let info = data.annotations.get_or_default_mut::<VerificationInfo>(true);
                        info.essential = true;
                    }
                }
            }
            
            if should_keep {
                functions_to_keep.insert(fun_id.clone());
            }
        }
        
        println!("DEBUG: Functions to keep after first pass: {}", functions_to_keep.len());
        
        // Second pass: recursively keep all callees of inlined functions and dependencies
        let mut functions_to_add = Vec::new();
        let mut processed_functions = BTreeSet::new();
        
        // Start with the functions we've already decided to keep
        let mut functions_to_process: Vec<(QualifiedId<FunId>, bool)> = functions_to_keep.iter().map(|id| (*id, true)).collect();
        println!("DEBUG: Starting with {} functions to process", functions_to_process.len());
        
        println!("DEBUG: Starting callee and dependency processing loop");
        while !functions_to_process.is_empty() {
            let (fun_id, mark_as_inlined) = functions_to_process.pop().unwrap();
            
            if processed_functions.contains(&fun_id) {
                continue;
            }
            processed_functions.insert(fun_id.clone());
            
            let fun_env = env.get_function(fun_id);
            
            // Check if this function is inlined or verified (needs deep analysis)
            let mut needs_deep_analysis = false;
            for variant in targets.get_target_variants(&fun_env) {
                if let Some(data) = targets.get_data(&fun_id, &variant) {
                    let info = get_info(&FunctionTarget::new(&fun_env, data));
                    if info.inlined || info.verified {
                        needs_deep_analysis = true;
                        break;
                    }
                }
            }
            
            // If this function needs deep analysis, keep all its callees
            if needs_deep_analysis {
                for callee in fun_env.get_called_functions() {
                    if !functions_to_keep.contains(&callee) && !processed_functions.contains(&callee) {
                        functions_to_add.push(callee);
                        // Add to processing for recursive exploration
                        // Mark callees as inlined only if the caller is inlined, not just verified
                        let should_mark_callee_inlined = mark_as_inlined && {
                            let mut caller_is_inlined = false;
                            for variant in targets.get_target_variants(&fun_env) {
                                if let Some(data) = targets.get_data(&fun_id, &variant) {
                                    let info = get_info(&FunctionTarget::new(&fun_env, data));
                                    if info.inlined {
                                        caller_is_inlined = true;
                                        break;
                                    }
                                }
                            }
                            caller_is_inlined
                        };
                        
                        functions_to_process.push((callee, should_mark_callee_inlined));
                        println!("Keeping callee of function {}: {} (mark_inlined: {})", 
                                fun_env.get_full_name_str(), env.get_function(callee).get_full_name_str(), should_mark_callee_inlined);
                        
                        // Mark the callee as inlined if needed
                        if should_mark_callee_inlined {
                            let callee_env = env.get_function(callee);
                            for variant in targets.get_target_variants(&callee_env) {
                                if let Some(data) = targets.get_data_mut(&callee, &variant) {
                                    let info = data.annotations.get_or_default_mut::<VerificationInfo>(true);
                                    if !info.inlined {
                                        info.inlined = true;
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                // Even if this function doesn't need deep analysis, we still need to keep its callees
                // for dependency reasons (like spec functions needed by borrow analysis)
                for callee in fun_env.get_called_functions() {
                    if !functions_to_keep.contains(&callee) && !processed_functions.contains(&callee) {
                        functions_to_add.push(callee);
                        // Add to processing but don't mark as inlined (just dependency)
                        functions_to_process.push((callee, false));
                        println!("Keeping dependency of function {}: {}", 
                                fun_env.get_full_name_str(), env.get_function(callee).get_full_name_str());
                    }
                }
            }
        }
        
        // Add the callees to the keep set
        for fun_id in functions_to_add {
            functions_to_keep.insert(fun_id);
        }
        
        println!("DEBUG: Total functions to keep after callee processing: {}", functions_to_keep.len());
        
        // Remove functions that are not in the keep set
        let functions_to_remove: Vec<QualifiedId<FunId>> = targets
            .get_funs()
            .filter(|fun_id| !functions_to_keep.contains(fun_id))
            .collect();
            
        println!("DEBUG: Functions to remove: {}", functions_to_remove.len());
        
        // Debug: print functions being removed
        for fun_id in &functions_to_remove {
            let fun_env = env.get_function(*fun_id);
            let fun_name = fun_env.get_full_name_str();
            println!("Removing function: {}", fun_name);
        }
            
        for fun_id in functions_to_remove {
            targets.remove_target(&fun_id);
        }
        
        println!("DEBUG: Final function count after filtering: {}", targets.get_funs().count());
    }

    fn dump_result(
        &self,
        f: &mut Formatter<'_>,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> fmt::Result {
        writeln!(f, "\n********* Result of verification analysis *********\n")?;

        // let analysis = env
        //     .get_extension::<InvariantAnalysisData>()
        //     .expect("Verification analysis not performed");

        // writeln!(f, "functions that defer invariant checking at return: [")?;
        // for fun_id in &analysis.fun_set_with_inv_check_on_exit {
        //     writeln!(f, "  {}", env.get_function(*fun_id).get_full_name_str())?;
        // }
        // writeln!(f, "]\n")?;

        // writeln!(f, "functions that delegate invariants to its callers: [")?;
        // for fun_id in &analysis.fun_set_with_no_inv_check {
        //     writeln!(f, "  {}", env.get_function(*fun_id).get_full_name_str())?;
        // }
        // writeln!(f, "]\n")?;

        // writeln!(f, "invariant applicability: [")?;
        // let target_invs: BTreeSet<_> = env
        //     .get_target_modules()
        //     .iter()
        //     .flat_map(|menv| env.get_global_invariants_by_module(menv.get_id()))
        //     .collect();

        // let fmt_inv_ids = |ids: &BTreeSet<GlobalId>| -> String {
        //     ids.iter()
        //         .map(|i| {
        //             if target_invs.contains(i) {
        //                 format!("{}*", i)
        //             } else {
        //                 i.to_string()
        //             }
        //         })
        //         .join(", ")
        // };

        // for (fun_id, inv_relevance) in &analysis.fun_to_inv_map {
        //     writeln!(f, "  {}: {{", env.get_function(*fun_id).get_full_name_str())?;
        //     writeln!(
        //         f,
        //         "    accessed: [{}]",
        //         fmt_inv_ids(&inv_relevance.accessed)
        //     )?;
        //     writeln!(
        //         f,
        //         "    modified: [{}]",
        //         fmt_inv_ids(&inv_relevance.modified)
        //     )?;
        //     writeln!(
        //         f,
        //         "    directly accessed: [{}]",
        //         fmt_inv_ids(&inv_relevance.direct_accessed)
        //     )?;
        //     writeln!(
        //         f,
        //         "    directly modified: [{}]",
        //         fmt_inv_ids(&inv_relevance.direct_modified)
        //     )?;
        //     writeln!(f, "  }}")?;
        // }
        // writeln!(f, "]\n")?;

        writeln!(f, "verification analysis: [")?;
        for fun_id in targets.get_funs() {
            let fenv = env.get_function(fun_id);
            for fun_variant in targets.get_target_variants(&fenv) {
                let target = targets.get_target(&fenv, &fun_variant);
                let result = get_info(&target);
                write!(f, "  {}: ", fenv.get_full_name_str())?;
                if result.verified {
                    if result.inlined {
                        writeln!(f, "verified + inlined")?;
                    } else {
                        writeln!(f, "verified")?;
                    }
                } else if result.inlined {
                    writeln!(f, "inlined")?;
                } else {
                    writeln!(f, "not verified and not inlined")?;
                }
            }
        }
        writeln!(f, "]")
    }

    fn initialize(&self, env: &GlobalEnv, _targets: &mut FunctionTargetsHolder) {
        let options = ProverOptions::get(env);

        // If we are verifying only one function or module, check that this indeed exists.
        match &options.verify_scope {
            VerificationScope::Only(name) | VerificationScope::OnlyModule(name) => {
                let for_module = matches!(&options.verify_scope, VerificationScope::OnlyModule(_));
                let mut target_exists = false;
                for module in env.get_modules() {
                    if module.is_target() {
                        if for_module {
                            target_exists = module.matches_name(name)
                        } else {
                            target_exists = module.get_functions().any(|f| f.matches_name(name));
                        }
                        if target_exists {
                            break;
                        }
                    }
                }
                if !target_exists {
                    env.error(
                        &env.unknown_loc(),
                        &format!(
                            "{} target {} does not exist in target modules",
                            if for_module { "module" } else { "function" },
                            name
                        ),
                    )
                }
            }
            _ => {}
        }

        // // Collect information for global invariant instrumentation

        // // probe how global invariants will be evaluated in the functions
        // let (fun_set_with_inv_check_on_exit, fun_set_with_no_inv_check) =
        //     Self::probe_invariant_status_in_functions(env);

        // // get a map on how invariants are applicable in functions
        // let fun_to_inv_map = Self::build_function_to_invariants_map(env, targets);

        // // error checking, this needs to be done after the invariant applicability map because some
        // // rules depends on information in that map.
        // for fun_id in &fun_set_with_no_inv_check {
        //     let fun_env = env.get_function(*fun_id);

        //     // Rule 1: external-facing functions are not allowed in the N set (i.e., have invariant
        //     // checking completely turned-off), UNLESS they don't modify any memory that are checked
        //     // in any suspendable invariant.
        //     if fun_env.has_unknown_callers() {
        //         let relevance = fun_to_inv_map.get(fun_id).unwrap();
        //         let num_suspendable_inv_modified = relevance
        //             .modified
        //             .iter()
        //             .filter(|inv_id| is_invariant_suspendable(env, **inv_id))
        //             .count();
        //         if num_suspendable_inv_modified != 0 {
        //             if is_invariant_checking_delegated(&fun_env) {
        //                 let message = "Public or script functions cannot delegate invariants";
        //                 env.error(&fun_env.get_loc(), message);
        //             } else {
        //                 let message = "Public or script functions cannot be transitively \
        //                 called by functions disabling or delegating invariants";
        //                 let trace = Self::compute_non_inv_cause_chain(&fun_env);
        //                 env.error_with_notes(&fun_env.get_loc(), message, trace);
        //             };
        //         }
        //     }

        //     // Rule 2: a function cannot be both on the E set and N set, i.e., a function cannot
        //     // have invariant checking turned-off completely while also checking the invariant at
        //     // the function return.
        //     if fun_set_with_inv_check_on_exit.contains(fun_id) {
        //         let message = format!(
        //             "Functions must not have `pragma {}` when invariant checking is turned-off on \
        //             this function",
        //             DISABLE_INVARIANTS_IN_BODY_PRAGMA,
        //         );
        //         let trace = Self::compute_non_inv_cause_chain(&fun_env);
        //         env.error_with_notes(&fun_env.get_loc(), &message, trace);
        //     }
        // }

        // // prune the function-to-invariants map with the pragma-magic
        // let fun_to_inv_map =
        //     Self::prune_function_to_invariants_map(env, fun_to_inv_map, &fun_set_with_no_inv_check);

        // // check for unused invariants defined in the target module
        // let all_checked_invariants: BTreeSet<_> = fun_to_inv_map
        //     .values()
        //     .flat_map(|rel| rel.direct_modified.iter())
        //     .cloned()
        //     .collect();
        // for module_env in env.get_modules() {
        //     if !module_env.is_target() {
        //         continue;
        //     }
        //     for inv_id in env.get_global_invariants_by_module(module_env.get_id()) {
        //         if !all_checked_invariants.contains(&inv_id) {
        //             let inv = env.get_global_invariant(inv_id).unwrap();
        //             env.diag(
        //                 Severity::Warning,
        //                 &inv.loc,
        //                 "Global invariant is not checked anywhere in the code",
        //             );
        //         }
        //     }
        // }

        // // save the analysis results in the env
        // let result = InvariantAnalysisData {
        //     fun_set_with_inv_check_on_exit,
        //     fun_set_with_no_inv_check,
        //     fun_to_inv_map,
        // };
        // env.set_extension(result);
    }
}

/// This impl block contains functions on marking a function as verified or inlined
impl VerificationAnalysisProcessor {
    /// Check if a function is essential for the verification pipeline
    pub fn is_essential_function(fun_env: &FunctionEnv) -> bool {
        let name = fun_env.get_full_name_str();
        
        // Handle ghost functions first (since they're also native)
        if name.contains("ghost::") {
            return true; // Keep all ghost functions
        }
        
        // All prover functions are essential
        if name.contains("prover::") {
            return true;
        }
        
        // Essential stdlib functions that are needed for verification
        if name.starts_with("vector::") || 
           name.starts_with("option::") ||
           name.starts_with("object::") {
            return true;
        }
        
        false
    }
    
    /// Check if a function is compiler-generated or fundamental infrastructure
    pub fn is_compiler_generated_function(fun_env: &FunctionEnv) -> bool {
        let name = fun_env.get_full_name_str();
        
        // Compiler-generated functions (prover/ghost)
        if name.contains("prover::") || name.contains("ghost::") {
            return true;
        }
        
        // Fundamental infrastructure functions needed for verification
        if name.starts_with("vector::") || name.starts_with("option::") {
            return true;
        }
        
        false
    }

    /// Check whether the function falls within the verification scope given in the options
    fn is_within_verification_scope(fun_env: &FunctionEnv) -> bool {
        let env = fun_env.module_env.env;
        let options = ProverOptions::get(env);
        match &options.verify_scope {
            VerificationScope::Public => fun_env.is_exposed(),
            VerificationScope::All => true,
            VerificationScope::Only(name) => fun_env.matches_name(name),
            VerificationScope::OnlyModule(name) => fun_env.module_env.matches_name(name),
            VerificationScope::None => false,
        }
    }

    /// Mark that this function should be verified, and as a result, mark that all its callees
    /// should be inlined
    fn mark_verified(
        fun_env: &FunctionEnv,
        data: &mut FunctionData,
        targets: &mut FunctionTargetsHolder,
    ) {
        // TODO(mengxu): re-check the treatment of fixedpoint here
        let info = data
            .annotations
            .get_or_default_mut::<VerificationInfo>(true);
        if !info.verified {
            info.verified = true;
            info.inlined = true;
            Self::mark_callees_inlined(fun_env, targets);
        }
    }

    /// Mark that this function should be inlined because it is called by a function that is marked
    /// as verified, and as a result, mark that all its callees should be inlined as well.
    ///
    /// NOTE: This does not apply to opaque, native, or intrinsic functions.
    fn mark_inlined(fun_env: &FunctionEnv, targets: &mut FunctionTargetsHolder) {
        if fun_env.is_native() {
            return;
        }

        // at this time, we only have the `baseline` variant in the targets
        let variant = FunctionVariant::Baseline;
        if let Some(data) = targets.get_data_mut(&fun_env.get_qualified_id(), &variant) {
            // TODO(mengxu): re-check the treatment of fixedpoint here
            let info = data
                .annotations
                .get_or_default_mut::<VerificationInfo>(true);
            if !info.inlined {
                info.inlined = true;
                Self::mark_callees_inlined(fun_env, targets);
            }
        } else {
            /*fun_env.module_env.env.error(
                &fun_env.get_loc(),
                &format!(
                    "function `{}` is a recursive function \
                       (or part of a mutually recursive function group) \
                       and should be marked as opaque",
                    fun_env.get_full_name_str()
                ),
            );*/
            // tolerate this since we do not support opaque annotations
        }
    }

    /// Marks all callees of this function to be inlined. Forms a mutual recursion with the
    /// `mark_inlined` function above.
    fn mark_callees_inlined(fun_env: &FunctionEnv, targets: &mut FunctionTargetsHolder) {
        for callee in fun_env.get_called_functions() {
            let callee_env = fun_env.module_env.env.get_function(callee);
            if let Some(spec_id) = targets.get_spec_by_fun(&callee) {
                let is_verified = targets.is_verified_spec(spec_id);
                let spec_env = fun_env.module_env.env.get_function(*spec_id);
                Self::mark_inlined(&spec_env, targets);
                if !is_verified {
                    continue;
                }
            }
            Self::mark_inlined(&callee_env, targets);
        }
    }

    // pub fn find_dynamics_in_function(
    //     &self, 
    //     func_env: &FunctionEnv,
    //     data: &FunctionData,
    // ) -> Option<Loc> {
    //     let env = func_env.module_env.env;
    //     let target = FunctionTarget::new(func_env, data);

    //     for cp in target.get_bytecode() {
    //         match cp {
    //             Bytecode::Call(attr, _, operation, _, _) => {
    //                 match operation {
    //                     Operation::Function(mod_id, _, _) => {
    //                         let module_name = env
    //                             .symbol_pool()
    //                             .string(env
    //                                 .get_module(*mod_id)
    //                                 .get_name()
    //                                 .name()
    //                             );

    //                         if ["dynamic_field", "dynamic_object_field"].contains(&module_name.as_str()) {
    //                             return Some(target.get_bytecode_loc(*attr)); 
    //                         }
    //                     },
    //                     _ => {}
    //                 };
    //             },
    //             _ => {},
    //         }
    //     }

    //     None
    // }
}

// /// This impl block contains functions on global invariant applicability analysis
// impl VerificationAnalysisProcessor {
//     /// Build the E set and N set
//     ///
//     /// E set: f in E if declared pragma disable_invariant_in_body for f
//     /// N set: f in N if f is called from a function in E or N
//     ///        can also put f in N by pragma delegate_invariant_to_caller
//     ///
//     /// E set means: a suspendable invariant holds before, after, but NOT during the function body
//     /// N set means: a suspendable invariant doesn't hold at any point in the function
//     fn probe_invariant_status_in_functions(
//         env: &GlobalEnv,
//     ) -> (BTreeSet<QualifiedId<FunId>>, BTreeSet<QualifiedId<FunId>>) {
//         let mut disabled_inv_fun_set = BTreeSet::new(); // the E set
//         let mut non_inv_fun_set = BTreeSet::new(); // the N set

//         // Invariant: if a function is in non_inv_fun_set and not in worklist, then all the
//         // functions it calls are also in non_inv_fun_set or in worklist. As a result, when the
//         // worklist is empty, all callees of a function in non_inv_fun_set will also be in
//         // non_inv_fun_set. Each function is added at most once to the worklist.
//         let mut worklist = vec![];
//         for module_env in env.get_modules() {
//             for fun_env in module_env.get_functions() {
//                 if is_invariant_checking_disabled(&fun_env) {
//                     let fun_id = fun_env.get_qualified_id();
//                     disabled_inv_fun_set.insert(fun_id);
//                     worklist.push(fun_id);
//                 }
//                 if is_invariant_checking_delegated(&fun_env) {
//                     let fun_id = fun_env.get_qualified_id();
//                     // Add to work_list only if fun_id is not in non_inv_fun_set (may have inferred
//                     // this from a caller already).
//                     if non_inv_fun_set.insert(fun_id) {
//                         worklist.push(fun_id);
//                     }
//                 }
//                 // Downward closure of the non_inv_fun_set
//                 while let Some(called_fun_id) = worklist.pop() {
//                     let called_funs = env.get_function(called_fun_id).get_called_functions();
//                     for called_fun_id in called_funs {
//                         if non_inv_fun_set.insert(called_fun_id) {
//                             // Add to work_list only if fun_id is not in fun_set
//                             worklist.push(called_fun_id);
//                         }
//                     }
//                 }
//             }
//         }
//         (disabled_inv_fun_set, non_inv_fun_set)
//     }

//     /// Compute the chain of calls which leads to an implicit non-inv function, i.e., explain why
//     /// a function appears in the N-set.
//     fn compute_non_inv_cause_chain(fun_env: &FunctionEnv<'_>) -> Vec<String> {
//         let global_env = fun_env.module_env.env;
//         let mut worklist: BTreeSet<Vec<QualifiedId<FunId>>> = fun_env
//             .get_calling_functions()
//             .into_iter()
//             .map(|id| vec![id])
//             .collect();
//         let mut done = BTreeSet::new();
//         let mut result = vec![];
//         while let Some(caller_list) = worklist.iter().next().cloned() {
//             worklist.remove(&caller_list);
//             let caller_id = *caller_list.iter().last().unwrap();
//             done.insert(caller_id);
//             let caller_env = global_env.get_function_qid(caller_id);
//             let display_chain = || {
//                 vec![fun_env.get_qualified_id()]
//                     .into_iter()
//                     .chain(caller_list.iter().cloned())
//                     .map(|id| global_env.get_function_qid(id).get_full_name_str())
//                     .join(" <- ")
//             };
//             if is_invariant_checking_disabled(&caller_env) {
//                 result.push(format!("disabled by {}", display_chain()));
//             } else if is_invariant_checking_delegated(&caller_env) {
//                 result.push(format!("delegated by {}", display_chain()));
//             } else {
//                 worklist.extend(
//                     caller_env
//                         .get_calling_functions()
//                         .into_iter()
//                         .filter_map(|id| {
//                             if done.contains(&id) {
//                                 None
//                             } else {
//                                 let mut new_caller_list = caller_list.clone();
//                                 new_caller_list.push(id);
//                                 Some(new_caller_list)
//                             }
//                         }),
//                 );
//             }
//         }
//         if result.is_empty() {
//             result.push("cannot determine disabling reason (bug?)".to_owned())
//         }
//         result
//     }

//     /// Produce a `Map[fun_id -> InvariantRelevance]` ignoring the relevant pragmas on both
//     /// function-side (i.e., `disable_invariants_in_body` and `delegate_invariants_to_caller`) and
//     /// invariant-side (i.e., `suspendable`)
//     fn build_function_to_invariants_map(
//         env: &GlobalEnv,
//         targets: &FunctionTargetsHolder,
//     ) -> BTreeMap<QualifiedId<FunId>, InvariantRelevance> {
//         // collect all global invariants
//         let mut global_invariants = vec![];
//         for menv in env.get_modules() {
//             for inv_id in env.get_global_invariants_by_module(menv.get_id()) {
//                 global_invariants.push(env.get_global_invariant(inv_id).unwrap());
//             }
//         }

//         // go over each function target and check global invariant applicability
//         let mut invariant_relevance = BTreeMap::new();
//         for (fun_id, fun_variant) in targets.get_funs_and_variants() {
//             debug_assert!(matches!(fun_variant, FunctionVariant::Baseline));
//             let fenv = env.get_function(fun_id);
//             let target = targets.get_target(&fenv, &fun_variant);
//             let related =
//                 Self::find_relevant_invariants(&target, global_invariants.clone().into_iter());
//             invariant_relevance.insert(fun_id, related);
//         }

//         // return the collected relevance map
//         invariant_relevance
//     }

//     /// From the iterator of global invariants, find the ones that are relevant to the function as
//     /// well as how/why the invariant is relevant.
//     fn find_relevant_invariants<'a>(
//         target: &FunctionTarget,
//         invariants: impl Iterator<Item = &'a GlobalInvariant>,
//     ) -> InvariantRelevance {
//         let mem_usage = usage_analysis::get_memory_usage(target);
//         let mem_accessed = &mem_usage.accessed.all;
//         let mem_modified = &mem_usage.modified.all;
//         let mem_direct_accessed = &mem_usage.accessed.direct;
//         let mem_direct_modified = &mem_usage.modified.direct;

//         let mut inv_accessed = BTreeSet::new();
//         let mut inv_modified = BTreeSet::new();
//         let mut inv_direct_accessed = BTreeSet::new();
//         let mut inv_direct_modified = BTreeSet::new();
//         for inv in invariants {
//             for fun_mem in mem_accessed.iter() {
//                 for inv_mem in &inv.mem_usage {
//                     if inv_mem.module_id != fun_mem.module_id || inv_mem.id != fun_mem.id {
//                         continue;
//                     }
//                     let adapter =
//                         TypeUnificationAdapter::new_vec(&fun_mem.inst, &inv_mem.inst, true, true);
//                     let rel = adapter.unify(Variance::Allow, /* shallow_subst */ false);
//                     if rel.is_some() {
//                         inv_accessed.insert(inv.id);

//                         // the rest exploits the fact that the `used_memory` set (a read-write set)
//                         // is always a superset of the others.
//                         if mem_modified.contains(fun_mem) {
//                             inv_modified.insert(inv.id);
//                         }
//                         if mem_direct_accessed.contains(fun_mem) {
//                             inv_direct_accessed.insert(inv.id);
//                         }
//                         if mem_direct_modified.contains(fun_mem) {
//                             inv_direct_modified.insert(inv.id);
//                         }
//                     }
//                 }
//             }
//         }
//         InvariantRelevance {
//             accessed: inv_accessed,
//             modified: inv_modified,
//             direct_accessed: inv_direct_accessed,
//             direct_modified: inv_direct_modified,
//         }
//     }

//     /// Prune the `Map[fun_id -> InvariantRelevance]` returned by `build_function_to_invariants_map`
//     /// after considering the invariant-related pragmas.
//     fn prune_function_to_invariants_map(
//         env: &GlobalEnv,
//         original: BTreeMap<QualifiedId<FunId>, InvariantRelevance>,
//         fun_set_with_no_inv_check: &BTreeSet<QualifiedId<FunId>>,
//     ) -> BTreeMap<QualifiedId<FunId>, InvariantRelevance> {
//         // NOTE: All fields in `