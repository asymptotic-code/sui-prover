// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

use move_model::model::FunctionEnv;

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
};

pub struct SSATransformProcessor {
    debug: bool,
}

impl SSATransformProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self { debug: false })
    }

    pub fn new_with_debug() -> Box<Self> {
        Box::new(Self { debug: true })
    }
}

impl FunctionTargetProcessor for SSATransformProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        if self.debug {
            println!(
                "Processing function {} for SSA transformation",
                func_env.get_full_name_str()
            );
        }

        if self.debug {
            println!(
                "SSA transformation completed for {}",
                func_env.get_full_name_str()
            );
        }

        data
    }

    fn name(&self) -> String {
        "ssa_transform".to_owned()
    }
}
