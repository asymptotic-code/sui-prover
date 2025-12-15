use std::{collections::BTreeSet, rc::Rc};

use move_model::{
    model::{FunId, FunctionEnv, GlobalEnv, QualifiedId},
    ty::Type,
};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation, QuantifierHelperType},
};

#[derive(Debug, Clone, Ord, Eq, PartialEq, PartialOrd)]
pub struct PureQuantifierHelperInfo {
    pub qht: QuantifierHelperType,
    pub function: QualifiedId<FunId>,
    pub li: usize,
    pub inst: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct PureQuantifierHelpersInfo {
    pub helpers: BTreeSet<PureQuantifierHelperInfo>,
}

pub struct PureQuantifierHelpersAnalysisProcessor();

impl PureQuantifierHelpersAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for PureQuantifierHelpersAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }
        let env = func_env.module_env.env;
        if !targets.is_pure_fun(&func_env.get_qualified_id()) {
            return data;
        }

        let mut info = if let Some(info) = env.get_extension::<PureQuantifierHelpersInfo>() {
            info.as_ref().clone()
        } else {
            PureQuantifierHelpersInfo {
                helpers: BTreeSet::new(),
            }
        };

        for bc in &data.code {
            if let Bytecode::Call(_, dests, Operation::Quantifier(qt, qid, inst, li), srcs, _) = bc
            {
                if let Some(qht) = qt.into_quantifier_helper_type() {
                    info.helpers.insert(PureQuantifierHelperInfo {
                        qht,
                        function: *qid,
                        li: *li,
                        inst: inst.to_vec(),
                    });
                }
            }
        }

        env.set_extension(info);
        data
    }

    fn name(&self) -> String {
        "pure_quantifier_helpers_analysis".to_string()
    }
}

pub fn get_info(env: &GlobalEnv) -> Rc<PureQuantifierHelpersInfo> {
    env.get_extension::<PureQuantifierHelpersInfo>().unwrap()
}
