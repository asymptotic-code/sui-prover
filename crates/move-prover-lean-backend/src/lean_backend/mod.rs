pub mod bytecode_translator;
pub mod lean_helpers;
pub mod lean_wrapper;
pub mod options;
pub mod prover_task_runner;
pub mod spec_translator;

#[macro_export]
macro_rules! wip {
    ($name:expr) => {
        println!("WIP: {}", $name)
    };
}
