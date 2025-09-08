pub mod lean_wrapper;
pub mod options;
pub mod prover_task_runner;
pub mod bytecode_translator;
pub mod spec_translator;
pub mod lean_helpers;

#[macro_export]
macro_rules! wip {
    ($name:expr) => {
        println!("WIP: {}", $name);
    }
}