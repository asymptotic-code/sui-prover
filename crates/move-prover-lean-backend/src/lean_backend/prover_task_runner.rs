// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! Prover task runner that runs multiple instances of the prover task and returns
//! as soon as the fastest instance finishes.

/// This file is nearly identical to Boogie's prover_task_runner.rs, with minor var name changes.
///
use async_trait::async_trait;
use futures::{future::FutureExt, pin_mut, select};
use log::debug;
use rand::Rng;
use regex::Regex;
use std::{
    process::Output,
    sync::Arc,
    time::Duration,
};
use tokio::{
    process::Command,
    sync::{broadcast, broadcast::Receiver, mpsc, Semaphore},
};
use crate::lean_backend::options::LeanOptions;

#[derive(Debug, Clone)]
enum BroadcastMsg {
    Stop,
}

const MAX_PERMITS: usize = usize::MAX >> 4;

#[async_trait]
pub trait ProverTask {
    type TaskResult: Send + 'static;
    type TaskId: Send + Copy + 'static;

    /// Initialize the task runner given the number of instances.
    fn init(&mut self, num_instances: usize) -> Vec<Self::TaskId>;

    /// Run the task with task_id. This function will be called from one of the worker threads.
    async fn run(&mut self, task_id: Self::TaskId, sem: Arc<Semaphore>) -> Self::TaskResult;

    /// Returns whether the task result is considered successful.
    fn is_success(&self, task_result: &Self::TaskResult) -> bool;

    /// Returns a task result used for representing a hard timeout
    fn make_timeout(&self) -> (Self::TaskId, Self::TaskResult);
}

pub struct ProverTaskRunner();

impl ProverTaskRunner {
    /// Run `num_instances` instances of the prover `task` and returns the task id
    /// as well as the result of the fastest running instance.
    pub async fn run_tasks<T>(
        mut task: T,
        num_instances: usize,
        sequential: bool,
        hard_timeout_secs: u64,
    ) -> (T::TaskId, T::TaskResult)
    where
        T: ProverTask + Clone + Send + 'static,
    {
        let sem = if sequential {
            Arc::new(Semaphore::new(1))
        } else {
            Arc::new(Semaphore::new(MAX_PERMITS))
        };
        // Create channels for communication - using tokio async channels
        let (worker_tx, mut master_rx) = mpsc::unbounded_channel();
        let (master_tx, _): (
            tokio::sync::broadcast::Sender<BroadcastMsg>,
            Receiver<BroadcastMsg>,
        ) = broadcast::channel(num_instances);

        // Initialize the prover tasks.
        let task_ids = task.init(num_instances);
        for task_id in task_ids {
            let s = sem.clone();
            let send_n = worker_tx.clone();
            let worker_rx = master_tx.subscribe();
            let cloned_task = task.clone();
            // Spawn a task worker for each task_id.
            tokio::spawn(async move {
                Self::run_task_until_cancelled(cloned_task, task_id, send_n, worker_rx, s).await;
            });
        }
        let mut num_working_instances = num_instances;
        // Listens until one of the workers finishes.
        loop {
            // Result received from one worker.
            let timeout = Duration::from_secs(if hard_timeout_secs > 0 {
                hard_timeout_secs
            } else {
                u64::MAX
            });

            // Use tokio's async recv with timeout
            let res = tokio::time::timeout(timeout, master_rx.recv()).await;

            match res {
                Ok(Some((task_id, result))) => {
                    if num_working_instances == 1 {
                        return (task_id, result);
                    } else if task.is_success(&result) {
                        // Result is successful. Broadcast to other workers
                        // so they can stop working.
                        let _ = master_tx.send(BroadcastMsg::Stop);
                        return (task_id, result);
                    }
                    debug!("previous instance failed, waiting for another worker to report...");
                    num_working_instances = usize::saturating_sub(num_working_instances, 1);
                }
                Ok(None) => {
                    // Channel closed without result
                    debug!("worker channel closed unexpectedly");
                }
                Err(_) => {
                    // Timeout occurred
                    let _ = master_tx.send(BroadcastMsg::Stop);
                    debug!(
                        "prover task exceeded hard timeout of {}s",
                        hard_timeout_secs
                    );
                    return task.make_timeout();
                }
            }
        }
    }

    // Run two async tasks, listening on broadcast channel and running the task, until
    // either the task finishes running, or a stop message is received.
    async fn run_task_until_cancelled<T>(
        mut task: T,
        task_id: T::TaskId,
        tx: mpsc::UnboundedSender<(T::TaskId, T::TaskResult)>,
        rx: Receiver<BroadcastMsg>,
        sem: Arc<Semaphore>,
    ) where
        T: ProverTask,
    {
        let task_fut = task.run(task_id, sem).fuse();
        let watchdog_fut = Self::watchdog(rx).fuse();
        pin_mut!(task_fut, watchdog_fut);
        select! {
            _ = watchdog_fut => {
                // A stop message is received.
            }
            res = task_fut => {
                // Task finishes running, send the result to parent thread.
                let _ = tx.send((task_id, res));
            },
        }
    }

    /// Waits for a stop message from the parent thread.
    async fn watchdog(mut rx: Receiver<BroadcastMsg>) {
        let _ = rx.recv().await;
    }
}

#[derive(Debug, Clone)]
pub struct RunLeanWithSeeds {
    pub options: LeanOptions,
    pub lean_file: String,
}

impl RunLeanWithSeeds {
    pub fn run_sync(&mut self, _seed: usize) -> std::io::Result<Output> {
        let args = self
            .get_lean_command(0)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::Other, err))?;
        debug!("running Lean command with seed {}", 0);
        std::process::Command::new(&args[0])
            .args(&args[1..])
            .output()
    }
}

#[async_trait]
impl ProverTask for RunLeanWithSeeds {
    type TaskResult = std::io::Result<Output>;
    type TaskId = usize;

    fn init(&mut self, num_instances: usize) -> Vec<Self::TaskId> {
        // If we are running only one Lean instance, use the default random seed.
        if num_instances == 1 {
            return vec![self.options.random_seed];
        }
        let mut rng = rand::thread_rng();
        // Otherwise generate a list of random numbers to use as seeds.
        (0..num_instances)
            .map(|_| rng.gen::<u8>() as usize)
            .collect()
    }

    async fn run(&mut self, task_id: Self::TaskId, sem: Arc<Semaphore>) -> Self::TaskResult {
        let _guard = sem.acquire().await;
        let args = self
            .get_lean_command(task_id)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::Other, err))?;
        debug!("running Lean command with seed {}", task_id);
        Command::new(&args[0])
            .args(&args[1..])
            .kill_on_drop(true)
            .output()
            .await
    }

    fn is_success(&self, task_result: &Self::TaskResult) -> bool {
        match task_result {
            Ok(res) => {
                if !res.status.success() {
                    return false;
                }
                let output = String::from_utf8_lossy(&res.stdout);
                self.contains_compilation_error(&output) || !self.contains_timeout(&output)
            }
            Err(_) => true, // Count this as success so we terminate everything else
        }
    }

    fn make_timeout(&self) -> (Self::TaskId, Self::TaskResult) {
        (0, Err(std::io::Error::from(std::io::ErrorKind::TimedOut)))
    }
}

impl RunLeanWithSeeds {
    /// Returns command line to call lean.
    pub fn get_lean_command(&mut self, seed: usize) -> anyhow::Result<Vec<String>> {
        self.options
            .lean_flags
            .push(format!("--random-seed={}", seed));
        self.options.get_lean_command(&self.lean_file)
    }

    /// Returns whether the output string contains any Lean compilation errors.
    fn contains_compilation_error(&self, output: &str) -> bool {
        let regex =
            Regex::new(r"(?m)^.*\((?P<line>\d+),(?P<col>\d+)\).*(Error:|error:).*$").unwrap();
        regex.is_match(output)
    }

    /// Returns whether the output string contains any Lean timeouts/inconclusiveness.
    fn contains_timeout(&self, output: &str) -> bool {
        let regex =
            Regex::new(r"(?m)^.*\((?P<line>\d+),(?P<col>\d+)\).*Verification.*(inconclusive|out of resource|timed out).*$")
                .unwrap();
        regex.is_match(output)
    }
}
