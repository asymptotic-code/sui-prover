use std::io::Result;
use std::process::{Command, Output, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

pub fn run(args: &[String]) -> Result<Output> {
    Command::new(&args[0]).args(&args[1..]).output()
}

#[cfg(unix)]
pub fn run_with_timeout(args: &[String], timeout: Duration) -> Result<Output> {
    use nix::sys::signal::{self, Signal};
    use nix::unistd::Pid;
    use std::os::unix::process::CommandExt;

    let child = Command::new(&args[0])
        .args(&args[1..])
        .process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let pid = child.id() as i32;

    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let result = child.wait_with_output();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result,
        Err(_) => {
            // Timeout reached - kill entire process group
            let _ = signal::killpg(Pid::from_raw(pid), Signal::SIGKILL);
            Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "Process timed out",
            ))
        }
    }
}

#[cfg(windows)]
pub fn run_with_timeout(args: &[String], timeout: Duration) -> Result<Output> {
    use std::os::windows::process::CommandExt;

    const CREATE_NEW_PROCESS_GROUP: u32 = 0x00000200;

    let mut child = Command::new(&args[0])
        .args(&args[1..])
        .creation_flags(CREATE_NEW_PROCESS_GROUP)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let pid = child.id();

    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let result = child.wait_with_output();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result,
        Err(_) => {
            // Timeout reached - kill process tree
            let _ = Command::new("taskkill")
                .args(&["/F", "/T", "/PID", &pid.to_string()])
                .output();
            Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "Process timed out",
            ))
        }
    }
}
