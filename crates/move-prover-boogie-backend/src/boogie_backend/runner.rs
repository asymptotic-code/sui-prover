use std::io::{Error, ErrorKind, Result};
use std::process::{Command, Output, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

pub fn run(args: &[String]) -> Result<Output> {
    Command::new(&args[0]).args(&args[1..]).output()
}

#[cfg(unix)]
pub fn run_with_timeout(args: &[String], timeout: Duration) -> Result<Output> {
    use nix::sys::signal::{self, Signal};
    use nix::unistd::Pid;
    use std::os::unix::process::CommandExt;

    let mut child = Command::new(&args[0])
        .args(&args[1..])
        .process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let pid = child.id() as i32;

    match child.wait_timeout(timeout)? {
        Some(status) => {
            let stdout = child.stdout.take().unwrap();
            let stderr = child.stderr.take().unwrap();

            use std::io::Read;
            let mut stdout_bytes = Vec::new();
            let mut stderr_bytes = Vec::new();
            std::io::BufReader::new(stdout).read_to_end(&mut stdout_bytes)?;
            std::io::BufReader::new(stderr).read_to_end(&mut stderr_bytes)?;

            Ok(Output {
                status,
                stdout: stdout_bytes,
                stderr: stderr_bytes,
            })
        }
        None => {
            let _ = signal::killpg(Pid::from_raw(pid), Signal::SIGKILL);
            Err(Error::new(ErrorKind::TimedOut, "Process timed out"))
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

    match child.wait_timeout(timeout)? {
        Some(status) => {
            let stdout = child.stdout.take().unwrap();
            let stderr = child.stderr.take().unwrap();

            use std::io::Read;
            let mut stdout_bytes = Vec::new();
            let mut stderr_bytes = Vec::new();
            std::io::BufReader::new(stdout).read_to_end(&mut stdout_bytes)?;
            std::io::BufReader::new(stderr).read_to_end(&mut stderr_bytes)?;

            Ok(Output {
                status,
                stdout: stdout_bytes,
                stderr: stderr_bytes,
            })
        }
        None => {
            let _ = Command::new("taskkill")
                .args(&["/F", "/T", "/PID", &pid.to_string()])
                .output();
            Err(Error::new(ErrorKind::TimedOut, "Process timed out"))
        }
    }
}
