use std::io::{BufRead, Error, ErrorKind, Result};
use std::process::{Command, Output, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

pub fn run(args: &[String]) -> Result<Output> {
    Command::new(&args[0]).args(&args[1..]).output()
}

pub fn run_with_line_callback<F: FnMut(&str)>(args: &[String], mut on_line: F) -> Result<Output> {
    let mut child = Command::new(&args[0])
        .args(&args[1..])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let stdout = child.stdout.take().unwrap();
    let mut stdout_bytes = Vec::new();
    let reader = std::io::BufReader::new(stdout);
    for line in reader.lines() {
        let line = line?;
        on_line(&line);
        stdout_bytes.extend_from_slice(line.as_bytes());
        stdout_bytes.push(b'\n');
    }

    let status = child.wait()?;

    use std::io::Read;
    let mut stderr_bytes = Vec::new();
    if let Some(mut stderr) = child.stderr.take() {
        stderr.read_to_end(&mut stderr_bytes)?;
    }

    Ok(Output {
        status,
        stdout: stdout_bytes,
        stderr: stderr_bytes,
    })
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

#[cfg(unix)]
pub fn run_with_timeout_and_line_callback<F: FnMut(&str) + Send>(
    args: &[String],
    timeout: Duration,
    mut on_line: F,
) -> Result<Output> {
    use nix::sys::signal::{self, Signal};
    use nix::unistd::Pid;
    use std::os::unix::process::CommandExt;
    use std::time::Instant;

    let mut child = Command::new(&args[0])
        .args(&args[1..])
        .process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let pid = child.id() as i32;

    let stdout = child.stdout.take().unwrap();
    let (tx, rx) = std::sync::mpsc::channel::<String>();

    let reader_thread = std::thread::spawn(move || {
        let reader = std::io::BufReader::new(stdout);
        let mut all_bytes = Vec::new();
        for line in reader.lines() {
            match line {
                Ok(line) => {
                    all_bytes.extend_from_slice(line.as_bytes());
                    all_bytes.push(b'\n');
                    if tx.send(line).is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
        all_bytes
    });

    let start = Instant::now();
    loop {
        // Drain any available lines
        while let Ok(line) = rx.try_recv() {
            on_line(&line);
        }

        let elapsed = start.elapsed();
        if elapsed >= timeout {
            let _ = signal::killpg(Pid::from_raw(pid), Signal::SIGKILL);
            let _ = reader_thread.join();
            return Err(Error::new(ErrorKind::TimedOut, "Process timed out"));
        }

        let remaining = timeout - elapsed;
        let poll = remaining.min(Duration::from_millis(100));

        match child.wait_timeout(poll)? {
            Some(status) => {
                // Process finished. Drain remaining lines.
                for line in rx.try_iter() {
                    on_line(&line);
                }

                let stdout_bytes = reader_thread.join().unwrap_or_default();

                use std::io::Read;
                let mut stderr_bytes = Vec::new();
                if let Some(mut stderr) = child.stderr.take() {
                    stderr.read_to_end(&mut stderr_bytes)?;
                }

                return Ok(Output {
                    status,
                    stdout: stdout_bytes,
                    stderr: stderr_bytes,
                });
            }
            None => {}
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

#[cfg(windows)]
pub fn run_with_timeout_and_line_callback<F: FnMut(&str) + Send>(
    args: &[String],
    timeout: Duration,
    mut on_line: F,
) -> Result<Output> {
    use std::os::windows::process::CommandExt;
    use std::time::Instant;

    const CREATE_NEW_PROCESS_GROUP: u32 = 0x00000200;

    let mut child = Command::new(&args[0])
        .args(&args[1..])
        .creation_flags(CREATE_NEW_PROCESS_GROUP)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let pid = child.id();

    let stdout = child.stdout.take().unwrap();
    let (tx, rx) = std::sync::mpsc::channel::<String>();

    let reader_thread = std::thread::spawn(move || {
        let reader = std::io::BufReader::new(stdout);
        let mut all_bytes = Vec::new();
        for line in reader.lines() {
            match line {
                Ok(line) => {
                    all_bytes.extend_from_slice(line.as_bytes());
                    all_bytes.push(b'\n');
                    if tx.send(line).is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
        all_bytes
    });

    let start = Instant::now();
    loop {
        while let Ok(line) = rx.try_recv() {
            on_line(&line);
        }

        let elapsed = start.elapsed();
        if elapsed >= timeout {
            let _ = Command::new("taskkill")
                .args(&["/F", "/T", "/PID", &pid.to_string()])
                .output();
            let _ = reader_thread.join();
            return Err(Error::new(ErrorKind::TimedOut, "Process timed out"));
        }

        let remaining = timeout - elapsed;
        let poll = remaining.min(Duration::from_millis(100));

        match child.wait_timeout(poll)? {
            Some(status) => {
                for line in rx.try_iter() {
                    on_line(&line);
                }

                let stdout_bytes = reader_thread.join().unwrap_or_default();

                use std::io::Read;
                let mut stderr_bytes = Vec::new();
                if let Some(mut stderr) = child.stderr.take() {
                    stderr.read_to_end(&mut stderr_bytes)?;
                }

                return Ok(Output {
                    status,
                    stdout: stdout_bytes,
                    stderr: stderr_bytes,
                });
            }
            None => {}
        }
    }
}
