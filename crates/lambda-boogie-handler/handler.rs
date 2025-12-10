use anyhow::{Context, Result};
use libc::{killpg, SIGKILL};
use redis::{AsyncCommands, RedisError};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::io::{BufReader, Read};
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};

#[derive(Serialize, Debug)]
pub struct ProverResponse {
    pub out: String,
    pub err: String,
    pub status: i32,
    pub cached: bool,
}

const DEFAULT_BOOGIE_FLAGS: &[&str] = &[
    "-inferModifies",
    "-printVerifiedProceduresCount:0",
    "-printModel:1",
    "-enhancedErrorMessages:1",
    "-useArrayAxioms",
    "-proverOpt:O:smt.QI.EAGER_THRESHOLD=10",
    "-proverOpt:O:smt.QI.LAZY_THRESHOLD=100",
    "-proverOpt:O:model_validate=true",
    "-vcsCores:4",
    "-verifySeparately",
    "-vcsMaxKeepGoingSplits:2",
    "-vcsSplitOnEveryAssert",
    "-vcsFinalAssertTimeout:600",
];

pub struct ProverHandler {
    redis_client: Option<redis::Client>,
    cache_lifetime_seconds: u64,
}

impl ProverHandler {
    pub fn new() -> Result<Self> {
        let cache_lifetime_seconds = std::env::var("CACHE_LIFETIME_SECONDS")
            .unwrap_or_else(|_| "172800".to_string())
            .parse::<u64>()
            .context("Invalid CACHE_LIFETIME_SECONDS value")?;

        if std::env::var("REDIS_HOST").is_err() {
            return Ok(Self {
                redis_client: None,
                cache_lifetime_seconds,
            });
        }

        let redis_host =
            std::env::var("REDIS_HOST").context("REDIS_HOST environment variable not set")?;
        let redis_port = std::env::var("REDIS_PORT")
            .unwrap_or_else(|_| "6379".to_string())
            .parse::<u16>()
            .context("Invalid REDIS_PORT value")?;

        let info = redis::ConnectionInfo {
            addr: redis::ConnectionAddr::TcpTls {
                host: redis_host,
                port: redis_port,
                insecure: true,
                tls_params: None,
            },
            redis: redis::RedisConnectionInfo::default(),
        };

        let redis_client =
            Some(redis::Client::open(info).context("Failed to create Redis client")?);

        Ok(Self {
            redis_client,
            cache_lifetime_seconds,
        })
    }

    pub fn generate_hash(file_text: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(file_text.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    async fn check_cache(&self, hash: &str) -> Result<Option<(String, String, i32)>> {
        if let Some(redis_client) = &self.redis_client {
            let mut conn = redis_client
                .get_multiplexed_async_connection()
                .await
                .context("Failed to get Redis connection")?;

            let result: Option<String> = conn.get(hash).await?;
            let deserialized: Option<(String, String, i32)> = match result {
                Some(data) => serde_json::from_str(&data).ok(),
                None => None,
            };

            Ok(deserialized)
        } else {
            Ok(None)
        }
    }

    async fn cache_result(&self, hash: &str, out: &str, err: &str, status: i32) -> Result<()> {
        if let Some(redis_client) = &self.redis_client {
            let mut conn = redis_client
                .get_multiplexed_async_connection()
                .await
                .context("Failed to get Redis connection")?;

            let serialized = serde_json::to_string(&(out, err, status))?;
            let result: Result<(), RedisError> = conn
                .set_ex(hash, serialized, self.cache_lifetime_seconds)
                .await;
            result?;
        }

        Ok(())
    }

    fn get_option_key(option: &str) -> &str {
        if let Some(eq_pos) = option.find('=') {
            &option[..eq_pos]
        } else if let Some(colon_pos) = option.rfind(':') {
            let after_colon = &option[colon_pos + 1..];
            if after_colon.chars().next().map_or(false, |c| {
                c.is_ascii_digit() || after_colon.starts_with('/') || after_colon.starts_with('.')
            }) {
                &option[..colon_pos]
            } else {
                option
            }
        } else {
            option
        }
    }

    fn get_boogie_command(
        &self,
        boogie_file_name: &str,
        individual_options: Option<String>,
    ) -> Result<Vec<String>> {
        let boogie_exe =
            std::env::var("BOOGIE_EXE").context("BOOGIE_EXE environment variable not set")?;
        let z3_exe = std::env::var("Z3_EXE").context("Z3_EXE environment variable not set")?;

        let mut result = vec![boogie_exe];
        result.extend(DEFAULT_BOOGIE_FLAGS.iter().map(|s| s.to_string()));

        if let Some(options) = individual_options {
            for option in options.split_whitespace().map(|s| format!("-{}", s)) {
                let key = Self::get_option_key(&option);
                result.retain(|existing: &String| Self::get_option_key(existing) != key);
                result.push(option);
            }
        }

        result.push(format!("-proverOpt:PROVER_PATH={z3_exe}"));
        result.push(boogie_file_name.to_string());

        Ok(result)
    }

    async fn execute_boogie(
        &self,
        temp_file_path: &str,
        individual_options: Option<String>,
    ) -> Result<(String, String, i32)> {
        let args = self.get_boogie_command(temp_file_path, individual_options)?;

        let mut child = unsafe {
            Command::new(&args[0])
                .args(&args[1..])
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .pre_exec(|| {
                    libc::setsid();
                    Ok(())
                })
                .spawn()
                .context("Failed to spawn command")
        }?;

        let pid = child.id() as i32;
        println!("Spawned process with PID {}", pid);

        // Capture stdout/stderr in separate threads
        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();

        let mut stdout_reader = BufReader::new(stdout);
        let mut stderr_reader = BufReader::new(stderr);

        let mut stdout_buf = String::new();
        let mut stderr_buf = String::new();

        // Read stdout and stderr
        let status = child.wait().context("Failed to wait for child")?;

        stdout_reader.read_to_string(&mut stdout_buf).ok();
        stderr_reader.read_to_string(&mut stderr_buf).ok();

        println!("Captured stdout:\n{}", stdout_buf);
        println!("Captured stderr:\n{}", stderr_buf);
        println!("Process exited with: {}", status);

        // Kill the whole process group
        println!("Killing process group...");
        unsafe {
            let result = killpg(pid, SIGKILL);
            if result != 0 {
                println!("Failed to kill process group {}", result);
            }
        }

        Ok((stdout_buf, stderr_buf, status.code().unwrap_or(-1)))
    }

    pub async fn process(
        &self,
        file_text: String,
        boogie_options: Option<String>,
    ) -> Result<ProverResponse> {
        let hash = Self::generate_hash(&file_text);

        if let Some((out, err, status)) = self.check_cache(&hash).await? {
            return Ok(ProverResponse {
                out,
                err,
                status,
                cached: true,
            });
        }

        let mut temp_file = tempfile::Builder::new()
            .suffix(".bpl")
            .tempfile()
            .context("Failed to create temporary file")?;

        use std::io::Write;
        temp_file
            .write_all(file_text.as_bytes())
            .context("Failed to write to temporary file")?;

        let temp_file_path = temp_file.path().to_string_lossy().to_string();

        let (out, err, status) = match self.execute_boogie(&temp_file_path, boogie_options).await {
            Ok(output) => output,
            Err(e) => (
                String::new(),
                format!("Error executing boogie remotely: {}", e),
                -1,
            ),
        };

        if let Err(e) = self.cache_result(&hash, &out, &err, status).await {
            println!("Failed to cache result: {}", e);
        } else {
            println!("Result cached successfully for hash: {}", hash);
        }

        temp_file.close()?;

        Ok(ProverResponse {
            out,
            err,
            status: status,
            cached: false,
        })
    }
}
