use anyhow::{Context, Result};
use libc::{killpg, SIGKILL};
use redis::{AsyncCommands, RedisError};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::io::{BufReader, Read};
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Stdio};

#[derive(Serialize, Debug)]
pub struct ProverResponse {
    pub out: String,
    pub err: String,
    pub status: i32,
    pub cached: bool,
}

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

    pub fn generate_hash(files: &[(String, String)], prover_options: Option<String>) -> String {
        let mut hasher = Sha256::new();
        for (file_path, file_content) in files {
            hasher.update(file_path.as_bytes());
            hasher.update(file_content.as_bytes());
        }
        if let Some(options) = prover_options {
            hasher.update(options.as_bytes());
        }
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

    async fn execute_prover(
        &self,
        temp_dir_path: &Path,
        options: Option<String>,
    ) -> Result<(String, String, i32)> {
        // Create sui_prover.toml from environment variable if provided
        if let Ok(secret) = std::env::var("SUI_PROVER_SECRET") {
            let config_dir = Path::new("/tmp/.asymptotic");
            std::fs::create_dir_all(config_dir).context("Failed to create config directory")?;

            let config_path = config_dir.join("sui_prover.toml");
            std::fs::write(&config_path, secret).context("Failed to write sui_prover.toml")?;

            println!("Created config file at {:?}", config_path);
        }

        let mut child = unsafe {
            let mut c = Command::new("sui-prover");
            if let Some(opts) = options {
                let args: Vec<&str> = opts.split_whitespace().collect();
                c.args(&args);
            };

            c.arg("--cloud")
                .arg("--skip-fetch-latest-git-deps")
                .env("HOME", "/tmp")
                .env("MOVE_HOME", "/opt/.move")
                .current_dir(temp_dir_path)
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

        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();

        let mut stdout_reader = BufReader::new(stdout);
        let mut stderr_reader = BufReader::new(stderr);

        let mut stdout_buf = String::new();
        let mut stderr_buf = String::new();

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

    fn parse_module_header(content: &str) -> (&str, &str) {
        let mut default_address = "0x0";
        let mut default_alias = "specs";

        for line in content.lines() {
            let line = line.trim();
            if line.starts_with("//") || line.is_empty() {
                continue;
            }

            if let Some(module_start) = line.find("module ") {
                let after_module = &line[module_start + 7..].trim();

                if let Some(double_colon_pos) = after_module.find("::") {
                    let address_part = after_module[..double_colon_pos].trim();
                    let rest = &after_module[double_colon_pos + 2..];

                    let module_name = rest
                        .split(|c: char| c == '{' || c == ';' || c.is_whitespace())
                        .next()
                        .unwrap_or("")
                        .trim();

                    if !module_name.is_empty() {
                        if address_part.starts_with("0x") {
                            default_address = address_part;
                        } else {
                            default_alias = address_part;
                        }
                        break;
                    }
                }
            }
        }

        (default_address, default_alias)
    }

    fn build_files(files: Vec<(String, String)>) -> Result<tempfile::TempDir> {
        use std::io::Write;

        for (file_path, _) in &files {
            let path = Path::new(file_path);
            if path.is_absolute() {
                anyhow::bail!("Absolute paths are not allowed: {}", file_path);
            }

            if file_path.contains("..") {
                anyhow::bail!("Directory traversal is not allowed: {}", file_path);
            }

            let is_move_toml = file_path == "Move.toml";
            let is_move_file = file_path.ends_with(".move");

            if !is_move_toml && !is_move_file {
                anyhow::bail!("Only Move.toml and .move files are allowed: {}", file_path);
            }
        }

        let temp_dir = tempfile::tempdir().context("Failed to create temporary directory")?;

        let has_move_toml = files
            .iter()
            .any(|(path, _)| path.ends_with("Move.toml") || path == "Move.toml");

        for (file_path, content) in &files {
            let normalized_path = if file_path.starts_with("sources/")
                || file_path.starts_with("sources\\")
                || file_path.ends_with(".toml")
            {
                file_path.clone()
            } else {
                format!("sources/{}", file_path.trim_start_matches('/'))
            };

            let full_path = temp_dir.path().join(&normalized_path);

            if let Some(parent) = full_path.parent() {
                std::fs::create_dir_all(parent).context(format!(
                    "Failed to create parent directories for {}",
                    normalized_path
                ))?;
            }

            let mut file = std::fs::File::create(&full_path)
                .context(format!("Failed to create file {}", normalized_path))?;
            file.write_all(content.as_bytes())
                .context(format!("Failed to write to file {}", normalized_path))?;
        }

        if !has_move_toml {
            let move_toml_path = temp_dir.path().join("Move.toml");

            let (address, alias) = files
                .iter()
                .find(|(path, _)| path.ends_with(".move"))
                .map(|(_, content)| Self::parse_module_header(content))
                .expect("No .move file found");

            let default_move_toml = format!(
                r#"[package]
                name = "{}"
                edition = "2024.beta"

                [addresses]
                {} = "{}"
                "#,
                alias, alias, address,
            );

            let mut file = std::fs::File::create(&move_toml_path)
                .context("Failed to create default Move.toml")?;
            file.write_all(default_move_toml.as_bytes())
                .context("Failed to write default Move.toml")?;
        }

        Ok(temp_dir)
    }

    pub async fn process(
        &self,
        files: Vec<(String, String)>,
        prover_options: Option<String>,
    ) -> Result<ProverResponse> {
        let hash = Self::generate_hash(&files, prover_options.clone());

        if let Some((out, err, status)) = self.check_cache(&hash).await? {
            return Ok(ProverResponse {
                out,
                err,
                status,
                cached: true,
            });
        }

        let temp_dir = Self::build_files(files)?;

        let (out, err, status) = match self.execute_prover(temp_dir.path(), prover_options).await {
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

        Ok(ProverResponse {
            out,
            err,
            status,
            cached: false,
        })
    }
}
