use anyhow::{Context, Result};
use redis::{AsyncCommands, RedisError};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::process::Command;

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
    "-proverOpt:O:model_validate=true",
    "-vcsCores:2",
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
    pub fn new(skip_redis: bool) -> Result<Self> {        
        let cache_lifetime_seconds = std::env::var("CACHE_LIFETIME_SECONDS")
            .unwrap_or_else(|_| "172800".to_string())
            .parse::<u64>()
            .context("Invalid CACHE_LIFETIME_SECONDS value")?;

        if skip_redis {
            return Ok(Self { 
                redis_client: None,
                cache_lifetime_seconds,
            });
        }

        let redis_host = std::env::var("REDIS_HOST")
            .context("REDIS_HOST environment variable not set")?;
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

        let redis_client = Some(redis::Client::open(info)
            .context("Failed to create Redis client")?);

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
            let mut conn = redis_client.get_multiplexed_async_connection().await
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
            let mut conn = redis_client.get_multiplexed_async_connection().await
                .context("Failed to get Redis connection")?;

            let serialized = serde_json::to_string(&(out, err, status))?;
            let result: Result<(), RedisError> = conn.set_ex(hash, serialized, self.cache_lifetime_seconds).await;
            result?;
        }

        Ok(())
    }

    fn get_boogie_command(&self, boogie_file_name: &str) -> Result<Vec<String>> {
        let boogie_exe = std::env::var("BOOGIE_EXE")
            .context("BOOGIE_EXE environment variable not set")?;
        let z3_exe = std::env::var("Z3_EXE")
            .context("Z3_EXE environment variable not set")?;

        let mut result = vec![boogie_exe];
        result.extend(DEFAULT_BOOGIE_FLAGS.iter().map(|s| s.to_string()));
        result.push(format!("-proverOpt:PROVER_PATH={z3_exe}"));
        result.push(boogie_file_name.to_string());

        Ok(result)
    }

    async fn execute_boogie(&self, temp_file_path: &str) -> Result<(String, String, i32)> {
        let args = self.get_boogie_command(temp_file_path)?;

        let output = Command::new(&args[0])
            .args(&args[1..])
            .output()
            .context("Failed to execute boogie command")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        Ok((
            stdout.to_string(),
            stderr.to_string(),
            output.status.code().unwrap_or(-1),
        ))
    }

    pub async fn process(&self, file_text: String) -> Result<ProverResponse> {
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
        temp_file.write_all(file_text.as_bytes())
            .context("Failed to write to temporary file")?;

        let temp_file_path = temp_file.path().to_string_lossy().to_string();

        let (out, err, status) = match self.execute_boogie(&temp_file_path).await {
            Ok(output) => output,
            Err(e) => (String::new(), format!("Error remote executing boogie: {}", e), -1),
        };

        if let Err(e) = self.cache_result(&hash, &out, &err, status).await {
            println!("Failed to cache result: {}", e);
        } else {
            println!("Result cached successfully for hash: {}", hash);
        }

        Ok(ProverResponse {
            out,
            err,
            status: status,
            cached: false,
        })
    }
}
