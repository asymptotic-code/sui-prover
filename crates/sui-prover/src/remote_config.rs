use clap::Args;
use move_prover_boogie_backend::boogie_backend::options::RemoteOptions;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

#[derive(Debug, Serialize, Deserialize, Clone)]
struct CloudConfig {
    url: String,
    key: String,
    concurrency: usize,
}

fn default_config_path() -> anyhow::Result<PathBuf> {
    let home = std::env::var("HOME")
        .or_else(|_| std::env::var("USERPROFILE"))
        .map_err(|_| anyhow::anyhow!("Could not determine home directory"))?;

    Ok(PathBuf::from(home)
        .join(".asymptotic")
        .join("sui_prover.toml"))
}

fn save_cloud_config(
    url: &str,
    key: &str,
    concurrency: usize,
    config_path: Option<&Path>,
) -> anyhow::Result<PathBuf> {
    let config = CloudConfig {
        url: url.to_string(),
        key: key.to_string(),
        concurrency,
    };

    let path = match config_path {
        Some(p) => p.to_path_buf(),
        None => default_config_path()?,
    };

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }

    let toml_string = toml::to_string_pretty(&config)?;
    fs::write(&path, toml_string)?;

    Ok(path)
}

fn load_cloud_config(config_path: Option<&Path>) -> anyhow::Result<CloudConfig> {
    let path = match config_path {
        Some(p) => p.to_path_buf(),
        None => default_config_path()?,
    };

    if !path.exists() {
        return Err(anyhow::anyhow!(
            "Cloud config file not found at: {}",
            path.display()
        ));
    }

    let toml_string = fs::read_to_string(&path)?;
    let config: CloudConfig = toml::from_str(&toml_string)?;

    Ok(config)
}

#[derive(Args, Default)]
#[clap(next_help_heading = "Remote Options (concurrent remote boogie execution)")]
pub struct RemoteConfig {
    /// Use cloud configuration from file
    #[clap(long = "cloud", global = true)]
    pub cloud: bool,

    /// Path to cloud configuration file (default: $HOME/.asymptotic/sui_prover.toml)
    #[clap(long = "cloud-config-path", global = true)]
    pub cloud_config_path: Option<PathBuf>,

    /// Create/update cloud configuration file interactively
    #[clap(long = "cloud-config", global = true)]
    pub cloud_config_create: bool,
}

impl RemoteConfig {
    pub fn create(&self) -> anyhow::Result<()> {
        println!("=== Cloud Configuration Setup ===\n");

        let existing_config = load_cloud_config(self.cloud_config_path.as_deref()).ok();

        if existing_config.is_some() {
            println!("Found existing configuration. Press Enter to keep current values.\n");
        }

        let url = if let Some(ref config) = existing_config {
            print!("Enter remote URL [{}]: ", config.url);
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            if input.is_empty() {
                config.url.clone()
            } else {
                input.to_string()
            }
        } else {
            print!("Enter remote URL: ");
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            if input.is_empty() {
                return Err(anyhow::anyhow!("URL cannot be empty"));
            }
            input.to_string()
        };

        let key = if let Some(ref config) = existing_config {
            print!("Enter API key [***hidden***]: ");
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            if input.is_empty() {
                config.key.clone()
            } else {
                input.to_string()
            }
        } else {
            print!("Enter API key: ");
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            if input.is_empty() {
                return Err(anyhow::anyhow!("API key cannot be empty"));
            }
            input.to_string()
        };

        let concurrency = if let Some(ref config) = existing_config {
            print!("Enter concurrency [{}]: ", config.concurrency);
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            let res = if input.is_empty() {
                config.concurrency
            } else {
                input.parse::<usize>().map_err(|_| {
                    anyhow::anyhow!("Invalid concurrency value. Must be a positive integer.")
                })?
            };
            if res == 0 {
                return Err(anyhow::anyhow!("Concurrency must be a positive integer."));
            }
            res
        } else {
            print!("Enter concurrency (default: 10): ");
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            let res = if input.is_empty() {
                10
            } else {
                input.parse::<usize>().map_err(|_| {
                    anyhow::anyhow!("Invalid concurrency value. Must be a positive integer.")
                })?
            };
            if res == 0 {
                return Err(anyhow::anyhow!("Concurrency must be a positive integer."));
            }
            res
        };

        let path = save_cloud_config(&url, &key, concurrency, self.cloud_config_path.as_deref())?;

        println!("\n✓ Cloud configuration saved successfully!");
        println!("  Config file: {}", path.display());
        println!("\nYou can now use --cloud to load these settings.");
        Ok(())
    }

    pub fn to_config(&self) -> anyhow::Result<Option<RemoteOptions>> {
        if !self.cloud {
            return Ok(None);
        }

        let config = load_cloud_config(self.cloud_config_path.as_deref()).map_err(|e| {
            anyhow::anyhow!(
                "Failed to load cloud config: {}\n\
                     Hint: Create a config file first using:\n\
                     --cloud-config",
                e
            )
        })?;

        Ok(Some(RemoteOptions {
            url: config.url,
            api_key: config.key,
            concurrency: config.concurrency,
        }))
    }
}
