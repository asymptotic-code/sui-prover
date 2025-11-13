use std::{fs::create_dir_all, fs::remove_dir_all, process::Command};

use crate::handler::ProverHandler;
use anyhow::Result;
use dotenv;
use lambda_runtime::{service_fn, Error, LambdaEvent};
use rustls::crypto::CryptoProvider;
use serde_json::{from_str, json, Value};

pub mod handler;

fn cleanup_processes() {
    if let Ok(output) = Command::new("ps").args(["-ef"]).output() {
        println!("--- Process list before cleanup ---");
        if let Ok(process_list) = String::from_utf8(output.stdout) {
            println!("{}", process_list);
        }
    }

    // Kill any orphaned Z3 processes
    let _ = Command::new("pkill").args(["-9", "z3"]).output();

    // Kill any orphaned dotnet processes
    let _ = Command::new("pkill").args(["-9", "dotnet"]).output();

    // Clean temp files
    remove_dir_all("/tmp").ok();
    create_dir_all("/tmp/lambda").ok();
}

fn make_error_response(status_code: u16, error: &str) -> Value {
    json!({
        "statusCode": status_code,
        "headers": {
            "Content-Type": "application/json"
        },
        "body": {
            "error": error
        }
    })
}

fn make_success_response(body: String) -> Value {
    json!({
        "statusCode": 200,
        "headers": {
            "Content-Type": "application/json"
        },
        "body": body.to_string()
    })
}

fn security_check(event: Value) -> Option<Value> {
    if event.get("headers").is_none() || event.get("headers").unwrap().as_object().is_none() {
        return Some(make_error_response(400, "Headers are missing or invalid."));
    }

    let auth_header: Option<&Value> = event
        .get("headers")
        .unwrap()
        .as_object()
        .unwrap()
        .get("Authorization")
        .or_else(|| {
            event
                .get("headers")
                .unwrap()
                .as_object()
                .unwrap()
                .get("authorization")
        });

    if auth_header.is_none() || auth_header.unwrap().as_str().is_none() {
        return Some(make_error_response(
            401,
            "Authorization header is missing or invalid.",
        ));
    }

    let auth_value = auth_header.unwrap().as_str().unwrap();
    let allowed = std::env::var("ALLOWED_KEY_HASHES_CSV")
        .unwrap_or_else(|_| "".to_string())
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<Vec<String>>();

    if allowed.is_empty() {
        return None;
    }

    if !allowed.contains(&ProverHandler::generate_hash(auth_value)) {
        Some(make_error_response(403, "Forbidden"))
    } else {
        None
    }
}

async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    cleanup_processes();
    dotenv::dotenv().ok();

    match CryptoProvider::install_default(rustls::crypto::ring::default_provider()) {
        Ok(_) => {}
        Err(_) => { /* Provider is already installed, we can ignore the error */ }
    }

    let (event, _context) = event.into_parts();

    let security_response = security_check(event.clone());
    if security_response.is_some() {
        return Ok(security_response.unwrap());
    }

    if event.get("body").is_none() || event.get("body").unwrap().as_str().is_none() {
        return Ok(make_error_response(400, "Body is missing or invalid."));
    }

    let body_value: Value = from_str(event.get("body").unwrap().as_str().unwrap()).unwrap();
    let body = body_value.as_object().unwrap();

    if body.get("file_text").is_none() || body.get("file_text").unwrap().as_str().is_none() {
        return Ok(make_error_response(400, "File text is missing."));
    }

    let file_text = body.get("file_text").unwrap().as_str().unwrap().to_string();
    let boogie_options = if let Some(options) = body.get("options") {
        Some(options.as_str().unwrap().to_string())
    } else {
        None
    };

    let prover = ProverHandler::new()?;

    let response = match prover.process(file_text, boogie_options).await {
        Ok(resp) => resp,
        Err(e) => {
            return Ok(make_error_response(
                500,
                &format!("Prover processing failed: {}", e),
            ));
        }
    };

    let response_body = serde_json::to_string(&response).unwrap();

    Ok(make_success_response(response_body))
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    let func = service_fn(handler);
    lambda_runtime::run(func).await
}

#[tokio::test]
async fn local_handler() -> Result<()> {
    let file_path = "<>/sui-kit/examples/amm/output/spec_no_abort_check.bpl";
    let file_text = match std::fs::read_to_string(file_path) {
        Ok(content) => content,
        Err(e) => {
            println!("❌ Failed to read test file: {}", e);
            println!("⚠️  Test skipped because test file is not available");
            return Ok(());
        }
    };

    let prover = ProverHandler::new().unwrap();
    prover.process(file_text, None).await.unwrap();

    Ok(())
}
