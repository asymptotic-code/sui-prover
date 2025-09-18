
use anyhow::Result;
use lambda_runtime::{service_fn, Error, LambdaEvent};
use crate::handler::ProverHandler;
use serde_json::{from_str, json, Value};

pub mod handler;

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

async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    let (event, _context) = event.into_parts();

    if event.get("body").is_none() || event.get("body").unwrap().as_str().is_none() {
        return Ok(make_error_response(400, "Body is missing or invalid."));
    }

    let body_value: Value = from_str(event.get("body").unwrap().as_str().unwrap()).unwrap();
    let body = body_value.as_object().unwrap();

    if body.get("file_text").is_none() || body.get("file_text").unwrap().as_str().is_none() {
        return Ok(make_error_response(400, "File text is missing."));
    }

    let file_text = body.get("file_text").unwrap().as_str().unwrap().to_string();

    let prover = ProverHandler::new(true)?;

    let response = match prover.process(file_text).await {
        Ok(resp) => resp,
        Err(e) => {
            return Ok(make_error_response(500, &format!("Prover processing failed: {}", e)));
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

    let prover = ProverHandler::new(true).unwrap();
    prover.process(file_text).await.unwrap();

    Ok(())
}
