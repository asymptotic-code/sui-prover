# CLAUDE.md - lambda-boogie-handler

AWS Lambda wrapper for remote Boogie/Z3 verification execution.

## Overview

This crate provides a serverless endpoint that accepts Boogie verification files via HTTP, executes Boogie/Z3, and returns results with optional Redis caching.

## Directory Structure

```
lambda-boogie-handler/
├── lambda.rs                   # AWS Lambda HTTP handler
├── handler.rs                  # ProverHandler (Boogie execution, caching)
├── Cargo.toml                  # Dependencies
├── Dockerfile                  # Development image (Ubuntu)
├── Dockerfile.aws              # Production image (Amazon Linux)
├── Dockerfile.boogie-runner    # Standalone Boogie runner
├── build-ecr.sh                # AWS ECR deployment script
├── local.sh                    # Local testing examples
└── sample.env                  # Environment variable template
```

## Key Components

### lambda.rs - HTTP Handler

```rust
// Main Lambda handler
async fn handler(event: Request) -> Result<Response<Body>, Error>

// Security check (SHA256 hash of API key)
fn security_check(headers: &HeaderMap) -> Result<(), StatusCode>

// Process cleanup (kills orphaned Z3/dotnet processes)
fn cleanup_processes()
```

**Request Format**:
```json
{
  "body": "{\"file_text\": \"<boogie code>\", \"options\": \"<boogie flags>\"}",
  "headers": {"Authorization": "<api_key>"}
}
```

**Response Format**:
```json
{
  "statusCode": 200,
  "body": "{\"out\": \"<stdout>\", \"err\": \"<stderr>\", \"status\": 0, \"cached\": false}"
}
```

### handler.rs - ProverHandler

```rust
pub struct ProverHandler {
    redis_client: Option<redis::Client>,
    cache_lifetime_seconds: u64,  // Default: 172800 (2 days)
}

impl ProverHandler {
    pub async fn process(&self, file_text: &str, options: &str) -> Result<ProverResponse>;
}
```

**Key methods**:
- `new()` - Initialize with optional Redis connection
- `generate_hash()` - SHA256 of Boogie file (cache key)
- `check_cache()` / `cache_result()` - Redis operations
- `execute_boogie()` - Spawns Boogie process with timeout

**Default Boogie flags**:
```
-inferModifies -printVerifiedProceduresCount:0 -printModel:1
-enhancedErrorMessages:1 -useArrayAxioms
-proverOpt:O:smt.QI.EAGER_THRESHOLD=10
-proverOpt:O:smt.QI.LAZY_THRESHOLD=100
-vcsCores:4 -verifySeparately
-vcsSplitOnEveryAssert -vcsFinalAssertTimeout:600
```

## Environment Variables

```bash
REDIS_HOST              # Redis server (optional, enables caching)
REDIS_PORT              # Redis port (default: 6379)
CACHE_LIFETIME_SECONDS  # Cache TTL (default: 172800)
ALLOWED_KEY_HASHES_CSV  # Comma-separated SHA256 hashes of allowed API keys
BOOGIE_EXE              # Path to Boogie executable
Z3_EXE                  # Path to Z3 executable
```

## Docker Images

### Development (Dockerfile)
- Base: Ubuntu 22.04
- Includes: AWS Lambda RIE for local testing
- Entry point auto-detects local vs Lambda environment

### Production (Dockerfile.aws)
- Base: Amazon Linux
- Aggressive .NET GC tuning for 6GB memory
- Optimized for AWS Lambda execution

### Standalone (Dockerfile.boogie-runner)
- Pure Boogie/Z3 execution for local testing
- Usage: `docker run -v $(pwd):/workspace boogie-runner spec.bpl`

## Local Development

```bash
# Build image
docker build -t lambda-boogie .

# Run with Lambda RIE
docker run -p 9000:8080 \
  -e ALLOWED_KEY_HASHES_CSV="<sha256_hash>" \
  lambda-boogie

# Test with curl
curl -XPOST "http://localhost:9000/2015-03-31/functions/function/invocations" \
  -H "Content-Type: application/json" \
  -d '{
    "body": "{\"file_text\": \"procedure main() { assert true; }\"}",
    "headers": {"Authorization": "test_key"}
  }'
```

## AWS Deployment

```bash
# Build and push to ECR
./build-ecr.sh <ecr-repo-url> <region> <tag>

# Recommended Lambda config
# Memory: 10240 MB
# Timeout: 1500 seconds (25 min)
# Architecture: ARM64
```

## Integration with Main Prover

The main prover uses this Lambda via `--cloud` flag:

```bash
# Configure remote endpoint (once)
sui-prover --cloud-config

# Run with remote verification
sui-prover --cloud --path ./project
```

Configuration stored at `$HOME/.asymptotic/sui_prover.toml`:
```toml
url = "https://lambda-url/prover"
api_key = "your_key"
concurrency = 4
```

## Process Management

- Uses `libc::setsid()` to create process groups
- Kills entire group with `SIGKILL` after execution
- Cleans orphaned Z3/dotnet processes between invocations
- Handles timeouts gracefully

## Caching

- Optional Redis-based caching (graceful degradation if unavailable)
- Cache key: SHA256 of Boogie file content
- Default TTL: 2 days
- Stores: (stdout, stderr, exit_code) tuple

## HTTP Status Codes

- `200` - Success (cached or fresh)
- `400` - Invalid request body
- `401` - Missing Authorization header
- `403` - API key not in allowed list
- `500` - Prover error