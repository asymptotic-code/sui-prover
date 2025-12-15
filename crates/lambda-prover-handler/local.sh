# 1. For complete flow
docker build -t my-lambda-prover-function .


# 2.
 docker run -p 9000:8080 \
  --cpus="4" \
  -e AWS_LAMBDA_FUNCTION_NAME="lambda-prover-handler" \
  -e AWS_LAMBDA_FUNCTION_MEMORY_SIZE=10240 \
  -e AWS_LAMBDA_FUNCTION_TIMEOUT=1500 \
  -e AWS_LAMBDA_FUNCTION_VERSION="$LATEST" \
  -e ALLOWED_KEY_HASHES_CSV="10a6e6cc8311a3e2bcc09bf6c199adecd5dd59408c343e926b129c4914f3cb01" \
  -e SUI_PROVER_SECRET="url = \"https://hdhs3sbtlk22w5ceivvbuege4i0devap.lambda-url.us-west-2.on.aws/\"\nkey = \"test_password\"\nconcurrency = 10" \
  my-lambda-prover-function 

# 3.

curl -XPOST "http://localhost:9000/2015-03-31/functions/function/invocations" \
  -H "Content-Type: application/json" \
  -d '{
    "body": "{\"files\": [{\"path\": \"test.move\", \"content\": \"module spec::test { }\"}], \"options\": \"\"}",
    "headers": {
      "Content-Type": "application/json",
      "Authorization": "test_password"
    },
    "httpMethod": "POST",
    "path": "/"
  }'
