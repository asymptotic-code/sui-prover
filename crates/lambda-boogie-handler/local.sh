# 1. For complete flow
docker build -t my-lambda-function .


# 2.
 docker run -p 9000:8080 \
  --cpus="4" \
  -e AWS_LAMBDA_FUNCTION_NAME="lambda-boogie-handler" \
  -e AWS_LAMBDA_FUNCTION_MEMORY_SIZE=10240 \
  -e AWS_LAMBDA_FUNCTION_TIMEOUT=1500 \
  -e AWS_LAMBDA_FUNCTION_VERSION="$LATEST" \
  -e ALLOWED_KEY_HASHES_CSV="10a6e6cc8311a3e2bcc09bf6c199adecd5dd59408c343e926b129c4914f3cb01" \
  my-lambda-function 

# 3.

curl -XPOST "http://localhost:9000/2015-03-31/functions/function/invocations" \
  -H "Content-Type: application/json" \
  -d '{
    "body": "{\"file_text\": \"hello!\"}",
    "headers": {
      "Content-Type": "application/json",
      "Authorization": "test_password"
    },
    "httpMethod": "POST",
    "path": "/"
  }'

# For basic usage

# 1.

docker build -f Dockerfile.boogie-runner -t boogie-runner...

# 2.

docker run -v $(pwd):/workspace boogie-runner pool::withdraw_spec.bpl
