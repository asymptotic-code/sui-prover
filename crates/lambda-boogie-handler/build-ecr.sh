set -e

DEFAULT_ECR_URI="679720146588.dkr.ecr.us-west-2.amazonaws.com/prover/prover"
DEFAULT_REGION="us-west-2"
DEFAULT_TAG="latest"
LOCAL_IMAGE_NAME="prover/prover"

ECR_REPOSITORY_URI=${1:-$DEFAULT_ECR_URI}
AWS_REGION=${2:-$DEFAULT_REGION}
IMAGE_TAG=${3:-$DEFAULT_TAG}

if [ -z "$ECR_REPOSITORY_URI" ]; then
    echo "Usage: $0 [ECR_REPOSITORY_URI] [AWS_REGION] [IMAGE_TAG]"
    echo "Default: $0 $DEFAULT_ECR_URI $DEFAULT_REGION $DEFAULT_TAG"
    echo "Example: $0 123456789012.dkr.ecr.us-west-2.amazonaws.com/sui-prover us-west-2 v1.0.0"
    exit 1
fi

echo "Building Sui Prover Docker image for ECR..."
echo "Repository: $ECR_REPOSITORY_URI"
echo "Region: $AWS_REGION"
echo "Tag: $IMAGE_TAG"

echo "Building Docker image for AWS Lambda compatibility..."
export BUILDX_NO_DEFAULT_ATTESTATIONS=1
docker build --platform linux/arm64 -f Dockerfile.aws -t "$LOCAL_IMAGE_NAME:$IMAGE_TAG" .

echo "Tagging image for ECR..."
docker tag "$LOCAL_IMAGE_NAME:$IMAGE_TAG" "$ECR_REPOSITORY_URI:$IMAGE_TAG"

echo "Logging in to ECR..."
aws ecr get-login-password --region "$AWS_REGION" | docker login --username AWS --password-stdin "$ECR_REPOSITORY_URI"

echo "Pushing image to ECR..."
docker push "$ECR_REPOSITORY_URI:$IMAGE_TAG"

echo "Successfully pushed $ECR_REPOSITORY_URI:$IMAGE_TAG"

echo "Cleaning up local images..."
docker rmi "$LOCAL_IMAGE_NAME:$IMAGE_TAG" "$ECR_REPOSITORY_URI:$IMAGE_TAG"

echo "Build and push completed successfully!"
