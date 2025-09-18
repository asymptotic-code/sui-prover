#!/bin/bash

# Build and push Sui Prover Docker image to AWS ECR
# Usage: ./build-ecr.sh [ECR_REPOSITORY_URI] [AWS_REGION] [IMAGE_TAG]

set -e

# Default values based on AWS instructions
DEFAULT_ECR_URI="679720146588.dkr.ecr.us-west-2.amazonaws.com/prover/prover"
DEFAULT_REGION="us-west-2"
DEFAULT_TAG="latest"
LOCAL_IMAGE_NAME="prover/prover"

# Parse arguments
ECR_REPOSITORY_URI=${1:-$DEFAULT_ECR_URI}
AWS_REGION=${2:-$DEFAULT_REGION}
IMAGE_TAG=${3:-$DEFAULT_TAG}

# Validate required parameters
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

# Build the Docker image with Lambda-compatible format
echo "Building Docker image for AWS Lambda compatibility..."
export BUILDX_NO_DEFAULT_ATTESTATIONS=1
docker build --platform linux/amd64 -t "$LOCAL_IMAGE_NAME:$IMAGE_TAG" .

# Tag for ECR
echo "Tagging image for ECR..."
docker tag "$LOCAL_IMAGE_NAME:$IMAGE_TAG" "$ECR_REPOSITORY_URI:$IMAGE_TAG"

# Login to ECR
echo "Logging in to ECR..."
aws ecr get-login-password --region "$AWS_REGION" | docker login --username AWS --password-stdin "$ECR_REPOSITORY_URI"

# Push to ECR
echo "Pushing image to ECR..."
docker push "$ECR_REPOSITORY_URI:$IMAGE_TAG"

echo "Successfully pushed $ECR_REPOSITORY_URI:$IMAGE_TAG"

# Clean up local images to save space
echo "Cleaning up local images..."
docker rmi "$LOCAL_IMAGE_NAME:$IMAGE_TAG" "$ECR_REPOSITORY_URI:$IMAGE_TAG"

echo "Build and push completed successfully!"
