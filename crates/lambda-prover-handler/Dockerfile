FROM --platform=linux/arm64 public.ecr.aws/amazonlinux/amazonlinux:latest AS builder

ENV PATH="/root/.cargo/bin:$PATH"

RUN yum update -y && \
    yum groupinstall -y "Development Tools" && \
    yum install -y --allowerasing \
        curl \
        git \
        openssl-devel && \
    yum clean all

RUN mkdir -p /app

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Download Lambda Runtime Interface Emulator
RUN curl -Lo /opt/aws-lambda-rie \
    https://github.com/aws/aws-lambda-runtime-interface-emulator/releases/latest/download/aws-lambda-rie-arm64 && \
    chmod +x /opt/aws-lambda-rie

# Install sui-prover
RUN git clone --depth 1 https://github.com/asymptotic-code/sui-prover.git /tmp/prover && \
    cd /tmp/prover && \
    cargo install --path crates/sui-prover --locked && \
    cd ../.. && \
    rm -rf /tmp

COPY . /app/
WORKDIR /app

RUN cargo build --release --bin lambda-prover-handler

FROM --platform=linux/arm64 public.ecr.aws/amazonlinux/amazonlinux:latest

RUN yum update -y && \
    yum install -y \
        git \
        openssl \
        ca-certificates \
        shadow-utils \
        procps-ng && \
    yum clean all

ENV PATH="/opt/bin:$PATH"

RUN mkdir -p /opt/bin

COPY --from=builder /root/.cargo/bin/sui-prover /opt/bin/sui-prover
COPY --from=builder /app/target/release/lambda-handler /opt/bin/lambda-handler
COPY --from=builder /opt/aws-lambda-rie /usr/local/bin/aws-lambda-rie

RUN chmod +x /opt/bin/sui-prover /opt/bin/lambda-handler /usr/local/bin/aws-lambda-rie

RUN mkdir -p /root/.move && \
    git clone https://github.com/asymptotic-code/sui.git /root/.move/https___github_com_asymptotic-code_sui_git_next

# Create entry point script to detect local vs Lambda environment
RUN echo '#!/bin/sh' > /entry.sh && \
    echo '' >> /entry.sh && \
    echo '# Create sui_prover.toml from environment variable if provided' >> /entry.sh && \
    echo 'if [ -n "${SUI_PROVER_SECRET}" ]; then' >> /entry.sh && \
    echo '  mkdir -p /root/.asymptotic' >> /entry.sh && \
    echo '  echo "${SUI_PROVER_SECRET}" > /root/.asymptotic/sui_prover.toml' >> /entry.sh && \
    echo 'fi' >> /entry.sh && \
    echo '' >> /entry.sh && \
    echo 'if [ -z "${AWS_LAMBDA_RUNTIME_API}" ]; then' >> /entry.sh && \
    echo '  /usr/local/bin/aws-lambda-rie /opt/bin/lambda-handler' >> /entry.sh && \
    echo 'else' >> /entry.sh && \
    echo '  /opt/bin/lambda-handler' >> /entry.sh && \
    echo 'fi' >> /entry.sh && \
    chmod +x /entry.sh

WORKDIR /var/task

ENTRYPOINT ["/entry.sh"]
