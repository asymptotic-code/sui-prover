ARG TARGETPLATFORM=linux/arm64

FROM --platform=$TARGETPLATFORM public.ecr.aws/amazonlinux/amazonlinux:latest AS builder

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
RUN git clone --depth 1 https://github.com/asymptotic-code/sui-prover.git /tmp/prover
RUN cd /tmp/prover && cargo fetch
RUN cd /tmp/prover && cargo install --path crates/sui-prover --locked

COPY . /app/
WORKDIR /app

RUN cargo build --release --bin lambda-prover-handler

FROM --platform=$TARGETPLATFORM public.ecr.aws/amazonlinux/amazonlinux:latest

RUN yum update -y && \
    yum install -y \
        git \
        openssl \
        ca-certificates \
        shadow-utils \
        procps-ng && \
    yum clean all

ENV PATH="/opt/bin:$PATH"
ENV MOVE_HOME="/opt/.move"

RUN mkdir -p /opt/bin

COPY --from=builder /root/.cargo/bin/sui-prover /opt/bin/sui-prover
COPY --from=builder /app/target/release/lambda-prover-handler /opt/bin/lambda-prover-handler
COPY --from=builder /opt/aws-lambda-rie /usr/local/bin/aws-lambda-rie

RUN chmod +x /opt/bin/sui-prover /opt/bin/lambda-prover-handler /usr/local/bin/aws-lambda-rie

RUN mkdir -p /opt/.move && \
    git clone --depth 1 https://github.com/asymptotic-code/sui.git /opt/.move/https___github_com_asymptotic-code_sui_git_next && \
    git clone --depth 1 https://github.com/asymptotic-code/sui-prover.git /opt/.move/https___github_com_asymptotic-code_sui-prover_git_main && \
    chmod -R 755 /opt/.move


# Create entry point script to detect local vs Lambda environment
RUN echo '#!/bin/sh' > /entry.sh && \
    echo '' >> /entry.sh && \
    echo '# Ensure writable directories exist' >> /entry.sh && \
    echo 'mkdir -p /tmp/.move /tmp/.asymptotic' >> /entry.sh && \
    echo '' >> /entry.sh && \
    echo 'if [ -z "${AWS_LAMBDA_RUNTIME_API}" ]; then' >> /entry.sh && \
    echo '  /usr/local/bin/aws-lambda-rie /opt/bin/lambda-prover-handler' >> /entry.sh && \
    echo 'else' >> /entry.sh && \
    echo '  /opt/bin/lambda-prover-handler' >> /entry.sh && \
    echo 'fi' >> /entry.sh && \
    chmod +x /entry.sh

WORKDIR /var/task

ENTRYPOINT ["/entry.sh"]
