# Multi-stage build for Sui Prover
FROM public.ecr.aws/amazonlinux/amazonlinux:latest AS builder

# Set environment variables
ENV DOTNET_INSTALL_DIR="/opt/dotnet/"
ENV INSTALL_DIR="/opt/bin/"
ENV Z3_VERSION="4.11.2"
ENV DOTNET_VERSION="8.0"
ENV PATH="/opt/bin:/opt/dotnet:$PATH"

# Install system dependencies
RUN yum update -y && \
    yum groupinstall -y "Development Tools" && \
    yum install -y --allowerasing \
        curl \
        unzip \
        git \
        tar \
        icu \
        zlib \
        openssl-devel \
        libicu-devel \
        zlib-devel && \
    yum clean all

# Create necessary directories
RUN mkdir -p "${DOTNET_INSTALL_DIR}" "${INSTALL_DIR}" /app

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:$PATH"

# Install .NET 8 SDK
RUN curl -sSL https://dot.net/v1/dotnet-install.sh | \
    TERM=linux /bin/bash -s -- --channel ${DOTNET_VERSION} --install-dir "${DOTNET_INSTALL_DIR}" --version latest

# Install Z3 theorem prover
RUN Z3_PKG="z3-${Z3_VERSION}-x64-glibc-2.31" && \
    curl -LOs "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_PKG}.zip" && \
    unzip -q "${Z3_PKG}.zip" && \
    cp "${Z3_PKG}/bin/z3" "${INSTALL_DIR}" && \
    chmod +x "${INSTALL_DIR}z3" && \
    rm -rf "${Z3_PKG}.zip" "${Z3_PKG}"

# Install Boogie
RUN mkdir -p "${DOTNET_INSTALL_DIR}tools/" && \
    "${DOTNET_INSTALL_DIR}dotnet" tool install --tool-path "${DOTNET_INSTALL_DIR}tools/" Boogie

# Copy workspace source code
COPY . /app/
WORKDIR /app

# Build Lambda Boogie Handler
RUN cargo build --release --bin lambda-handler

# Create final runtime image
FROM public.ecr.aws/amazonlinux/amazonlinux:latest

# Install minimal runtime dependencies
RUN yum update -y && \
    yum install -y \
        libicu \
        zlib \
        openssl \
        ca-certificates \
        shadow-utils && \
    yum clean all

# Set environment variables
ENV DOTNET_ROOT="/opt/dotnet"
ENV PATH="/opt/bin:/opt/dotnet:/opt/dotnet/tools:$PATH"
ENV BOOGIE_EXE="/opt/dotnet/tools/boogie"
ENV Z3_EXE="/opt/bin/z3"

# Create necessary directories
RUN mkdir -p /opt/bin /opt/dotnet/tools

# Copy binaries from builder stage
COPY --from=builder /opt/dotnet /opt/dotnet
COPY --from=builder /opt/bin/z3 /opt/bin/z3
COPY --from=builder /app/target/release/lambda-handler /opt/bin/lambda-handler

# Make binaries executable
RUN chmod +x /opt/bin/lambda-handler /opt/bin/z3

# Set working directory for Lambda
WORKDIR /var/task

# Default command for Lambda execution
ENTRYPOINT ["/opt/bin/lambda-handler"]
