FROM --platform=linux/arm64 ubuntu:22.04 AS builder

ENV DEBIAN_FRONTEND=noninteractive

ENV DOTNET_INSTALL_DIR="/opt/dotnet"
ENV INSTALL_DIR="/opt/bin"
ENV Z3_VERSION="4.15.3"
ENV DOTNET_VERSION="8.0"
ENV PATH="${INSTALL_DIR}:${DOTNET_INSTALL_DIR}:${PATH}"

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        build-essential \
        curl \
        unzip \
        git \
        tar \
        libicu-dev \
        zlib1g-dev \
        libssl-dev \
        pkg-config \
        ca-certificates \
        sudo && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN mkdir -p "${DOTNET_INSTALL_DIR}" "${INSTALL_DIR}" /app

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN curl -sSL https://dot.net/v1/dotnet-install.sh | bash -s -- \
    --channel ${DOTNET_VERSION} \
    --install-dir "${DOTNET_INSTALL_DIR}" \
    --version latest

RUN curl -L https://github.com/krallin/tini/releases/download/v0.19.0/tini-arm64 -o /opt/tini && \
    chmod +x /opt/tini

RUN Z3_PKG="z3-${Z3_VERSION}-arm64-glibc-2.34" && \
    curl -LO "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_PKG}.zip" && \
    unzip -q "${Z3_PKG}.zip" && \
    cp "${Z3_PKG}/bin/z3" "${INSTALL_DIR}" && \
    chmod +x "${INSTALL_DIR}/z3" && \
    rm -rf "${Z3_PKG}.zip" "${Z3_PKG}"

RUN mkdir -p "${DOTNET_INSTALL_DIR}/tools" && \
    "${DOTNET_INSTALL_DIR}/dotnet" tool install --tool-path "${DOTNET_INSTALL_DIR}/tools" Boogie

RUN curl -Lo /opt/aws-lambda-rie \
    https://github.com/aws/aws-lambda-runtime-interface-emulator/releases/latest/download/aws-lambda-rie-arm64 && \
    chmod +x /opt/aws-lambda-rie

COPY . /app
WORKDIR /app
RUN cargo build --release --bin lambda-handler


FROM --platform=linux/arm64 ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        libicu70 \
        zlib1g \
        libssl3 \
        ca-certificates \
        procps \
        sudo && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN echo '#!/bin/sh' > /opt/init.sh && \
    echo 'echo 1048576 > /proc/sys/fs/pipe-max-size 2>/dev/null || true' >> /opt/init.sh && \
    echo 'exec "$@"' >> /opt/init.sh && \
    chmod +x /opt/init.sh

ENV DOTNET_ROOT="/opt/dotnet"
ENV PATH="/opt/bin:/opt/dotnet:/opt/dotnet/tools:${PATH}"
ENV BOOGIE_EXE="/opt/dotnet/tools/boogie"
ENV Z3_EXE="/opt/bin/z3"

# .NET GC settings
ENV DOTNET_GCHeapHardLimit=6442450944
ENV DOTNET_GCServer=0
ENV DOTNET_GCRetainVM=0
ENV DOTNET_GCConserveMemory=9

RUN mkdir -p /opt/bin /opt/dotnet/tools

COPY --from=builder /opt/tini /opt/tini
COPY --from=builder /opt/dotnet /opt/dotnet
COPY --from=builder /opt/bin/z3 /opt/bin/z3
COPY --from=builder /app/target/release/lambda-handler /opt/bin/lambda-handler
COPY --from=builder /opt/aws-lambda-rie /usr/local/bin/aws-lambda-rie

RUN chmod +x /opt/bin/lambda-handler /opt/bin/z3 /opt/tini /usr/local/bin/aws-lambda-rie

RUN echo '#!/bin/sh' > /entry.sh && \
    echo 'if [ -z "${AWS_LAMBDA_RUNTIME_API}" ]; then' >> /entry.sh && \
    echo '  exec /opt/tini -- /usr/local/bin/aws-lambda-rie /opt/bin/lambda-handler' >> /entry.sh && \
    echo 'else' >> /entry.sh && \
    echo '  exec /opt/tini -- /opt/bin/lambda-handler' >> /entry.sh && \
    echo 'fi' >> /entry.sh && \
    chmod +x /entry.sh

WORKDIR /var/task

ENTRYPOINT ["/entry.sh"]
