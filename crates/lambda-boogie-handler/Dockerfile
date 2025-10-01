FROM public.ecr.aws/amazonlinux/amazonlinux:latest AS builder

ENV DOTNET_INSTALL_DIR="/opt/dotnet/"
ENV INSTALL_DIR="/opt/bin/"
ENV Z3_VERSION="4.11.2"
ENV DOTNET_VERSION="8.0"
ENV PATH="/opt/bin:/opt/dotnet:$PATH"

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

RUN mkdir -p "${DOTNET_INSTALL_DIR}" "${INSTALL_DIR}" /app

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:$PATH"

RUN curl -sSL https://dot.net/v1/dotnet-install.sh | \
    TERM=linux /bin/bash -s -- --channel ${DOTNET_VERSION} --install-dir "${DOTNET_INSTALL_DIR}" --version latest

RUN Z3_PKG="z3-${Z3_VERSION}-x64-glibc-2.31" && \
    curl -LOs "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_PKG}.zip" && \
    unzip -q "${Z3_PKG}.zip" && \
    cp "${Z3_PKG}/bin/z3" "${INSTALL_DIR}" && \
    chmod +x "${INSTALL_DIR}z3" && \
    rm -rf "${Z3_PKG}.zip" "${Z3_PKG}"

RUN mkdir -p "${DOTNET_INSTALL_DIR}tools/" && \
    "${DOTNET_INSTALL_DIR}dotnet" tool install --tool-path "${DOTNET_INSTALL_DIR}tools/" Boogie

COPY . /app/
WORKDIR /app

RUN cargo build --release --bin lambda-handler

FROM public.ecr.aws/amazonlinux/amazonlinux:latest

RUN yum update -y && \
    yum install -y \
        libicu \
        zlib \
        openssl \
        ca-certificates \
        shadow-utils && \
    yum clean all

ENV DOTNET_ROOT="/opt/dotnet"
ENV PATH="/opt/bin:/opt/dotnet:/opt/dotnet/tools:$PATH"
ENV BOOGIE_EXE="/opt/dotnet/tools/boogie"
ENV Z3_EXE="/opt/bin/z3"

RUN mkdir -p /opt/bin /opt/dotnet/tools

COPY --from=builder /opt/dotnet /opt/dotnet
COPY --from=builder /opt/bin/z3 /opt/bin/z3
COPY --from=builder /app/target/release/lambda-handler /opt/bin/lambda-handler

RUN chmod +x /opt/bin/lambda-handler /opt/bin/z3

WORKDIR /var/task

ENTRYPOINT ["/opt/bin/lambda-handler"]
