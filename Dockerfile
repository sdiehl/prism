# Bundles LLVM 22 + clang so prism runs with no host toolchain.
FROM rust:1-bookworm AS builder
RUN set -eux; \
    apt-get update; \
    apt-get install -y --no-install-recommends wget gnupg ca-certificates; \
    wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
      | tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc >/dev/null; \
    echo "deb http://apt.llvm.org/bookworm/ llvm-toolchain-bookworm-22 main" \
      > /etc/apt/sources.list.d/llvm.list; \
    apt-get update; \
    apt-get install -y --no-install-recommends llvm-22-dev libpolly-22-dev clang-22; \
    rm -rf /var/lib/apt/lists/*
ENV LLVM_SYS_221_PREFIX=/usr/lib/llvm-22 \
    PRISM_CC=/usr/lib/llvm-22/bin/clang
WORKDIR /src
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim AS runtime
RUN set -eux; \
    apt-get update; \
    apt-get install -y --no-install-recommends wget gnupg ca-certificates; \
    wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
      | tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc >/dev/null; \
    echo "deb http://apt.llvm.org/bookworm/ llvm-toolchain-bookworm-22 main" \
      > /etc/apt/sources.list.d/llvm.list; \
    apt-get update; \
    apt-get install -y --no-install-recommends llvm-22 clang-22; \
    apt-get purge -y wget gnupg; apt-get autoremove -y; \
    rm -rf /var/lib/apt/lists/*
COPY --from=builder /src/target/release/prism /usr/bin/prism
ENV PRISM_CC=/usr/lib/llvm-22/bin/clang
ENTRYPOINT ["/usr/bin/prism"]
CMD ["--help"]
