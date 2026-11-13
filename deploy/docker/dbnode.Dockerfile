# syntax=docker/dockerfile:1.7
#
# Database node image: secret-shared-db's `server` (one of the five nodes), plus `pki` (the network
# configuration generator) and `handoff_client`. The database checkout has no image of its own
# (its server/docker-compose.yml runs only Postgres). Postgres runs as its own container
# (deploy/compose/db-node.yml.example). STATUS: written, not built here (DEPLOYMENT.md).
#
# Build context: the directory staged by `deploy/scripts/build_artifacts.py context --out DIR`
# (it holds src/.deps/secret-shared-db-handoff, the checkout the harness uses: branch
# two-party-handoff-signup-tool).
#
#   docker build -f deploy/docker/dbnode.Dockerfile -t tls-mpc-dbnode DIR
#
# Mounted at run time: /srv/ssdb/config (this node's directory from `pki`: config.json with its
# signing key and the network configuration; read-only). Nothing secret is in the image.

ARG UBUNTU=ubuntu:24.04
ARG RUSTUP_VERSION=1.28.2
ARG RUST_STABLE=1.88.0

FROM ${UBUNTU} AS build
ARG RUSTUP_VERSION
ARG RUST_STABLE
ENV DEBIAN_FRONTEND=noninteractive
RUN set -eux; apt-get update; \
    apt-get install -y --no-install-recommends build-essential clang cmake git curl ca-certificates pkg-config \
        libssl-dev protobuf-compiler libclang-dev perl; \
    rm -rf /var/lib/apt/lists/*
RUN set -eux; \
    case "$(uname -m)" in x86_64) T=x86_64-unknown-linux-gnu ;; aarch64) T=aarch64-unknown-linux-gnu ;; *) exit 1 ;; esac; \
    curl -fsSL -o /tmp/rustup-init "https://static.rust-lang.org/rustup/archive/${RUSTUP_VERSION}/${T}/rustup-init"; \
    chmod +x /tmp/rustup-init; /tmp/rustup-init -y --profile minimal --default-toolchain "${RUST_STABLE}" --no-modify-path
ENV PATH=/root/.cargo/bin:$PATH
COPY src/.deps/secret-shared-db-handoff /src/ssdb
# Not vendored: fetches crates.io and the forks on github.com its Cargo.toml names. --locked.
RUN set -eux; cargo build --locked --release --manifest-path /src/ssdb/Cargo.toml --target-dir /build \
      -p server -p pki --bin server --bin handoff_client --bin pki; \
    mkdir -p /out; for b in server handoff_client pki; do install -D /build/release/$b /out/$b; done; \
    install -D /src/ssdb/server/init.sql /out/init.sql

FROM ${UBUNTU} AS runtime
ENV DEBIAN_FRONTEND=noninteractive
RUN set -eux; apt-get update; apt-get install -y --no-install-recommends ca-certificates libssl3t64 python3; \
    rm -rf /var/lib/apt/lists/*; \
    groupadd --system --gid 10002 ssdb; useradd --system --uid 10002 --gid ssdb --home-dir /srv/ssdb --shell /usr/sbin/nologin ssdb; \
    mkdir -p /srv/ssdb/config
COPY --from=build /out/server /out/handoff_client /out/pki /opt/ssdb/bin/
COPY --from=build /out/init.sql /opt/ssdb/share/init.sql
ENV PATH=/opt/ssdb/bin:$PATH RUST_LOG=info,sqlx=warn
USER ssdb
WORKDIR /srv/ssdb
ENTRYPOINT ["/opt/ssdb/bin/server", "--config-dir", "/srv/ssdb/config"]
