# syntax=docker/dockerfile:1.7
#
# Computation node image: node daemon + Lean controller + node_worker (EMP and MP-SPDZ engines)
# + the certificate checker + the database client + the scaffolding KEM tool.
# DEPLOYMENT.md, "Build". STATUS: written; see DEPLOYMENT.md "Status of this tooling" for what was
# built and run.
#
# Build context: the directory `deploy/scripts/build_artifacts.py context --out DIR` stages (NOT
# the repository root): DIR/bundle (make_bundle.py --with-workers: engines, pins, kit), DIR/src
# (tracked sources, the vendored crates, libsignal and the database checkout), DIR/pins.json.
#
#   docker build -f deploy/docker/worker.Dockerfile --build-arg MODE=malicious -t tls-mpc-node:malicious DIR
#   docker build -f deploy/docker/worker.Dockerfile --build-arg MODE=semi-honest -t tls-mpc-node:semi-honest DIR
#
# Nothing secret and no circuit is in the image. Mounted at run time (deploy/compose/*.example):
#   /srv/tls-mpc/config    the daemon configuration (read-only)
#   /srv/tls-mpc/secrets   peer key, database client key, bearer token, the workers' Player-Data (read-only)
#   /srv/tls-mpc/circuits  manifest.txt and the gate lists (read-only)
#   /opt/tls-mpc/word      the word circuits and the 22 V3 field programs (read-only; this path is
#                          compiled into the worker: NODE_WORKER_WORD_DIR / EMP_WORD_CIRCUIT_DIR)
#   /srv/tls-mpc/state     the daemon's state directory (logs, work, journal, events)

# Base images, pinned. UBUNTU: replace the tag by its digest after the first pull
# (`docker buildx imagetools inspect ubuntu:24.04`); the build records what it used in build-info.json.
ARG UBUNTU=ubuntu:24.04
# Toolchains (lean-toolchain; node_worker/build.sh's cargo; node_daemon/build.sh's and provision.sh's nightly).
ARG ELAN_VERSION=v4.2.3
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.31.0
ARG RUSTUP_VERSION=1.28.2
ARG RUST_STABLE=1.88.0
ARG RUST_NIGHTLY=nightly-2025-09-24
ARG MODE=malicious
# 1: build the engines for a CPU class, not this build machine's exact CPU (build_linux.sh --portable).
ARG PORTABLE=1
# Optional: an Ubuntu archive snapshot (e.g. 20261101T000000Z) to freeze the distribution packages.
ARG APT_SNAPSHOT=

############################################################################ base: compilers, -dev libraries
FROM ${UBUNTU} AS base
ARG APT_SNAPSHOT
ENV DEBIAN_FRONTEND=noninteractive
# The package list of deployment/vm_pair_test/build_linux.sh --packages (less the network tools),
# plus curl/xz/zstd for the toolchain downloads and protobuf/libclang for the database client.
RUN set -eux; \
    if [ -n "$APT_SNAPSHOT" ]; then SNAP="--snapshot $APT_SNAPSHOT"; else SNAP=; fi; \
    apt-get update $SNAP; \
    apt-get install -y --no-install-recommends $SNAP \
        build-essential clang cmake make git python3 pkg-config ca-certificates openssl curl xz-utils zstd \
        libssl-dev libsodium-dev libgmp-dev libboost-dev libboost-filesystem-dev libboost-iostreams-dev \
        libboost-thread-dev libboost-system-dev protobuf-compiler libclang-dev perl; \
    rm -rf /var/lib/apt/lists/*

############################################################################ engines: EMP, MP-SPDZ, engine library
FROM base AS engines
ARG PORTABLE
COPY bundle /bundle
COPY src/handshake_backend /src/handshake_backend
COPY src/signal_backend /src/signal_backend
COPY src/deploy/docker/build_engine_abi.sh /src/deploy/docker/build_engine_abi.sh
# The bundle's own Linux build (emp-tool, emp-ot, the field engine's library, field_engine.o in both
# modes, the fixtures and the C++ workers), then the engine library for node_worker in both modes.
RUN set -eux; cd /bundle; sha256sum -c --quiet MANIFEST.sha256; \
    if [ "$PORTABLE" = 1 ]; then sh kit/build_linux.sh --portable; else sh kit/build_linux.sh; fi
RUN set -eux; for v in v3 sh-v3; do \
      sh /src/deploy/docker/build_engine_abi.sh /bundle /src /build/engine-abi /opt/tls-mpc/word "$v"; done

############################################################################ lean: the controller
FROM base AS lean
ARG ELAN_VERSION
ARG LEAN_TOOLCHAIN
RUN set -eux; \
    case "$(uname -m)" in x86_64) T=x86_64-unknown-linux-gnu ;; aarch64) T=aarch64-unknown-linux-gnu ;; *) exit 1 ;; esac; \
    curl -fsSL -o /tmp/elan.tar.gz "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${T}.tar.gz"; \
    sha256sum /tmp/elan.tar.gz | tee /tmp/elan.sha256; \
    tar -xzf /tmp/elan.tar.gz -C /tmp; /tmp/elan-init -y --default-toolchain none --no-modify-path; \
    /root/.elan/bin/elan toolchain install "${LEAN_TOOLCHAIN}"; /root/.elan/bin/elan default "${LEAN_TOOLCHAIN}"
ENV PATH=/root/.elan/bin:$PATH
COPY src/lean-toolchain src/lakefile.toml src/lake-manifest.json src/TlsMpc.lean /src/
COPY src/TlsMpc /src/TlsMpc
COPY src/handshake_backend /src/handshake_backend
WORKDIR /src
RUN set -eux; test "$(cat lean-toolchain)" = "${LEAN_TOOLCHAIN}"; lake build public_service_controller; \
    install -D .lake/build/bin/public_service_controller /out/bin/public_service_controller
# The certificate checker the controller runs on the server's chain (as run_real_test.py builds it).
RUN set -eux; c++ -std=c++20 -O2 handshake_backend/public_auth.cpp -lssl -lcrypto -o /out/bin/public_auth

############################################################################ rust: worker, daemon, KEM tool, database client
FROM engines AS rust
ARG RUSTUP_VERSION
ARG RUST_STABLE
ARG RUST_NIGHTLY
ARG MODE
RUN set -eux; \
    case "$(uname -m)" in x86_64) T=x86_64-unknown-linux-gnu ;; aarch64) T=aarch64-unknown-linux-gnu ;; *) exit 1 ;; esac; \
    curl -fsSL -o /tmp/rustup-init "https://static.rust-lang.org/rustup/archive/${RUSTUP_VERSION}/${T}/rustup-init"; \
    sha256sum /tmp/rustup-init | tee /tmp/rustup.sha256; chmod +x /tmp/rustup-init; \
    /tmp/rustup-init -y --profile minimal --default-toolchain "${RUST_STABLE}" --no-modify-path; \
    /root/.cargo/bin/rustup toolchain install "${RUST_NIGHTLY}" --profile minimal
ENV PATH=/root/.cargo/bin:$PATH
COPY src /src
# node_worker: the production variant of the mode, linked against the engine library above; the
# word-circuit directory is the mount point. (node_worker/build.sh does the same but passes the
# build machine's absolute vendored path; the image's is given here.)
RUN set -eux; \
    case "$MODE" in malicious) F= ;; semi-honest) F="--features semi-honest" ;; *) echo "MODE: malicious or semi-honest" >&2; exit 2 ;; esac; \
    NODE_WORKER_ENGINE_DIR=/build/engine-abi NODE_WORKER_WORD_DIR=/opt/tls-mpc/word \
      cargo +"${RUST_STABLE}" --config /src/deploy/docker/cargo-vendored.toml build --offline --locked --release \
      --manifest-path /src/node_worker/Cargo.toml --target-dir /build/node_worker $F; \
    install -D /build/node_worker/release/node-worker /out/bin/node-worker
RUN set -eux; \
    cargo +"${RUST_NIGHTLY}" --config /src/deploy/docker/cargo-vendored.toml build --offline --locked --release --ignore-rust-version \
      --manifest-path /src/node_daemon/Cargo.toml --target-dir /build/node_daemon; \
    install -D /build/node_daemon/release/node-daemon /out/bin/node-daemon; \
    install -D /build/node_daemon/release/notify-app /out/bin/notify-app; \
    cargo +"${RUST_NIGHTLY}" --config /src/deploy/docker/cargo-vendored.toml build --offline --locked --release --ignore-rust-version \
      --manifest-path /src/local_signal_server/provision/Cargo.toml --target-dir /build/provision; \
    install -D /build/provision/release/lss-provision /out/bin/lss-provision
# The database client (secret-shared-db, branch two-party-handoff-signup-tool): not vendored, so
# this step fetches crates.io and the Signal forks on github.com named in its Cargo.toml (no
# Signal service host). --locked: exactly its Cargo.lock.
RUN set -eux; \
    cargo +"${RUST_STABLE}" build --locked --release --manifest-path /src/.deps/secret-shared-db-handoff/Cargo.toml \
      --target-dir /build/ssdb -p server --bin handoff_client; \
    install -D /build/ssdb/release/handoff_client /out/bin/handoff_client
RUN set -eux; install -D /bundle/engines/MP-SPDZ/libSPDZ.so /out/lib/libSPDZ.so

############################################################################ runtime
FROM ${UBUNTU} AS runtime
ARG MODE
ARG UBUNTU
ARG LEAN_TOOLCHAIN
ARG RUST_STABLE
ARG RUST_NIGHTLY
ARG APT_SNAPSHOT
ENV DEBIAN_FRONTEND=noninteractive
RUN set -eux; \
    if [ -n "$APT_SNAPSHOT" ]; then SNAP="--snapshot $APT_SNAPSHOT"; else SNAP=; fi; \
    apt-get update $SNAP; \
    apt-get install -y --no-install-recommends $SNAP python3 openssl ca-certificates procps \
        libgmp10 libgmpxx4ldbl libsodium23 libssl3t64 libboost-filesystem1.83.0 libboost-iostreams1.83.0 libboost-system1.83.0; \
    rm -rf /var/lib/apt/lists/*; \
    groupadd --system --gid 10001 tlsmpc; useradd --system --uid 10001 --gid tlsmpc --home-dir /srv/tls-mpc --shell /usr/sbin/nologin tlsmpc; \
    mkdir -p /srv/tls-mpc/config /srv/tls-mpc/secrets /srv/tls-mpc/circuits /srv/tls-mpc/state /opt/tls-mpc/word; \
    chown tlsmpc:tlsmpc /srv/tls-mpc/state; chmod 700 /srv/tls-mpc/state
COPY --from=lean /out/bin/ /opt/tls-mpc/bin/
COPY --from=rust /out/bin/ /opt/tls-mpc/bin/
COPY --from=rust /out/lib/ /opt/tls-mpc/lib/
COPY src/handshake_backend/EmpHybridWork/circuit_cache.py /opt/tls-mpc/share/circuit_cache.py
COPY src/deploy /opt/tls-mpc/share/deploy
COPY src/deployment/vm_pair_test/bench_certs.sh /opt/tls-mpc/share/bench_certs.sh
COPY pins.json /opt/tls-mpc/share/pins.json
COPY context.json /opt/tls-mpc/share/context.json
RUN set -eux; python3 - <<'EOF'
import hashlib, json, os, pathlib
bins = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(pathlib.Path('/opt/tls-mpc/bin').iterdir())}
libs = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(pathlib.Path('/opt/tls-mpc/lib').iterdir())}
info = dict(format='tls-mpc-image-v1', mode=os.environ['MODE'], base=os.environ['UBUNTU'], lean=os.environ['LEAN_TOOLCHAIN'],
            rust=[os.environ['RUST_STABLE'], os.environ['RUST_NIGHTLY']], apt_snapshot=os.environ.get('APT_SNAPSHOT') or None,
            word_dir='/opt/tls-mpc/word', binaries=bins, libraries=libs,
            context=json.loads(pathlib.Path('/opt/tls-mpc/share/context.json').read_text()))
pathlib.Path('/opt/tls-mpc/share/build-info.json').write_text(json.dumps(info, indent=1, sort_keys=True) + '\n')
EOF
ENV PATH=/opt/tls-mpc/bin:$PATH \
    LD_LIBRARY_PATH=/opt/tls-mpc/lib \
    TLS_MPC_MODE=${MODE} \
    PYTHONDONTWRITEBYTECODE=1
USER tlsmpc
WORKDIR /srv/tls-mpc/state
VOLUME ["/srv/tls-mpc/state"]
ENTRYPOINT ["python3", "/opt/tls-mpc/share/deploy/docker/entrypoint.py"]
CMD ["daemon"]
