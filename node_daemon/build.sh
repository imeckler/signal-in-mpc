#!/bin/bash
# Build the node daemon and the application stand-in (offline, vendored crates, the toolchain
# local_signal_server/scripts/provision.sh uses). Binaries: target/debug/node-daemon, notify-app.
#   node_daemon/build.sh [TARGET_DIRECTORY]
set -euo pipefail
CRATE="$(cd "$(dirname "$0")" && pwd)"
TARGET="${1:-$CRATE/target}"
cargo +nightly-2025-09-24 --config "$CRATE/.cargo/config.toml" build --offline --quiet --ignore-rust-version \
  --manifest-path "$CRATE/Cargo.toml" --target-dir "$TARGET"
