#!/bin/bash
# Build (offline, vendored crates) and run the conventional provisioning client.
#   scripts/provision.sh                 -> register sender + recipient, establish session, verify one send
#   scripts/provision.sh receive recipient 10
#   scripts/provision.sh send sender recipient "text"
# Talks only to the local server at 127.0.0.1:18080. Accounts are written to state/accounts/.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
CRATE="$HERE/provision"
# cargo reads .cargo/config.toml from the working directory, so pass the vendored-sources config explicitly.
# Same toolchain flags tls-mpc uses for signal_backend/Oracle (libsignal v0.106.1 declares rustc 1.93.1).
cargo +nightly-2025-09-24 --config "$CRATE/.cargo/config.toml" build --offline --quiet --ignore-rust-version \
  --manifest-path "$CRATE/Cargo.toml"
if [ $# -eq 0 ]; then set -- provision; fi
exec "$CRATE/target/debug/lss-provision" "$@"
