#!/bin/bash
# Build the worker (offline, vendored crates). One variant per security mode, each with a -test
# form (the field engine's fault hook and unpinned circuit loading compiled in; never deployed):
#   node_worker/build.sh VARIANT [TARGET_ROOT]     VARIANT: v3 | v3-test | sh-v3 | sh-v3-test
# Binary: TARGET_ROOT/VARIANT/release/node-worker (TARGET_ROOT defaults to node_worker/target).
# Needs the engine library of the same variant first:
#   python3 handshake_backend/EmpHybridWork/build_hybrid_v3.py --engine-abi VARIANT
set -euo pipefail
CRATE="$(cd "$(dirname "$0")" && pwd)"
VARIANT="${1:?usage: node_worker/build.sh v3|v3-test|sh-v3|sh-v3-test [TARGET_ROOT]}"
ROOT="${2:-$CRATE/target}"
case "$VARIANT" in
  v3) FEATURES=() ;;
  v3-test) FEATURES=(--features test-engine) ;;
  sh-v3) FEATURES=(--features semi-honest) ;;
  sh-v3-test) FEATURES=(--features semi-honest,test-engine) ;;
  *) echo "node_worker/build.sh: unknown variant $VARIANT" >&2; exit 2 ;;
esac
cargo --config "$CRATE/.cargo/config.toml" build --offline --quiet --release \
  --manifest-path "$CRATE/Cargo.toml" --target-dir "$ROOT/$VARIANT" ${FEATURES[@]+"${FEATURES[@]}"}
