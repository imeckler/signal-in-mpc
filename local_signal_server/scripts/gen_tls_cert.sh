#!/bin/bash
# Local TLS PKI for the TLS terminator in front of the local Signal-Server.
#   state/tls/ca.pem       trust root handed to the MPC client (its TRUST argument)
#   state/tls/server.pem   leaf (+ CA) chain served by the terminator
#   state/tls/server.key   leaf private key
# Leaf names: server.example (what check_signal_service_v3.py passes as HOSTNAME), localhost, 127.0.0.1.
# LEAF_KEY=ed25519 (default, same profile the existing harness uses) or p256.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
OPENSSL="${OPENSSL:-/opt/homebrew/opt/openssl@3/bin/openssl}"
OUT="$HERE/state/tls"
LEAF_KEY="${LEAF_KEY:-ed25519}"
mkdir -p "$OUT"
chmod 700 "$OUT"
if [ -f "$OUT/server.pem" ] && [ "${FORCE:-0}" != "1" ]; then echo "exists: $OUT (FORCE=1 to regenerate)"; exit 0; fi

"$OPENSSL" genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out "$OUT/ca.key"
"$OPENSSL" req -x509 -new -key "$OUT/ca.key" -sha256 -days 365 -subj "/CN=tls-mpc LOCAL Signal test CA" \
  -addext "basicConstraints=critical,CA:TRUE,pathlen:0" -addext "keyUsage=critical,keyCertSign,cRLSign" -out "$OUT/ca.pem"

if [ "$LEAF_KEY" = "p256" ]; then
  "$OPENSSL" genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out "$OUT/server.key"
else
  "$OPENSSL" genpkey -algorithm ED25519 -out "$OUT/server.key"
fi
"$OPENSSL" req -new -key "$OUT/server.key" -subj "/CN=server.example" -out "$OUT/server.csr"
cat > "$OUT/leaf.ext" <<EOF
basicConstraints=critical,CA:FALSE
keyUsage=critical,digitalSignature
extendedKeyUsage=serverAuth
subjectAltName=DNS:server.example,DNS:localhost,IP:127.0.0.1
EOF
"$OPENSSL" x509 -req -in "$OUT/server.csr" -CA "$OUT/ca.pem" -CAkey "$OUT/ca.key" -CAcreateserial -days 30 \
  -extfile "$OUT/leaf.ext" -out "$OUT/leaf.pem"
cat "$OUT/leaf.pem" "$OUT/ca.pem" > "$OUT/server.pem"
chmod 600 "$OUT"/*.key
"$OPENSSL" verify -CAfile "$OUT/ca.pem" "$OUT/leaf.pem"
