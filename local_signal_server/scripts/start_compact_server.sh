#!/bin/bash
# Start a SECOND local Signal-Server whose sender certificates are in production's compact form
# (make_config.py `compact`: embedSigner false, signer by id 0x7357C357, UUID as bytes), with its
# own TLS terminator. The default instance (scripts/start_server.sh, ports 18080/18081/18443) is
# not touched, so runs against it are not disturbed.
#
#   plain HTTP/1.1 + h2c : http://127.0.0.1:19080   (lss-provision with LSS_SERVER=127.0.0.1:19080)
#   admin (Dropwizard)   : http://127.0.0.1:19081/ping
#   TLS 1.3 terminator   : 127.0.0.1:19443 -> 127.0.0.1:19080 (trust state/tls/ca.pem, as the default instance),
#                          scripts/coalesced_terminator.py: production's handshake shape
#
# Stop it with scripts/stop_compact_server.sh. Pids and config: state/compact/.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
TP="$HERE/third_party"
SRC="$TP/Signal-Server"
STATE="$HERE/state"
OWN="$STATE/compact"
LOGS="$HERE/logs"
JAVA="$TP/jdk/current/Contents/Home/bin/java"
mkdir -p "$OWN" "$LOGS"

if [ ! -f "$STATE/classpath.txt" ]; then echo "run scripts/build_server.sh first" >&2; exit 1; fi
if [ ! -f "$STATE/tls/server.pem" ]; then bash "$HERE/scripts/gen_tls_cert.sh"; fi
running() { [ -f "$OWN/$1" ] && kill -0 "$(cat "$OWN/$1")" 2>/dev/null; }
export DOCKER_HOST="${DOCKER_HOST:-unix://$HOME/.orbstack/run/docker.sock}"

if running server.pid; then
  echo "compact server already running (pid $(cat "$OWN/server.pid"))"
else
  python3 -I "$HERE/scripts/make_config.py" "$SRC" "$OWN/local.yml" compact
  export TESTCONTAINERS_DOCKER_SOCKET_OVERRIDE="${TESTCONTAINERS_DOCKER_SOCKET_OVERRIDE:-/var/run/docker.sock}"
  export SIGNAL_SERVER_CONFIG="$OWN/local.yml"
  CP="$SRC/service/target/classes:$SRC/service/target/test-classes:$(cat "$STATE/classpath.txt")"
  nohup "$JAVA" -Xmx2g -cp "$CP" org.whispersystems.textsecuregcm.LocalWhisperServerService \
    > "$LOGS/server-compact.log" 2>&1 < /dev/null &
  echo $! > "$OWN/server.pid"
  echo "compact server pid $(cat "$OWN/server.pid"); log: $LOGS/server-compact.log"
fi

if running terminator.pid; then
  echo "compact terminator already running (pid $(cat "$OWN/terminator.pid"))"
else
  # Production's handshake shape (real_signal/state/handshake-production.json): the encrypted flight
  # in one record with 16 bytes of padding, one Ed25519 certificate (the leaf; the client builds
  # the path to state/tls/ca.pem itself).
  nohup python3 -I "$HERE/scripts/coalesced_terminator.py" --cert "$STATE/tls/server.pem" --key "$STATE/tls/server.key" \
    --listen 19443 --backend 127.0.0.1:19080 --pad 16 --leaf-only > "$LOGS/tls_terminator-compact.log" 2>&1 < /dev/null &
  echo $! > "$OWN/terminator.pid"
  echo "compact terminator pid $(cat "$OWN/terminator.pid"); log: $LOGS/tls_terminator-compact.log"
fi

for _ in $(seq 1 360); do
  if ! kill -0 "$(cat "$OWN/server.pid")" 2>/dev/null; then
    echo "compact server exited during startup; see $LOGS/server-compact.log" >&2; exit 1
  fi
  if [ "$(curl -s -m 2 http://127.0.0.1:19081/ping || true)" = "pong" ]; then
    echo "compact server ready"; exit 0
  fi
  sleep 1
done
echo "compact server not ready after 360s; see $LOGS/server-compact.log" >&2
exit 1
