#!/bin/bash
# Start the LOCAL Signal-Server (upstream LocalWhisperServerService + test config with local
# bindings) and the TLS 1.3 terminator in front of it. Both run in the background; pids in state/.
#
#   plain HTTP/1.1 + h2c : http://127.0.0.1:18080   (provisioning tool talks here)
#   admin (Dropwizard)   : http://127.0.0.1:18081/ping
#   TLS 1.3 terminator   : 127.0.0.1:18443 -> 127.0.0.1:18080 (MPC client connects here; trust state/tls/ca.pem)
#
# Dependencies (DynamoDB Local, Redis cluster) are started by the server itself through
# Testcontainers on the local Docker daemon (OrbStack) and removed when the JVM exits.
# S3 clients are pointed at a closed loopback port (see scripts/make_config.py), so no request
# goes to AWS; one-time PQ prekeys are therefore unsupported locally.
# Environment: TRANSCRIPTS=1 to record plaintext transcripts in logs/transcripts/.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
TP="$HERE/third_party"
SRC="$TP/Signal-Server"
STATE="$HERE/state"
LOGS="$HERE/logs"
JAVA="$TP/jdk/current/Contents/Home/bin/java"
mkdir -p "$STATE" "$LOGS"

if [ ! -f "$STATE/classpath.txt" ]; then echo "run scripts/build_server.sh first" >&2; exit 1; fi
if [ ! -f "$STATE/tls/server.pem" ]; then bash "$HERE/scripts/gen_tls_cert.sh"; fi
running() { [ -f "$STATE/$1" ] && kill -0 "$(cat "$STATE/$1")" 2>/dev/null; }
export DOCKER_HOST="${DOCKER_HOST:-unix://$HOME/.orbstack/run/docker.sock}"

if running server.pid; then
  echo "server already running (pid $(cat "$STATE/server.pid"))"
else
  python3 -I "$HERE/scripts/make_config.py" "$SRC" "$STATE/server/local.yml"
  export TESTCONTAINERS_DOCKER_SOCKET_OVERRIDE="${TESTCONTAINERS_DOCKER_SOCKET_OVERRIDE:-/var/run/docker.sock}"
  export SIGNAL_SERVER_CONFIG="$STATE/server/local.yml"
  CP="$SRC/service/target/classes:$SRC/service/target/test-classes:$(cat "$STATE/classpath.txt")"
  nohup "$JAVA" -Xmx2g -cp "$CP" org.whispersystems.textsecuregcm.LocalWhisperServerService \
    > "$LOGS/server.log" 2>&1 < /dev/null &
  echo $! > "$STATE/server.pid"
  echo "server pid $(cat "$STATE/server.pid"); log: $LOGS/server.log"
fi

if running terminator.pid; then
  echo "terminator already running (pid $(cat "$STATE/terminator.pid"))"
else
  TERM_ARGS=(--cert "$STATE/tls/server.pem" --key "$STATE/tls/server.key" --listen 18443 --backend 127.0.0.1:18080 --require-aes128)
  if [ "${TRANSCRIPTS:-0}" = "1" ]; then TERM_ARGS+=(--transcripts "$LOGS/transcripts"); fi
  nohup python3 -I "$HERE/scripts/tls_terminator.py" "${TERM_ARGS[@]}" > "$LOGS/tls_terminator.log" 2>&1 < /dev/null &
  echo $! > "$STATE/terminator.pid"
  echo "terminator pid $(cat "$STATE/terminator.pid"); log: $LOGS/tls_terminator.log"
fi

# Wait for the admin ping (container startup + table creation can take a few minutes on first run).
for _ in $(seq 1 360); do
  if ! kill -0 "$(cat "$STATE/server.pid")" 2>/dev/null; then
    echo "server exited during startup; see $LOGS/server.log" >&2; exit 1
  fi
  if [ "$(curl -s -m 2 http://127.0.0.1:18081/ping || true)" = "pong" ]; then
    echo "server ready"; exit 0
  fi
  sleep 1
done
echo "server not ready after 360s; see $LOGS/server.log" >&2
exit 1
