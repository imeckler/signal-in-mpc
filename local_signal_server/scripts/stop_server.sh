#!/bin/bash
# Stop the local Signal-Server and the TLS terminator started by start_server.sh.
# The server's shutdown hooks (and the Testcontainers reaper) remove the DynamoDB/Redis containers;
# any that remain are listed at the end (they carry the label org.testcontainers=true).
set -uo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
STATE="$HERE/state"
export DOCKER_HOST="${DOCKER_HOST:-unix://$HOME/.orbstack/run/docker.sock}"

stop() {  # name pidfile
  local f="$STATE/$2"
  [ -f "$f" ] || { echo "$1: not running"; return; }
  local pid; pid="$(cat "$f")"
  if kill -0 "$pid" 2>/dev/null; then
    kill "$pid"
    for _ in $(seq 1 60); do kill -0 "$pid" 2>/dev/null || break; sleep 1; done
    if kill -0 "$pid" 2>/dev/null; then kill -9 "$pid"; echo "$1: killed"; else echo "$1: stopped"; fi
  else
    echo "$1: not running"
  fi
  rm -f "$f"
}
stop terminator terminator.pid
stop server server.pid

sleep 3
left="$(docker ps -q --filter label=org.testcontainers=true)"
if [ -n "$left" ]; then
  echo "Testcontainers containers still running (the reaper normally removes them within ~10s):"
  docker ps --filter label=org.testcontainers=true --format '{{.ID}} {{.Image}} {{.Names}}'
else
  echo "no Testcontainers containers left"
fi
