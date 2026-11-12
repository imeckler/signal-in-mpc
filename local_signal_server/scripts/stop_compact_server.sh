#!/bin/bash
# Stop the second (compact-certificate) local Signal-Server and its terminator started by
# start_compact_server.sh. The default instance is not touched.
set -uo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
OWN="$HERE/state/compact"

stop() {  # name pidfile
  local f="$OWN/$2"
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
stop "compact terminator" terminator.pid
stop "compact server" server.pid
