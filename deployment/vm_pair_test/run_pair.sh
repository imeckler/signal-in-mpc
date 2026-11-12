#!/bin/sh
# One machine's side of the whole benchmark run (README, part 3). Same command on both machines,
# party 0 first, party 1 within a minute:
#
#     sh vm-pair/kit/run_pair.sh 0 10.77.0.2 10.77.0.1 [ITERATIONS]      on machine a (party 0: listens on its tunnel address)
#     sh vm-pair/kit/run_pair.sh 1 10.77.0.1 -         [ITERATIONS]      on machine b (party 1: dials)
#
# Stage 1, one worker pair: for malicious then semi-honest mode, ITERATIONS messages (default 100),
#          then a contact's first-send preparation and the receive sequence's field programs.
# Stage 2, two worker pairs at once: ITERATIONS messages each, both modes.
# A system record (steal time, memory, tunnel counters) runs beside both stages.
# Logs: vm-pair/logs/ (one-pair/, two-pairs/, sysmon.csv). Ports: TCP 26000-26799 on the tunnel.
# Certificates must be in place first: kit/bench_certs.sh (README).
set -eu
[ $# -ge 3 ] || { echo "usage: $0 PARTY(0|1) PEER_TUNNEL_ADDRESS LISTEN_ADDRESS|- [ITERATIONS]" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PARTY=$1; PEER=$2; LISTEN=$3; N=${4:-100}
LOGS=$ROOT/logs; mkdir -p "$LOGS"
listen=""; [ "$LISTEN" = - ] || listen="--listen $LISTEN"
python3 "$ROOT/kit/net/sysmon.py" --out "$LOGS/sysmon.csv" &
monitor=$!
trap 'kill $monitor 2>/dev/null || true' EXIT INT TERM
status=0
echo "== stage 1: one worker pair, $N messages per mode"
python3 "$ROOT/kit/run_bench.py" --party "$PARTY" --peer "$PEER" $listen --iterations "$N" --port-base 26000 \
    --root "$ROOT" --work "$ROOT/work" --logs "$LOGS/one-pair" || status=1
if [ $status = 0 ]; then
    sleep 5
    echo "== stage 2: two worker pairs at once, $N messages each per mode"
    python3 "$ROOT/kit/run_bench.py" --party "$PARTY" --peer "$PEER" $listen --iterations "$N" --port-base 26400 --pairs 2 --steps bench \
        --root "$ROOT" --work "$ROOT/work" --logs "$LOGS/two-pairs" || status=1
fi
[ $status = 0 ] && echo "run complete; logs in $LOGS" || echo "run FAILED; logs in $LOGS"
exit $status
