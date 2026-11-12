#!/bin/sh
# One-machine check after build_linux.sh: both parties on this machine over 127.0.0.1, a few
# iterations in each mode, all three steps. Proves the build runs before the two-machine test.
# Uses its own directory (vm-pair/selftest/) and throwaway certificates; ports 27000-27199.
#     sh vm-pair/kit/selftest.sh [ITERATIONS]      (default 3; needs about 8 GB of memory free)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
KIT=$ROOT/kit
N=${1:-3}
DIR=$ROOT/selftest
rm -rf "$DIR"; mkdir -p "$DIR/p0" "$DIR/p1"
sh "$KIT/bench_certs.sh" init 0 "$DIR/p0/work" >/dev/null
sh "$KIT/bench_certs.sh" init 1 "$DIR/p1/work" >/dev/null
sh "$KIT/bench_certs.sh" trust "$DIR/p1/work/Player-Data/P1.pem" "$DIR/p0/work" >/dev/null
sh "$KIT/bench_certs.sh" trust "$DIR/p0/work/Player-Data/P0.pem" "$DIR/p1/work" >/dev/null
python3 "$KIT/run_bench.py" --party 0 --peer 127.0.0.1 --port-base 27000 --iterations "$N" --root "$ROOT" \
    --work "$DIR/p0/work" --logs "$DIR/p0/logs" >"$DIR/p0.out" 2>&1 &
first=$!
sleep 1
status=0
python3 "$KIT/run_bench.py" --party 1 --peer 127.0.0.1 --port-base 27000 --iterations "$N" --root "$ROOT" \
    --work "$DIR/p1/work" --logs "$DIR/p1/logs" >"$DIR/p1.out" 2>&1 || status=1
wait $first || status=1
echo "--- party 0"; cat "$DIR/p0.out"
echo "--- party 1"; cat "$DIR/p1.out"
[ $status = 0 ] && echo "selftest passed" || { echo "selftest FAILED; logs under $DIR"; exit 1; }
