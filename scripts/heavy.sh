#!/bin/sh
# heavy.sh MAX_GB MAX_SECONDS COMMAND...: run a heavy job under the machine-wide heavy-job lock
# and guarded.py's memory and time limits (REORGANIZATION_PLAN.md section 1, rule 3).
#
# Only for jobs that genuinely conflict: harness runs (shared local server, ports, database
# nodes); builds that replace binaries a harness run uses (`lake build` of an executable or of the
# TlsMpc library, build_hybrid_v3.py, cargo builds of node_daemon or the provision tool); circuit
# lowering and production. Light jobs (`lake env lean ONE_FILE`, lints, read-only scripts,
# `cargo check` in a separate target directory, kernel checks that start no server) never take
# it: plain guarded.py, cap at most 12 GB, any time. Declare a realistic cap (harness runs: 16-20)
# and keep each run short. Only one heavy job runs at a time; a second one waits (its time limit
# not yet running), naming the holder and how long it has held the lock every minute.
#
# The plan names `flock(1)`, which macOS does not ship. The lock is Python's fcntl.flock instead,
# inside guarded.py (`--heavy`); this file only forwards to it. Equivalent:
#   python3 scripts/guarded.py --heavy MAX_GB MAX_SECONDS COMMAND...
exec python3 "$(dirname "$0")/guarded.py" --heavy "$@"
