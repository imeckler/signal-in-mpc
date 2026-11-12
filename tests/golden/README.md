# Golden records (REORGANIZATION_PLAN.md, test set D)

Masked `SIGNAL_RECORD` files of local harness runs: what each controller sent to the (local)
Signal server and which bytes of the server's records it revealed or withheld. A later stage's
run must compare equal to these (`scripts/compare_records.py`), modulo the masks listed in that
script's docstring.

| Directory | Harness command (`local_signal_server/check_signal_service_local.py`) |
|---|---|
| `malicious-runs2-signup/` | `malicious --runs 2 --signup --record DIR` |
| `malicious-db/` | `malicious --runs 0 --db --record DIR` |

Made with `compare_records.py --mask DIR tests/golden/NAME` from the run's `--record` directory.
Compare a new run with `compare_records.py tests/golden/NAME NEW_DIR`.

Recorded 2026-11-12 on the tree of `5170711` plus the S0 working-tree changes, before the
device-refresh change (`SIGNAL_BUNDLE_SLOTS`, operation 60's tail) landed; regenerate both after
it, and add the semi-honest pair (`semi-honest …`, same arguments) once the local server runs.
