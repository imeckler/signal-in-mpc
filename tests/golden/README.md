# Golden records (REORGANIZATION_PLAN.md, test set D)

Masked `SIGNAL_RECORD` files of local harness runs: what each controller sent to the (local)
Signal server and which bytes of the server's records it revealed or withheld. A later stage's
run must compare equal to these (`scripts/compare_records.py`), modulo the masks listed in that
script's docstring.

| Directory | Harness command (`local_signal_server/check_signal_service_local.py`) |
|---|---|
| `malicious-runs2-signup/` | `malicious --runs 2 --signup --record DIR` |
| `malicious-db/` | `malicious --runs 0 --db --record DIR` |
| `semi-honest-runs2-signup/` | `semi-honest --runs 2 --signup --record DIR` |
| `semi-honest-db/` | `semi-honest --runs 0 --db --record DIR` |

Made with `compare_records.py --mask DIR tests/golden/NAME` from the run's `--record` directory.
Compare a new run with `compare_records.py tests/golden/NAME NEW_DIR`.

Regenerated 2026-11-12 on the tree at the end of stage S2 (after the device-refresh change), and the
semi-honest pair added. Before regenerating, the new malicious runs compared equal to the previous
golden set (`malicious-runs2-signup` all sessions; `malicious-db` all but the artefact below).

**Known false difference (slot widths).** A private slot appears in the masked template as
`<slot N>`, found as a run of zero bytes in the masked frame. When the WebSocket mask byte at a
slot's neighbouring text byte equals that byte (probability 1/256 per slot edge; a `--db` run has
about a hundred edges, so roughly one run in three), the masked byte is 0 and the slot shows one
byte wider (e.g. `<slot 25>` after `unidentified-access-key:` instead of `: ` + `<slot 24>`). The
frame itself is correct. The golden sets were chosen without such a slot (widths 36, 24, 3, 10
only); a comparison failing only this way is not a behaviour change.
