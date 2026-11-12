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

**Slot widths (fixed 2026-11-12).** A private slot appears in the masked template as
`<slot N>`. A slot is zero bytes on the wire, but so is a neighbouring text byte that happens to
equal its WebSocket mask byte (probability 1/256 per slot edge; a `--db` run has about a hundred
edges, so roughly one run in three). `compare_records.py` used to take the whole zero run as the
slot, so such a run showed `<slot 25>` after `unidentified-access-key:` (or `<slot 37>` after
`/v1/messages/`) and failed against these files although the frame was correct. It now takes
slot extents from the request builders (`TlsMpc/Node/Policy/Request.lean`; `KNOWN_SLOTS` and
`template_slots` in the script): the unmasked text before the slot must end with the slot's
prefix (`/v1/messages/`, `/v2/keys/` 36, `unidentified-access-key: ` 24,
`"destinationDeviceId":` 3, `"destinationRegistrationId":` 10), the slot is exactly that wide,
and leftover zero bytes are text (they unmask to the right character). The raw runs that showed
the artefact (`malicious --db`, `semi-honest --db`, one each) now compare equal to these files;
`.deps/lowering-scratch/test_compare_records.py` has a synthetic regression case. A zero run that
follows no known prefix is still taken whole, so a new slot kind must be added to `KNOWN_SLOTS`.
The golden files themselves were not regenerated (none contained the artefact).
