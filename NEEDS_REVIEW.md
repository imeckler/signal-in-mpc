# Needs review

Changes that touch a security-critical component and should be read by someone qualified before
they are relied on. Each entry says what changed, why, what to check, and how to switch it off.
Nothing here is known to be wrong.

## 1. Triples produced ahead of use (2026-11-11, commit 2c83176)

**What changed.** Both engines used to produce their multiplication triples inside the operation
that consumed them. They are now produced ahead of use by background generators of the same
session and taken from a stock.

- **Boolean engine (authenticated garbling).** The validated engine's `compute_inplace` was split:
  its function-independent part (triple generation, steps 1–2 in `TRIPLE_POOL_AUDIT.md`) is now
  `TriplePool::mint`, and a circuit run takes triples from a stock instead of minting its own.
  Extra "factories" are further `TriplePool`s of the same session: the **same Delta**, their own
  two channels, their own correlated-OT sessions, and their own counter range for digest tags
  and hash-tweak seeds. Files: `handshake_backend/EmpHybridWork/dyn_session.h` (`TripleStock`),
  `prepare_validation_v3.py` (regenerates the engine tree and `emp-ag2pc-validated-v3.patch`),
  `tls_worker_v3.cpp`.
- **Field engine (MASCOT).** Each generator line is a second `ProtocolSet` of the same engine on
  its own connection, running the library's own triple generator; multiplication takes triples
  from the stock. Files: `field_engine.cpp` (`FieldTripleStock`), `field_engine.h`,
  `field_program.h`.

**Why.** Triple generation was 74% of Boolean circuit time and almost all field-engine time. A
steady-state send went from 2.42 s to 0.97 s (malicious, localhost).

**What to check.**
1. Reusing one Delta across several pools with separate correlated-OT sessions: that the pools'
   outputs are jointly as good as one pool's, and that the separate counter ranges really make
   every hash tweak and digest tag unique across pools.
2. **Bucket size.** Factories mint batches of 2^19 with bucket size 8, "by the same rule as
   before from the batch length". Small circuits previously got buckets of 9 to 40 because
   their batches were small. Confirm that 8 at this batch size meets the statistical-128 target,
   and that a short final batch cannot get a smaller bucket than its length requires.
3. That a triple is used exactly once and in the same order by both parties, including when the
   stock runs dry mid-circuit, on abort, and at shutdown (the "staying in step" rule in
   `PERFORMANCE.md`: batch k starts when both sides have announced it).
4. That nothing about the triples depends on the circuit they end up in (so producing them
   before the circuit is known gives a cheating party no new choice), and that a party cannot
   bias which triples a given gate receives by timing its announcements.
5. For the field engine: that a second `ProtocolSet` shares the MAC key correctly and its
   triples pass the same sacrifice/MAC checks as before; that the opened-values check at the end
   of a session still covers every multiplication.
6. The split of `compute_inplace`: a line-by-line comparison with the validated v3 engine, since
   "moved without change" is the claim everything rests on.

**Tested so far.** Every pinned circuit of `check_lean_runs.py` through the fixture with triples
from two factories, with right and wrong expectations; a clean exit; the full local Signal flow
in both modes. Not rerun as wholes after the change: `check_validation.py`,
`check_tls_worker_v3.py`.

**Switch off.** `TLS_WORKER_TRIPLE_STOCK=0` and `TLS_WORKER_FIELD_STOCK=0` restore producing
triples inside each operation. Both workers must be configured alike (the settings are part of
every agreed request).

## 2. Implemented (2026-11-11): the record type is opened before a TLS record is scanned

**What changed.** Most of the AND gates of opening a received record were a scan that looks for
post-handshake handshake messages (key update, session ticket) in every record, although almost
every record is application data. The owner decided to open one bit first, "this record
authenticated and is a handshake record", and scan only when it is set. Two new kernels
(`TlsMpc/TypedOpenKernels.lean`), in the same size classes as `tls-open-application-class`,
which stays:
- `tls-open-typed CAP` decrypts and parses the record once, opens the bit, and gives the result
  for a record that is not a handshake record;
- `tls-frame CAP` runs only when the bit is set, on the first kernel's private parse.

AND gates, old → new: a 2.7 KB record (class 3072) 2.87M → 1.14M; a 150-byte record (class 160)
132K → 53K. A handshake record costs both kernels (2.91M; 135K). The saving is smaller than the
0.8M first estimated: AES-CTR and the inner-plaintext parse are about 370 gates per byte.

**What the nodes newly learn.** Before, a record gave one of five outcomes: rejected,
application data, control message skipped, key update, close. Now also, per record, one bit:
- for a record that **fails authentication**, whatever its bytes: nothing; the bit is 0 and the
  outcome is "rejected", as before;
- for an **authenticated** record: whether its inner type is handshake. This separates a
  skipped handshake record (session ticket, fragment) from an ignored **`user_canceled` alert**
  (both were "control message skipped"), and, among authenticated records the parser then
  **rejects** (malformed handshake message, an alert of another kind, any record after an
  earlier error), the handshake records from the others. Nothing about contents, lengths or
  contacts.

**The risk, and what is proved** (`TlsMpc/TypedOpenProofs.lean`; no `sorry`, no new axioms). The
node that owns the socket chooses what bytes reach the engines, and AES-GCM without its tag check
is malleable, so a bit of decrypted content opened for an unauthenticated record would let that
node read plaintext one bit per attempt.
- *Gating.* `rejected_parse`: with the private tag-check result 0, every byte of the parse is
  zero, for every record, header, length field and key. `tlsOpenTyped_gated`: under every
  assignment of the kernel's inputs with `accepted` = 0, the fields it may open are `[0]` (the
  bit) and `[0, 0]` (the event). `rejected_independent`: the whole parse, so every private
  output too, is the same for any two records of one size.
- *Refinement.* `typed_pair_refines`: the bit is 0 or 255; when 0, the first kernel's event,
  parser state, length and content are those of `tls-open-application-class` on the same
  inputs; `tls-frame` on the same parser state and the first kernel's parse gives exactly those
  four fields (so also when the bit is 255).
- Existing theorems are untouched.

**Not proved, for a reviewer.** The worker's sequencing (`tls_kernels.h`, `open_application`:
which kernel's fields are opened and kept for which bit) is C++, checked by
`check_typed_open.py` (real AES-GCM records of every kind and tampered copies, both paths
compared field by field with the existing kernel) and by the local flow. That `accepted` is the
tag check's result is `gcm-check`, as before.

**Switch.** `TLS_WORKER_TYPED_OPEN=0` restores scanning every record. Both workers must be
configured alike (the setting is part of every agreed request). A pinned deployment needs
`typed_records=1` in its circuit inventory.

## 3. Recovery: refusals that no longer end the session, and one new opened byte (2026-11-11)

**What changed.** A failure that concerns one contact used to end the two-party session (the
worker became terminal). It is now that contact's result and the session carries on
(`PublicServiceController.lean`, `Recovery` and `deliver`; `service_kernels.h`;
`tls_worker_v3.cpp`; `MULTI_DEVICE.md` section 9). What a reviewer should check is that nothing
is learned, by either node or by the server, that was not learned before, and that continuing
after a refusal gives a cheating node no new lever.

**Statuses that became non-fatal, and what each shows.** Every one of them is a value that was
already public; before, the same value was visible as "the session ended here".

| Where | Status both nodes see | Was |
|---|---|---|
| `contactSend` (41), `devicesSend` (61) | reply `0`: the seal kernel's gated `status` output was not 255, or Lean has no kernel for the opened counter widths | fatal `private send rejected` |
| `contactOpen` (37), `devicesOpen` (63) | reply `0`: the `accepted` output of `contact-open` (the key check of the stored blob) was not 255 | fatal `contact key does not match` |
| `bundleEstablish` (60) | step 8: the session's one status byte (as before); layout refused by Lean: `0` (as before) | the controllers ended the session |
| `pollRecord` (17) | reply `[0]`: the leader's socket to the server was closed (by the server or the proxy) | fatal `server closed` |
| responses | status and headers of a response (`Retry-After` among them), never its body | 2xx required, else fatal |

Still fatal: any engine failure or MAC check, a request the two workers were not handed
identically, a TLS record that does not authenticate or a fatal alert, a failed handshake, a
commitment that does not open, a width flag or shape that is not what Lean declares, the
database client failing on a read.

**To check.**
1. *Selective failure.* The node that owns the socket can make any contact's send fail (drop
   the connection, withhold a record) and now sees the session continue with the others. It
   could always do this one session at a time; confirm that which contacts go on to succeed
   gives it nothing about them beyond what a response status already gives.
2. *Resend after a lost connection* (owner's decision: resend, accept a duplicate). The resend
   is a new seal under the next message keys; the state was stored on the database nodes before
   the first copy left (`storeSoft`). Confirm no path sends two different ciphertexts under one
   message key: `sendSoft` always seals again, and a seal always advances the record.
   The socket owner can force any number of duplicates up to the bound (2 reconnects per
   message); it cannot read them.
3. *`Retry-After`.* No reveal-policy change: a response's headers were always revealed
   (`replyBudget`: only field 4, the body, is passed over). `retryAfterOf` only reads them. The
   wait it causes is bounded (60 s; a longer one gives the contact up for this session). A server
   can use it to delay, not to learn.
4. *Operation 91 (`resetConnection`).* Replaces the selected connection's socket, TLS secrets
   and WebSocket state by fresh ones; allowed only after 17 reported that connection closed.
   Check that nothing of the old connection's secrets is reused (a new handshake follows) and
   that private buffers received on the old connection cannot be confused with the new one's.
5. *Operation 10 no longer fails on a closed socket* (the write is dropped; the next poll
   reports the closure to both). Only the leader could see the write fail, so failing there
   would have let the two workers diverge.

**New opened byte: `changed` of `bundle-rebind`** (`TlsMpc/BundleKernels.lean`,
`BundleResponse.rebind`). Owner's decision: a contact whose identity key changed (registered
again) is accepted automatically and reported. `bundle-bind` required the bundle's identity key
to equal the stored one; `bundle-rebind` does not, and opens whether it differed.
- *Proved* (`TlsMpc/BundleProofs.lean`, no `sorry`, standard axioms): `bundleRebind_spec` (the
  kernel is `BundleResponse.rebind` on its inputs) and `rebind_rejects` (when the check is 0 —
  the bundle did not parse, a signature did not verify, the record is not live — every output is
  zero, the opened byte included). Tested against a reference: `check_bundle_kernels.py`, case
  `rebind`.
- *What the nodes learn:* that this contact's identity key changed, when the next send to it is
  refreshed. A node can compare that time with when a person it suspects re-registered (it can
  fetch anyone's bundle), as it already can for device changes (`MULTI_DEVICE.md` section 1,
  "not avoidable"). The result is reported to the application per id in any case.
- *What it trusts:* the signatures are checked under the identity key that the same response
  carries. A server that answers the prekey fetch with a bundle under a key of its own gets it
  accepted, and the next messages to that contact are encrypted to the server. Before, such a
  bundle failed the refresh. This is the cost of accepting identity changes without a human
  comparing safety numbers; the per-id result "delivered after identity change" is the only
  signal. The owner should confirm this is the intended trade.
- Not in the worker's reply: why an establishment failed (still one status byte).

**Scratch, then commit.** A refresh's new device list no longer replaces the contact's state in
the engines when the last device verifies; it is held aside (`Establishing` in
`service_kernels.h`), sealed (64), written to the database nodes, and committed (65) only when
both parties saw the nodes acknowledge it. Check that no send can use the scratch before the
commit and that a dropped scratch leaves nothing behind.

**What "confirmed" rests on.** Each computation node appends settled results to a local
journal; a later session for the same notify skips an entry only if both nodes' journals have
it. Entries are public values. A node that lies or loses its journal can cause a duplicate or
(by claiming nothing) a full resend; it cannot make a message be skipped alone.

**Tested.** `check_signal_service_local.py --recovery ...` (stages and results in
`MULTI_DEVICE.md` section 9); `public_service_controller recovery-check`. No cheating-party
test.

**Switch.** `SIGNAL_RECOVERY=0` (both nodes) runs the previous send loop, where any such failure
ends the session. The worker's replies stay as described either way.

## 4. Also waiting for a reviewer (pointers)

- Bit pairs for Boolean-to-field conversion on the runtime-sized layer
  (`dyn_word_mask.h`, `generate_masks` with `bit_blocks`): a port of the reviewed fixed-size
  construction; no cheating-party tests on this layer yet.
- The controllers' reveal policy (`PublicReceive.budget`, `mayReveal`, `replyBudget`): the claim
  that no request body, unknown message or response body is ever revealed is argued in
  comments, not proved.
- Kyber encapsulation (`TlsMpc/Signal/MlKemFast.lean`): the sampler's compaction network at full
  size and the bit-list encodings are tested, not proved.
- Multi-device state: the per-device "kind" stored beside the sealed state is not
  authenticated (harmless while every linked-device entry is an unanswered session).
- `secret-shared-db`, branch `two-party-handoff-signup-tool`: write-back under an expired
  request, delete, and the account row are new node rules with their reasoning in
  `docs/two-party-handoff.md`.
