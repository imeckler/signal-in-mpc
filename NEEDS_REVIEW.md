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

## 2. Proposed, not done: reveal the record type before opening a TLS record

**Proposal.** 640 of the 935 AND gates per received byte are a scan that looks for
post-handshake handshake messages (key update, session ticket) in every record, although almost
every record is application data. Opening one bit, "this is a handshake record", first would
let application records skip the scan: a 2.7 KB record would cost about 0.8M AND gates instead
of 2.53M.

**What the nodes would newly learn.** Today a record yields only one of five outcomes: rejected,
application data, control message skipped, key update, close. With the bit opened first they
would also learn:
- for a record that is then **rejected**, whether it presented itself as a handshake record;
- for a **`user_canceled` alert** (which TLS says to ignore), that it was an alert and not a
  handshake message; today both show only as "control message skipped".

**The risk to rule out.** The node that owns the socket chooses what bytes reach the engines. If
the bit were opened for a record that fails authentication, that node could feed altered copies
of genuine records and read one bit of decrypted content per attempt. So the bit must be forced
to zero unless the record authenticates; then it only ever describes genuine server records.
With that, what remains is the alert-versus-handshake distinction above, which says nothing
about contacts.

**Status.** Not implemented. Needs the owner's decision and, if taken, a proof that the opened
bit is zero for every record that fails authentication.

## 3. Also waiting for a reviewer (pointers)

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
