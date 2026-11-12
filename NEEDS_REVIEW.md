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

**Tested.** `check_signal_service_local.py --recovery ...`: nine stages, all passing in
semi-honest and malicious mode against the local server (stages, results and what they do not
show in `MULTI_DEVICE.md` section 9; 429, 5xx, 404 and bad bundles are injected by a test
proxy); `public_service_controller recovery-check` (29 checks); `bundle-rebind` against a
reference (8 cases). The existing `--db` and `--multi-device` flows pass through the new path.
No cheating-party test.

**Switch.** `SIGNAL_RECOVERY=0` (both nodes) runs the previous send loop, where any such failure
ends the session. The worker's replies stay as described either way.

## 3a. Client profile `libsignal`: what changes for the server and the nodes (2026-11-11, uncommitted)

Switch: `SIGNAL_CLIENT_PROFILE=libsignal` on both nodes and for circuit production (default
`legacy`). Comparison and sources: `handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md`.

**What the nodes learn: nothing new.** Every change is to public bytes the controllers already
build, or to the size of a public length class:
- The ClientHello's session id and client random are two SHA-256 hashes of the joint random
  value (`TlsClient.runWithScalar`). Both nodes knew that value already; an outsider sees two
  unrelated-looking 32-byte values. The ServerHello must now echo the session id.
- Content padding `80k − 1` (`PrivateTextNotification.buildOfficial`, kernel
  `signal-seal-official`, `bundle-seal` with `80k − 1`): the envelope still reveals only the size
  class, now with official boundaries (text length ranges shift down by one byte).
- Message timestamps from the agreed clock at send time (`restamp` in the controller): public to
  both nodes, as before.

**What the server learns that it did not:**
- `psk_key_exchange_modes` is now offered (no PSK is), so a server may send NewSessionTicket; the
  record parser skips post-handshake handshake messages (section 2), untested with tickets
  present (the local terminators send none).
- The authenticated upgrade's username is `uuid.1` (it was `uuid`): the device id, which the
  server knows anyway.
- Nothing that weakens a check: the CertificateVerify scheme must now be one the libsignal
  profile offered (stricter), and no cipher suite or group is offered that we cannot perform.

**Removed under the profile:** the client-initiated TLS KeyUpdate after the first delivered
message (no security role found; please confirm it was only exercising the key-update path), and
the 25 s `/v1/keepalive` request on the receive socket (now a WebSocket ping after 31 s; the pong
is not checked, so a dead connection is noticed only by the next read or by the closing keepalive).

## 3b. Constant-depth curve programs: masked openings and hints (2026-11-11, uncommitted; OFF by default)

Switch: `TLS_WORKER_HINTED=1` on both workers (part of every agreed request; the harness's
`--hinted`). Default 0: the ladders and chains as before, nothing below applies. It is off
because it opens values that were not opened before and differs from the earlier programs on
malformed keys; the owner should decide after review. Numbers: `PERFORMANCE.md`, "Rounds".

**What changed.** Over a link between the nodes every multiplication level of a field program is
a round trip, and the curve programs were long chains: a square root by a 250-step power chain,
a table by 256 successive doublings, a 255-step ladder per key agreement, a 509-step
double-and-add per signature, a 253-step multiplication by the group order. New field programs
(`TlsMpc/EdwardsHinted.lean`; runtime `hinted_points.h`; used by `service_kernels.h` when the
switch is on) compute the same results in a few dozen levels. Two techniques carry the risk:

1. **A square root from an opened masked value** (`liftOpen`, `liftPoint`). For a Montgomery
   coordinate `u`, `q = u(u² + 486662u + 1)`; with a uniform shared `r` (sum of both parties'
   inputs) and a uniform shared bit `b` (XOR of one checked private bit from each party), the
   workers open `w = q·r²·2^b`, take a public root, and get the Edwards point without a power
   chain. Validity of `u` stays a private bit (`sel xor b` for the public "is `w` a square").
2. **Hints, checked.** To get the multiples `16^w·P` of a private point without successive
   doublings, the workers open `Z = P + M_A + M_B` for private uniform points `M_A`, `M_B`, one
   entered by each party; party A then enters `16^w·(Z − M_A)` and party B `16^w·M_B` as private
   inputs (computed locally with libsodium), and the program takes their differences as the
   window bases. It does not trust them: every window computes `16·base_w` itself and the
   workers open (masked) `16·base_w − base_(w+1)`, which must be zero.

**Every value newly opened.** Per lifted point (a contact's stored identity key when it is
prepared; for a first message received: the envelope's ephemeral key, the sender's identity
key, the base key, the ratchet key; for a device refresh: the bundle's identity key, signed
prekey, one-time prekey):

| Opened | When honest | Otherwise |
|---|---|---|
| two bit checks, two curve checks of the parties' own mask contributions | 0 | a party entered a non-bit or a point off the curve: each value is a function of its owner's inputs only; the session stops |
| `w = q·r²·2^b`, after those checks | uniform over the nonzero field elements for every `q ≠ 0`, curve or twist (2 is a non-square, `r²` is a uniform nonzero square) | **0 exactly when `u = 0`** (or `r = 0`): see below |
| `Z = P + M_A + M_B` (`P` is the base point when `u` is invalid) | a uniform point of the curve's whole group (each mask is uniform over the prime-order part and the 8 torsion points: `Ed::random`) | — |
| masked denominators of the additions (`b·r`, as `FieldProgram` already opens) | uniform: the complete addition law has nonzero denominators on curve points, and the lift's `y` denominator is `1 + valid·u` | 0 only if a hint is off the curve: a party's deviation, the session stops |
| the masked links, per table (126 values) | 0 | a wrong hint: uniform nonzero values (each difference times its own mask), the session stops |
| per agreement, the masked denominator of the final quotient | uniform | 0 when the result is the neutral element (a low-order point): as the ladder's quotient already opened |
| a contact's `valid` when it is prepared for sending | 1 | 0: the stored key is not a curve point. The earlier program opened the same fact (its curve check) and ended the session; now it is that contact's status (operation 66 replies 0, a send to it replies 0) |

No longer opened: the server key's Edwards coordinates (they were computed in the engine from a
public value and opened; now each party evaluates the same pinned Lean program in the clear,
`FieldProgram::evaluate_clear`).

**`u = 0`.** The opening is zero exactly for the coordinate 0 (the point of order 2). The
ladder already told both nodes that such a key is of low order (its quotient opens zero for
the five low-order coordinates); this narrows it to `u = 0`. It concerns only a key that a
remote party chose to be 0.

**Where the results differ from the earlier programs** (only on keys no honest client has):
- *Twist points.* The ladder computes RFC 7748's X25519 for any `u`, also one on the twist. The
  new programs work on the curve: for a twist `u`, `valid` is privately 0 and the agreement is
  replaced by a uniform value (so the message or bundle fails its MAC and is refused like any
  other invalid one). libsignal accepts a first message whose ephemeral, identity or ratchet key
  is a twist point (it validates only the base key). **A sender of crafted messages can tell this
  client from libsignal by that.**
- *`u = 0` as a signing key.* The earlier lift called the order-2 point valid; now it is
  invalid, so a bundle under identity key 0 is refused where the signature equation might
  have held. As an agreement input the result is 0, as before.

**Why a hint cannot change a result or leak.** `EdwardsHinted.entries_sound` (Lean, no `sorry`,
axioms `propext` only): if every link holds, the table is the chain computed from `P` alone,
whatever the hints were. Whether a link holds depends only on the hint and on values its
author knows (`Z`, its own mask): A's hint is right exactly when it equals `16^w·(Z − M_A)`;
it cannot be made to pass or fail depending on `P`. The torsion check (`torsionHinted`) opens
nothing: its two outputs go to the receive kernel as before and are zero only if the hinted `Q`
is a curve point with `8Q = P` (the curve check of `Q` is folded in under a uniform mask), which
exists exactly for `P` in the prime-order subgroup.

**To check.**
1. The uniformity claims in the table, in particular that `w` is opened only after the bit and
   curve checks, and that `Z` hides `P` when one party's mask is uniform (including a `P` with a
   torsion component).
2. That every opening is still preceded by the engine's MAC check of what came before
   (`FieldEngine::checked_open`, unchanged), so a tampered earlier value cannot be probed
   through a masked denominator.
3. The public and local arithmetic in C++ (`LocalField`, `Ed` in `hinted_points.h`): conversions
   between libsodium's encoding and affine coordinates, the public square root of `w`, each
   party's own multiples. It touches no shared value.
4. That replacing an invalid point by the base point and carrying `valid` privately leaves no
   path where an invalid key's agreement is used unmasked (`bitSum`: numerator `mask +
   valid·(… − mask)`).
5. The two behaviour differences above: acceptable, or to be removed (a twist-capable program).

**Proved** (`TlsMpc/EdwardsHinted.lean`): the step functions and sums evaluate to the stated
value functions; `entries_sound`, `prepareTable_sound`, `bitTable_sound`; every accepted
compilation computes its program (`compiled_correct`, from `compileAll_correct`). **Not proved**
(as for the earlier programs): that the formulas are the group law, the Montgomery/Edwards map,
the uniformity statements. **Tested:** `hinted_program_checks.py` (every program against
independent Edwards arithmetic, a Montgomery ladder and `cryptography`'s X25519; wrong hints,
non-bits, twist points, `u ∈ {0, 1, −1}`, points with torsion); `rounds_fixture.cpp` (the old
and new programs on the same shared inputs in the two engines, results opened and compared:
nine agreements, a signature point, torsion, tables, an invalid key in a batch); the local
flow with `--hinted`. No cheating-party test in the engines.

**Also new, same date.**
- *Operation 66* (`contactsPrepare`): several contacts' tables in the same field rounds. Its
  reply is one public status per contact (255, 0 = key refused as above, 1 = not loaded).
- *`TLS_WORKER_FIELD_DIRECT=1`* (default 0): the field engine's openings by the library's direct
  protocol (`Direct_MAC_Check`: each party sends its shares to the other at once) instead of the
  indirect one (party 1 to party 0, sums back). One message delay per multiplication round
  instead of two. The opened values and the MAC check are the library's own in both; a reviewer
  should confirm that for two parties the two are equivalent for a deviating party.
- *`Challenge::transfer`* (`dabit_generator.h`; always on): for messages of at most 4 KiB both
  parties now send and then receive, where party 1 used to wait for party 0's bytes before
  sending its own. The bytes are the same (a party's message is fixed before the call). In a
  commit-then-open, the commitments now cross instead of party 1 seeing party 0's first; no
  check relied on that order, but it is a change to how every commitment, request agreement
  and challenge permutation is exchanged.
- **Found on the way, and a check added: a mirrored commitment.** The joint random values
  (`joint_random` in `tls_worker_v3.cpp`: the ClientHello random, upgrade nonces, WebSocket masks,
  **the nonce of every seal of a contact's or the account's stored state**; and the public
  offset of every sealed-sender message in `service_kernels.h`) are the XOR of two values
  exchanged commit-then-open with `SHA256(value)` as the commitment, without the party in it.
  A party that waits for the other's commitment and sends the same bytes back, and then does
  the same with the opening, passes the check and makes the XOR zero. (Before today party 1
  received first by construction; now the short transfers cross, but nothing stops a deviating
  party from waiting.) With a zero offset every message to a contact carries the same ephemeral
  public key; with a repeated state nonce two versions of a contact's state are sealed under
  the same key and nonce. All three sites now refuse a commitment equal to their own
  (`peer_commit != commit`), which closes the copy (a hash commitment cannot be related to
  another in any other way). A reviewer should confirm that, consider putting the party into
  the commitment as `split_ecdh.h` and the offset agreement's `K₀` exchange do, and check
  whether the state seal should also refuse a nonce it has used (`version_ok` refuses only the
  all-ones value).
- *`TLS_WORKER_TEST_LINK_SHIFT`* (test only): the connecting worker dials other ports, where
  `scripts/delay_relay.cpp` adds latency. Not for deployment.
- *Proposed, not implemented:* keeping a contact's table with its stored state
  (`SEALED_SENDER_AGREEMENT.md`, "Keeping the table across sessions"). The cheapest form needs
  a field-engine MAC key that persists across sessions; that is the owner's decision.

## 3c. The registration ceremony: a password made in the engines, one opened value, revealed response bodies (2026-11-11, uncommitted)

Design, who learns what, and what one node can do alone: `CEREMONY.md`. Used only by the
`ceremony` stages (`SIGNAL_CEREMONY`); no send or receive session runs any of it.

**New opened value: `masked` of `ceremony-secrets`** (`TlsMpc/CeremonyKernels.lean`, worker
operation 80). The password is `base64(seed_A ⊕ seed_B)[0..22]`; opened is
`password ⊕ mask_A ⊕ mask_B`, where seed and mask are private inputs each worker draws itself.
From it node A keeps `mask_A ⊕ masked`, node B `mask_B`: XOR shares of the password.
- *Proved* (`TlsMpc/CeremonyProofs.lean`, no `sorry`, standard axioms): `ceremonySecrets_spec`
  (the kernel's three fields are that specification), `masked_hides` (per byte, the opened value
  is a bijection of the other node's mask byte). *Not formalised:* that a uniform mask makes
  `masked` independent of the password; that the password is uniform when one seed is.
- *To check:* that both parties' private inputs to one kernel run are fixed independently in
  the Boolean engine (a node must not choose its seed after learning anything of the other's);
  that the worker's randomness (`emp::PRG` with a fresh seed) is good enough for a long-term
  secret; that the reply of operation 80 (this party's shares) goes only to that party's own
  controller and is not logged (`tls_worker_v3.cpp` logs operation numbers and counts only).

**New sealing kernel: `ceremony-register-ctr`** (operation 81). It writes base64 of (0–2 public
bytes, the password) and base64 of the recovery password into two slots of a frame both
controllers built, and encrypts the TLS record. Like `bundle-fetch-ctr`, it places private
values at offsets the controllers choose, so it is an encryption of the password to the server
at a position of the frame of the caller's choosing.
- *To check:* that nothing but the TLS record leaves (the plaintext is not an output:
  `registerPlaintext_spec` says what it is; outputs are `header`, `ciphertext`, the private
  `pad`); that the worker accepts the operation once per session and only on a frame both
  workers were handed (`agree`); that the server on the other end is the authenticated one (the
  handshake's certificate check, as for every authenticated upgrade, which sends the same
  password). The slots are checked not to overlap and to lie in the payload (`slotsOk`).
- The base64 split (public prefix by the controllers, the rest in the engine) is checked at run
  time on the number in use (`Ceremony.basicConsistent`), not proved for all numbers.

**Reveal policy: `PublicReceive.State.openBody`.** With it a response's body (field 4) is
revealed like its other fields (`replyScan`, `replyBudget` take an `inline` flag; `replyBody`
extracts it). Default false: every existing session is as before, and no response body of a
send or receive session is revealed. It is set in one place, the ceremony branch of
`PublicServiceController.lean`, where the bodies are a verification session, the registration
response and our own sender certificate. A server request's body (a delivered message) is not
affected: that path is separate and unchanged.
- *To check:* that no path sets `openBody` outside the ceremony; that on the ceremony's
  authenticated socket a delivered message is still passed over (it is: `scan` / `stepSkipped`).

**What both nodes newly see** (public by the owner's scope): the captcha token, the SMS code,
the verification-session id, the registration and certificate responses, and every account key
(generated in the clear by one node and sent to the other over the workers' link, operation 39).

**Known weaknesses, stated in `CEREMONY.md` section 4, for the owner to decide:** a verified
session id lets either node register the number alone with a password of its own while the
server keeps the session; the identity private key in the clear lets a node that colludes with
the Signal server open the sealed-sender layer of signups (the earlier split kept it shared).

**Tested.** `check_signal_service_local.py MODE --runs 0 --ceremony` (CEREMONY.md section 7).
No cheating-party test.

## 3d. The long-lived send session and the workers' bounded wait (2026-11-11, uncommitted)

**What changed.** A send session no longer ends after one notify (`PublicServiceController.lean`,
`serve`, `loadJob`, `deliverJob`; `node_daemon/` README, "The long-lived send session"). It
keeps its connections, the contacts it loaded and their per-session preparation, and takes one
notify after another from its daemon. The workers now give up on each other at the start of a
request after `TLS_WORKER_PEER_WAIT` seconds (`tls_worker_v3.cpp`, `await_peer`; default 180).

**To check.**
1. *A contact kept loaded across notifies.* Each job reads its ids from the database nodes under
   its own signed request (the parity check between the parties as before). A contact the
   engines already hold is NOT reloaded when the version the nodes return equals the version
   this session last stored (`versions`). Then the engines hold either exactly that stored state,
   or (after a store the nodes did not acknowledge) a state one sealed message further on: a gap
   in the counter, never a message key used twice, as within one session before. Any other
   version: evicted and loaded from the blob. Check that no path lets a job use state the nodes'
   current version does not describe in a way that could reuse a key (in particular, two pairs
   of nodes, or a session started while another still runs, writing the same contact: today
   prevented only by running one send session per node pair; PRODUCT_TODO section 7).
2. *Write authority per job.* `storeSoft`, `storeAdvanced` and `commitScratch` take the request
   of the job being served (`requestFile`) instead of `SIGNAL_DB_REQUEST`. The nodes accept a
   write-back only under a request that read that id (unchanged rule); check that a job can never
   write under another job's request.
3. *The tick.* Between jobs the two controllers exchange, through operation 39: the SHA-256 of the
   name of the job each holds (the request digest, already known to both daemons), one bit "end
   the session", and their clocks. Nothing secret; a job runs only when both hold the same one.
4. *What the Signal server sees now.* One unauthenticated connection (or one per Tor circuit)
   stays open for hours and carries many notifies, with a WebSocket ping (libsignal profile) or a
   keepalive request every 25 s while idle. **The server can now link the recipients of
   different notifies sent on the same connection**, where before each notify was a new
   connection (it could already link them by source address and timing; with Tor circuits a
   long-lived session keeps the same circuits too, since the SOCKS credentials are per session).
   Owner's decision: rotate connections per notify (a handshake each, about 1.5 to 2.6 s and
   3 to 4.5M AND gates per connection), per N messages (`send_session.max_messages`), or accept.
5. *The bounded wait.* A liveness change only: the first 32-byte exchange of each request now
   polls the socket with a deadline before reading (bytes already buffered skip the wait); the
   bytes on the wire are unchanged. A party could always end a session by closing its link; now a
   silent one ends it too. Check the default (180 s) against the longest legitimate gap between two
   requests of one controller (a database client call, a back-off both sleep, a proxy connect).
6. *Private buffers dropped* (`tls_worker_v3.cpp`, operations 12 and 13). A buffer sealed into a
   record is erased right after sealing; of the received records only the newest 64 are kept. A
   handle used after it was dropped is unknown and fails the request (never another buffer: handles
   are never reused). Check that no path seals a buffer twice or reads a record's handle after 64
   later records (the controller reads each record completely before the next; envelope and bundle
   takes copy what they keep). This frees memory only; it is not erasure.

**Tested.** `check_signal_service_local.py --runs 0 --app` (notifies in one session; a
controller killed in the middle of a notify, the next session resuming from the journals),
`--sustained N --restart-after M` (a planned restart between notifies: every recipient gets every
text exactly once), `--recovery hang` (a controller stopped: the other party ends within the wait,
with that reason). Results: PERFORMANCE.md, "The long-lived send session".

## 3e. First real test: Android signup layouts, provisional ids, send-time stamps (2026-11-12, uncommitted)

**What changed.**
1. `ReceiveFirst.withAccessKey` (kernel `receive-access-key CERT CIPHERTEXT OFFSET`, same name and
   inputs): the contact's profile key no longer has to follow the message body directly. Between
   them it accepts one of 72 layouts (`ReceiveFirst.gaps`: `flags`, `expireTimer`,
   `expireTimerVersion`, each absent or a varint of 1..2 / 1..5 / 1..3 bytes, in that order,
   which is Signal-Android's Wire declaration order and also covers tag order). One mask per
   layout is computed in the circuit, the key is the XOR of the masked candidates, and the opened
   status is "some layout matched" (before: "the empty layout matched"). OFFSET (body start +
   body length) is public as before: the body and its length are opened by `receive-text`.
   About 28k AND gates (one AES-256 key schedule and block plus the masks), once per signup.
2. The controller gives each opened message its own provisional id (2^128 − 1, then
   2^128 − 3, 2^128 − 4, …), so a signup refused after its session was made (bad token) no longer
   leaves an entry under the one provisional id that blocks the next signup (REAL_TEST_PLAN B6b).
   The worker still keeps evicted entries; nothing in the worker changed.
3. The libsignal profile's `restamp` prepares the contact (operation 66, the same work its first
   seal did) before taking the timestamp, so the message is stamped just before it is sealed.

**To check.**
1. *Nothing new opened.* The status byte of `receive-access-key` is opened as before; its meaning
   widened from one layout to 72. A refused signup still shows only "no layout matched" (no
   profile key, or an unknown field between body and key). Check that the masks are mutually
   exclusive (two layouts first differ in a tag byte, `20`/`28`/`B8 01`/`32`, or in a varint
   continuation bit), so the XOR selection cannot combine two candidates.
2. *Provisional ids.* Both controllers count opened messages in the same order (they process the
   same envelopes in lockstep). An application id equal to a provisional id of an earlier refusal
   in the same session is refused by the worker (`contactAssign` to an existing id): harmless,
   application ids are signed by the application and 2^-96-unlikely to collide.
3. *Timing.* The stamp is now taken after the contact's preparation; the server sees a message
   whose timestamp is the time of sealing (seconds old with the database write) instead of tens
   of seconds old.

**Switch off.** Revert the three hunks (`ReceiveFirst.lean` `gaps`/`withAccessKey`;
`PublicServiceController.lean` `provisionals` and the `contactsPrepare` call in `restamp`).

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
