# Architecture and security of the two-party Signal client

This document describes branch `two-party-hybrid-worker` at commit `30c2ce3` (2026-11-13). It
explains what the system does, how it is built, and the argument for its security, link by link,
with the theorems each link rests on. The aim is that a careful reader finishes knowing exactly
what is **proved**, what is **assumed**, and what is only **tested**, and can see how the pieces
fit.

Sources: `REORGANIZATION_PLAN.md`, `STACK_NOTES.md`, `PROOF_GAPS.md` (the authoritative list of what
is not proved), `TlsMpc/Security.lean` (every theorem the argument uses, restated in one file),
`SECURITY_AXIOMS.txt`, `NEEDS_REVIEW.md`, `S10_NOTES.md` … `S16_NOTES.md`, `CEREMONY.md`,
`FIELD_PROGRAMS_V3.md`, `STOCK.md`, `ROTATION.md`, `PERFORMANCE.md`, `NETWORKING_FINDINGS.md`,
`PRODUCT_TODO.md`, `real_signal/REAL_TEST_PLAN.md`, `proofs/README.md`,
`proofs/TlsMpcProofs/SecurityMathlib.lean`, `scripts/lint_node.py`, `scripts/check_axioms.py`,
`tests/golden/README.md`. Where this document and `PROOF_GAPS.md` disagree, `PROOF_GAPS.md` wins.

**How theorems are cited.** A name in backticks such as `receivePolicy_t1_all` is a theorem of
`TlsMpc/Security.lean` (namespace `TlsMpc.Security`). Each one there is a word-for-word restatement
proved by direct reference to the original (`theorem X : <statement> := Original.name`), so renaming
or weakening the original breaks the build. Where the original's name differs and matters it is
given in parentheses. Names marked **(proofs/)** are in the Mathlib package
`proofs/TlsMpcProofs/SecurityMathlib.lean`, which nothing executable imports. Names marked
**(branch)** are proved on an unmerged branch (section 3d.8) and are not part of the main line.

---

## 0. Summary

1. **Goal.** Neither of the two computation nodes alone learns the **contact list** (which Signal
   accounts the service talks to). The adversary corrupts one node, maliciously; statistical
   security is 128 bits; semi-honest is a switchable mode.
2. **Shape.** A Lean controller on each node drives a two-party session. Everything secret is
   computed inside two MPC engines (a Boolean engine and a field engine over p = 2²⁵⁵ − 19). The
   circuits and field programs are written in Lean and compiled from Lean. The per-operation
   logic runs either as C++ inside the worker (the **legacy path, still the default**) or as Lean
   scripts interpreted by the Rust worker (the **script path**, selectable, at near parity).
3. **What is proved**, with only the standard axioms (783 restated theorems in
   `TlsMpc/Security.lean`; 136 more in `proofs/`): what the controller reveals of the server's
   bytes (T1); that the request frames the controllers build in the clear do not depend on the
   contact; the send/store/commit ordering (ORD-1, ORD-2) and agreed results (T11); that the
   lowering and printing of circuits is sound; that each kernel computes its Lean specification;
   for the script path, what each operation opens against any adversary (T3) and, for most flows,
   what honest runs compute (T4); the cut-and-choose bound, hiding of the masked openings, and
   the curve mathematics.
4. **What is assumed**: the MPC engines and their C++; the Rust worker and its pipe; the Lean
   compiler; the engines' loaders parsing files as Lean's parsers do; the I/O glue of the script
   backends; RFC and libsignal transcriptions; SHA-256 commitments as ideal commitments.
5. **What is not proved at all**: there is **no end-to-end theorem** ("one corrupted node plus the
   server learn nothing about the contact list beyond the reveal list", with a simulator;
   PROOF_GAPS A7). The argument is a chain of per-component theorems plus stated assumptions.
6. **On the default path** (legacy C++ flows) the per-flow disclosure theorems (T3) do **not**
   apply: the openings there are bounded by the kernels' open marks and specifications, and the C++
   sequencing is trusted (PROOF_GAPS A2, F5). The controller-level theorems (T1, T8, ORD-1, ORD-2,
   T11) and the kernel theorems apply to both paths.

---

## 1. What the system does, and the security goal

### 1.1 The product

An application server calls `notify(ids, message)` to send a text (at least 200 bytes, by
decision) to thousands of contacts, and `delete(ids)` to forget contacts. Contacts are keyed by
application ids (u128). People sign up by sending the service's Signal account a **sealed-sender**
Signal message whose text is a fixed-width signup token; the token names the id the new contact
gets. No read or delivery receipts are ever sent (they de-anonymise through timing). Each contact's
key shares and sealed state live on **five secret-shared database nodes** (a separate project,
`secret-shared-db`). Two **computation nodes**, intended to run with different providers in
different jurisdictions and connected by WireGuard, jointly run a Signal client — TLS 1.3, the
WebSocket, sealed sender, PQXDH and the Signal ratchets — inside two-party computation.

### 1.2 The security goal

**What must stay secret: the contact list.** In the owner's words (2026-11-10): "we're just trying
to protect the list of contacts". That means anything that identifies a contact: service UUIDs,
contacts' identity, base, ratchet and prekey public keys, access keys, per-contact registration and
device metadata, sender certificates and sender fields of incoming envelopes, every session key
derived from a contact's keys, and every incoming envelope ciphertext.

**What is secret-shared besides that.** The account **password** and the registration recovery
password are made inside the engines and exist only as XOR shares, one per node (`CEREMONY.md`
section 1), so neither node can open the authenticated socket and fetch the account's incoming
messages alone. The account's **private keys are in the clear on both nodes**, by the owner's
decision of 2026-11-11 ("it's actually fine if the private keys are in the clear. it's just the
password that needs to be kept secret shared"): identity key, signed prekeys, one-time prekeys and
Kyber keys. ML-KEM decapsulation therefore runs outside the engines. (An earlier split kept the
identity key shared; `CEREMONY.md` records that it was dropped and what that costs: section 1.3.)

**From whom.** From **each computation node alone**, under a **malicious** adversary that corrupts
one of the two nodes (arbitrary deviation, aborts at any point), with **statistical security 128**.
Semi-honest mode is a separate, explicitly selected build (`tls-worker-sh`, node_worker `sh-v3`).
From **the network**: everything to the Signal server is inside TLS 1.3, which only the engines can
key; the link between the nodes is WireGuard. The **database nodes** hold contact key shares and
sealed state; their own guarantee (threshold secret sharing among n nodes with threshold t,
per that project's description) is outside this repository (PROOF_GAPS A6). What this repository
relies on from them: the key shares they deal, the parity check on reads (trusted, designed
public), signed requests from the application.

### 1.3 Not a goal, or not hidden

* **The Signal server learns each send's destination.** Sealed sender hides the sender, not the
  recipient. The server sees every recipient of a broadcast, arriving as a burst over one
  connection from one IP — the same IP as the account's authenticated socket — so it can link a
  broadcast's recipients by traffic analysis. Sending through a proxy is noted as future work, not
  built. Each send is per recipient (multi-recipient send would link all recipients explicitly).
* **A node colluding with the Signal server.** With the identity private key in the clear, such a
  node can open the sealed-sender layer of envelopes addressed to the account and so read **who
  signs up** (`CEREMONY.md` section 4). This is an open owner's decision (accept; erase the key on
  both nodes after setup; or generate it jointly).
* **Registration authority.** Both nodes see the SMS code and the verification-session id, so
  either node can re-register the number alone while the session lives (`CEREMONY.md` section 4,
  fix designed, not built).
* **Timing, lengths and counts.** The policy treats as public: server framing, request ids,
  timestamps, lengths, statuses and the message text. Lengths can carry per-contact metadata:
  the first real run's notes infer a contact's device count from the length of a 409 body
  (`real_signal/REAL_TEST_PLAN.md` section 0). No theorem bounds what lengths and timing reveal.
* **The one-byte allowance.** The reveal policy can reveal the byte right after the first
  malformed byte (by design; PROOF_GAPS D2).
* **Distinguishability from real clients.** The client speaks HTTP/1.1 to `chat.signal.org` while
  claiming a libsignal version that never does; "the server can single us out with one log line"
  (`NETWORKING_FINDINGS.md` B.3). ClientHello parity is partial (section D there). The official
  client reference is derived from source, not from a capture (PROOF_GAPS J3, the second J3).
* **Availability.** Either node can stop a session at any time. The goal is privacy, not liveness.
* **The application** knows its ids and texts; it is not an adversary in this model.

---

## 2. Architecture

### 2.1 Components and where they run

```
          application server
                 │  signed notify(ids, text) / delete(ids)          (one per node)
   ┌─────────────┴───────────── node A ──────────┐      ┌──────── node B ───────────┐
   │ node_daemon (Rust): jobs, peer channel       │◄────►│ node_daemon               │
   │   │ spawns                                   │      │   │                       │
   │ controller (Lean, TlsMpc/Node)               │◄────►│ controller                │
   │   Session/* Policy/* Flows/* Reveal Channels │ peer │                           │
   │   │ pipe: agreed instruction batches         │ msgs │   │                       │
   │ node_worker (Rust shell)                     │◄────►│ node_worker               │
   │   pipe, agree, link, loader, handles,        │ link │                           │
   │   interp, program, server(socket), socks     │      │                           │
   │   │ C ABI (handles only)                     │      │   │                       │
   │ C++ engines: emp-ag2pc (Boolean, malicious   │◄════►│ C++ engines               │
   │ authenticated garbling) + MP-SPDZ-based      │engine│                           │
   │ field engine (MASCOT) over 2^255-19;         │ chan.│                           │
   │ legacy library (legacy_dispatch) [default]   │      │                           │
   └───────┬────────────────────┬─────────────────┘      └───────┬───────────────────┘
           │ TLS 1.3 (leader's   │ handoff_client                 │
           │ socket; follower    │                                │
           │ gets the records)   ▼                                ▼
     Signal server        five database nodes (secret-shared-db)
```

| Component | Language | Role | Why that language |
|---|---|---|---|
| Circuits (kernels) and field programs | Lean, lowered to flat gate lists / V3 programs | Everything computed on secrets: AES, SHA-256, GHASH, TLS key schedule, Signal ratchets, sealed sender, ML-KEM encapsulation, X25519, XEdDSA, the parsers of private data | Specified and proved in Lean; the lowering is proved sound, so the file the engine loads is the term that was proved about (section 3c) |
| Controller (`TlsMpc/Node`) | Lean | Drives the session: settings agreement, connections, the reveal policy over server bytes, request templates, ordering of store and send, results | Its decisions are what the ordering and reveal-policy theorems are about; I/O is confined to one file (`Channels.lean`) |
| Flow scripts (`TlsMpc/Node/Flows/*`) | Lean, interpreted by node_worker | Each worker operation as a script over a small instruction set (input, run kernel, run program, plumb, open, exchange, server I/O, free) | Proved against an ideal two-party model (section 3d) |
| Legacy flows | C++ (`tls_worker_v3.cpp`, `service_kernels.h`, `tls_kernels.h`, …) behind `Flows/*Legacy.lean` | The same operations as hand-sequenced C++ calling the same Lean circuits | Historical; the default until the script path reaches speed parity; then deleted (`STACK_NOTES.md` 11.3) |
| node_worker | Rust | The trusted shell: pipe codec, per-batch agreement with the peer, manifest and pin checks, the handle table and its open rule, the instruction interpreter, the V3 program evaluator, the server socket | Small; the security-relevant part (`interp.rs`, `program.rs`, `handles.rs`) is a few hundred lines |
| Engines | C++ | emp-ag2pc (authenticated garbling, validated v3 patch, triples produced ahead of use) and a MASCOT field engine | Existing malicious-secure MPC implementations; trusted (PROOF_GAPS A1) |
| node_daemon | Rust | Application channel, peer channel (sealed, nonce, replay cache), controller spawn | Tested, not proved (PROOF_GAPS B5) |

### 2.2 The two worker paths

Every flow function (`Flow.Contacts.seal`, `Flow.Send.request`, …) consults the session's
**selection**. With nothing selected (the default) it calls the legacy C++ operation through
node_worker (`ea_legacy_dispatch`). With `SIGNAL_SCRIPTS` naming flow groups it runs the Lean script
of that group through the controller's script runner (`Flows/Runner.lean`, worker operation 93).
The legacy operations need the legacy library's own TLS state, so a selection containing `tls`
must script every operation the session can issue: the **closed selection** is all ten groups
(`closedSet`) for a normal session and all eleven (`ceremonySet`) for the registration ceremony
(`STACK_NOTES.md` section 10).

Status (`STACK_NOTES.md` 11.2, 11.3): with the closed selection, every stage of the local test set
passes on the real engines in malicious mode and the main stages in semi-honest mode, and the
golden records compare equal. **Speed parity is not reached on one machine** (semi-honest about
+11 %, malicious about +5 % per repeat-send message) and is reached with a 2 ms round trip. So
**the default is still all-legacy**.

### 2.3 How the two nodes agree on what they run

1. **Settings.** At the start of every two-party session each controller sends the other the
   SHA-256 of `Config.agreedText` (`PeerMsg.settingsDigest`; `Session/Start.lean` `connect`) and
   the session ends on any difference. The agreed settings include the client profile, recovery
   mode, the worker kind, the hinted curve programs, and `SIGNAL_SCRIPTS` when non-empty. Enforced
   by code and the lint, not by a theorem (PROOF_GAPS I5).
2. **Circuits.** Each worker loads only the kernels its manifest lists, checks every file against
   its pin, and the two workers compare the manifest's digest (with the pins of the word circuits
   and V3 field programs) on the control link before any request (`node_worker/src/loader.rs`).
   Script-path workers also refuse to start when a kernel's layout differs from what the scripts'
   well-formedness theorems assume (`tls_script_kernels_check`, `send_script_kernels_check`,
   the receive layout check, `refresh_script_kernels_check`): fail closed.
3. **Every batch.** Both workers send `SHA-256(session ‖ batch sequence ‖ skeleton)` on the control
   link and compare **before executing** the batch; the skeleton is the batch with every secret
   and exchange payload replaced by its length (`REORGANIZATION_PLAN.md` 5.1). An unusable batch
   stops both before any engine call (`engine_unusable_rejected_by_both`, `engine_shellPair_unusable`).
4. **Script selection.** `Select.check` refuses, at start, a selection that would strand a legacy
   operation:
   * `j22_check_closed`: if the check accepts a selection containing `tls`, every legacy operation
     that needs the legacy TLS phase and that this session kind can issue is replaced by a script
     of a selected group.
   * `j22_tls_needs_closedSet`: an accepted selection with `tls` contains all ten groups (any
     session but a ceremony); `j22_ceremony_needs`: for a ceremony, all eleven.
   * `j22_refusals`: the selection the stack accepted before (contact set + `tls` + `masks`) is
     refused, and a ceremony session cannot select `tls` without `ceremony`.
   * Not a theorem: which session kind issues which operation, and that the table lists every
     legacy operation that needs the legacy TLS phase (PROOF_GAPS J22b).

### 2.4 One send, end to end

1. The application sends both nodes a signed `notify(ids, text)`. The daemons agree on the job and
   start a send session.
2. Settings, manifest and connection: steps 1–2 of section 2.3. The **leader** node holds the TCP
   connection to the Signal server; the follower receives the server's records through the
   leader's worker (`ServerRecord` frames). The TLS 1.3 handshake runs inside the engines: the key
   share is a split X25519 (each node contributes a scalar summand), the handshake and
   application keys are derived in Boolean circuits, the server certificate and Finished are
   verified. Then the unauthenticated WebSocket upgrade, its nonce from joint randomness.
3. For each id: the controllers read the contact's key shares and sealed state from the database
   nodes (read with the parity check), enter their shares as private inputs (`contact-key`: the
   two shares summed mod p, then SHA-256), open the state (`contact-open`: only the one-byte
   `accepted` flag leaves the engines), and prepare the contact's curve values.
4. **Seal** (`signal-seal-official` / `-built`): the Signal ratchet step and sealed sender v1 in
   circuits. Opened: a status byte; on 255, the timestamp and the sealed-sender envelope.
5. **Store before send** (ORD-1): the advanced state is sealed under a fresh nonce from joint
   randomness, written to the database nodes, and both parties' acknowledgements are exchanged.
6. **Request**: the controller builds the WebSocket frame in the clear with **zero slots** where the
   contact's UUID, access key, device id and registration id go (`Policy/Request.lean`). The kernel
   `signal-request-ctr` fills the slots inside the engines and encrypts the TLS record; the GCM tag
   is formed from GHASH shares. The record goes to the server.
7. The server's response is read under the reveal policy (T1). A 409/410 triggers a device refresh
   (prekey fetch, PQXDH establishment per device), whose scratch state becomes the contact's state
   only after both parties saw the nodes acknowledge it (ORD-2).
8. The controllers exchange a digest of the per-id results and report only agreed results (T11).

### 2.5 One signup (receive), end to end

1. A receive session opens the **authenticated** socket: the Basic authorization line is built
   inside the engines from the two password shares (`signal-upgrade-shared`).
2. The server pushes `PUT /api/v1/message` requests. The controller reveals the framing and the
   request head under the reveal policy, and passes over the envelope's field payloads
   **unrevealed** (T1); the envelope bytes go into the engines.
3. Operation 50 (open the first message): unseal the static layer with the account's identity key,
   unseal the message, check the sender certificate (XEdDSA, the signature's point computed by the
   field engine), parse the PreKey message. Opened: the certificate length, shapes, the prekey ids
   it names and its Kyber ciphertext. The Kyber decapsulation runs outside the engines with the
   prekey private key (in the clear by policy).
4. Operation 51 (session): PQXDH agreements in the field engine, the receiving chain, the MAC
   check, decryption. Opened: a status byte, and **only if the status is 255** the text (`receive-text`
   is gated by `receive-session`, T13).
5. The text is the signup token; the database nodes map it to the contact's id, the new contact's
   record is sealed and stored, and only then is the message acknowledged (tested; no theorem is
   cited for this ordering).

Delete: the application's signed delete request with a list of ids is submitted to the database
nodes by both parties (one party can block it by not forwarding; `PRODUCT_TODO.md` section 6).

---

## 3. The security argument

### 3.0 The claim and the chain

**Top-level claim, in words.** In any run, everything a node learns comes from: its own inputs and
randomness; values the engines release, each of which goes through a typed opening of a listed
kind; the server's bytes it is allowed to reveal under the reveal policy; and messages from the
other node, which carry only public values. Each listed kind is shown to depend on the contact list
only as stated (mostly: not at all, or through a uniformly masked value), and the secret inputs it
is computed from are computed correctly.

**This claim is not one theorem** (PROOF_GAPS A7). It is the composition of the links below, each
proved under stated hypotheses, plus the trusted base of section 4.

```
 (a) every opening is typed (RevealKind) and bounded ──┐
     T1: server bytes; T3: per scripted operation;     │
     gating: refusals open nothing; T8/T9: what leaves │
 (b) ordering: store before send, commit after ack ────┤
 (c) circuits compute their Lean specifications ───────┼──► per-component guarantees
 (d) scripts are well formed; honest runs compute ─────┤      + section 4 (assumptions)
     their references                                  │      ≠ an end-to-end simulator proof
 (e) masks and conversions hide what they mask ────────┤
 (f) the curve and field facts the above use ──────────┤
 (g) state: nonces, the table, stock, rotation ────────┤
 (h) enforcement keeps the code inside the theorems ───┘
```

**Status words** used in `Security.lean` and below: **K** (about a term lowered into a deployed
kernel or program); **K-fn** (about a function a kernel is built from, on its own); **C** (about a
function the controller executes); **C-gen** (about a monad-generic definition that the controller
executes at its own monad, proved at a pure model monad; section 4.2, A8); **M** (about the ideal
two-party model of the engines, or a model not yet used by the session). **F** marks a
function-level statement (kernels' specifications composed through a script's own wiring, not
through a joint run).

**The model.** `Engine/Model.lean` defines the ideal semantics of each instruction (`idealStep`),
a run against any adversary (`withAdv`: the adversary controls one party's script inputs and
exchange payloads as functions of its view, and may abort) and a run of two honest parties
(`jointRun`). "Against any adversary" below always means `withAdv` for every `Adversary`.

### 3a. Every opening is typed and bounded

#### 3a.1 The reveal list

Every value that leaves the engines, or this party's own secrets, has type `Opened r α` for a
`RevealKind r` (`TlsMpc/Node/Types.lean`, 49 kinds in ten groups: TLS, policy-public, stored state,
send, receive, refresh, ceremony, conversions, curve, own-secret reveals). `Opened`'s constructor is
private to `TlsMpc/Node/Reveal.lean`, so the kinds and their makers there are the complete list.
That is a type-system fact plus the lint (section 3h), not a theorem. Secret values are of type
`Secret α`, whose accessor appears only in the eliminators' files (lint `secret-val`).

| Theorem | Statement in plain words |
|---|---|
| `revealKind_codes_distinct` | The kinds' numeric codes are pairwise distinct, so a code (and the engine label mapped to it) names one kind. |
| `revealKind_mem_all` | `RevealKind.all` lists every kind. |
| `revealKind_code_ne_zero` | No kind has code 0 (the worker refuses label 0). |
| `engine_label_ofKind_inj`, `engine_label_all_distinct`, `engine_label_all_nonzero` | Engine labels name their kinds injectively; registered labels are distinct and nonzero. |
| `engine_view_labels_H`, `engine_view_labels_D` | In any model run, what was released to either party carries, in order, the labels of release instructions the run reached. |
| `engine_viewD_kinds`, `engine_viewH_kinds` | If a script declares kinds `ks` (`Reveals ks s`), every release either party receives, against any adversary, is labelled with a declared kind. |
| `registry_declared_registered` | Every kind a script flow declares is a registered kind. |
| `registry_viewD_registered` | Hence the adversary only ever receives registered labels. |

#### 3a.2 T1: what the controller reveals of the server's bytes

Server bytes arrive as TLS records the engines decrypt. The controller asks the engines to reveal
byte ranges of a record (the length probe and `revealRange`) and decides, byte by byte, what may be
revealed. The **reference** `ReceiveSpec.classify` marks as hidden: the body of every server request
(protobuf field 3), the body of every response (field 4, unless the session explicitly opens
response bodies), every envelope field's payload, and payload bytes of a message of unknown kind
past its second byte. T1 says the controller never reveals a hidden byte.

| Theorem | File (original) | Statement and hypotheses |
|---|---|---|
| `receivePolicy_t1_start` (`ReceiveStart.t1_start`) | `Policy/ReceiveStart.lean` | **The headline.** From the start states the session uses, over **every** byte stream (the upgrade response's HTTP head, then WebSocket frames), cut into TLS records **in any way**, every stream position the session's record loop has the engines reveal is allowed by `ReceiveSpec.classify`, or is the stream's first `error` (the one-byte allowance). Hypotheses: the engines are `Faithful` (D8, section 4.2); the steps between records keep the policy's view and the upgrade parser's state (`KeepsHead`). **C-gen**. |
| `receivePolicy_t1_all` (`ReceiveLoop.t1_all`) | `Policy/ReceiveSession.lean` | The same from the upgraded state against `classifyFrames` (frames only), with steps that keep the view (`Keeps`). **C-gen**. Its general form from any simulating state is `ReceiveLoop.t1_session` (not restated). |
| `receivePolicy_loop_sub` | `Policy/ReceiveSession.lean` | The loop the session runs (`RecordLoop.run`) reveals only positions the model loop reveals, and returns the model's state (under `Faithful`). This is what makes T1 about the deployed loop (PROOF_GAPS C1, closed). |
| `receivePolicy_run_fuel` | same | The deployed loop's fuel (record length + 1) never runs out: it behaves as the unbounded loop. |
| `receivePolicy_keeps_afterRecord`, `receivePolicy_keepsHead_afterRecord`, `receivePolicy_view_replies` | same / `ReceiveStart.lean` | The session's actual steps between records (control replies with any masks, then clearing requests) keep the view (and the upgrade parser's state), discharging `Keeps` / `KeepsHead` for them. |
| `receivePolicy_t1_start_model`, `receivePolicy_t1_frames` | | T1 for the model loop (**M**), which the deployed-loop theorems run through. |
| `receivePolicy_request_body_unrevealed`, `receivePolicy_response_body_unrevealed` | `Policy/ReceiveProofs.lean` | For any request (response) in the server's layout with varints of at most 10 bytes: no reveal run reaches the body, and at the body's length the scanner says to pass over exactly the body. |
| `receivePolicy_envRun_safe`, `receivePolicy_request_envelope_safe`, `receivePolicy_envelope_payload_unrevealed` | `Policy/ReceiveInvariant.lean`, `ReceiveEnvelope.lean` | Walking a delivered envelope (`/api/v1/message`), whatever moves the controller makes, every revealed body byte is a key, a length or a varint value of the reference envelope, never a field's payload. |
| `receivePolicy_scanBody_tooLong`, `receivePolicy_scan_wrapper_tooLong`, `receivePolicy_replyScanBody_tooLong`, `receivePolicy_replyScan_wrapper_tooLong` | `Policy/ReceiveProofs.lean` | Fail closed: a varint longer than 10 bytes is `malformed`. (These close the leak of NEEDS_REVIEW 3f item 5, section 5.2.) |
| `receivePolicy_upgrade_run_safe`, `receivePolicy_frameByte_head`, `receivePolicy_headStep` | `Policy/ReceiveHead.lean`, `ReceiveStart.lean` | Before the upgrade every reveal stays inside the HTTP head; the head's bytes leave the frame parser idle; the byte completing CR LF CR LF hands over to the frame relation at the reference's initial state. |

**The weight-carrying hypothesis is `Faithful`** (`ReceiveSession.lean` line 87): the engines' length
probe returns the record's length, and `revealRange offset count` returns exactly
`(record.drop offset).take count`, revealing those positions and no others; the other record
operations reveal nothing. On the default path this is an **assumption on the C++ operation 43**
(PROOF_GAPS D8). On the script path the reveal kernel's value is proved
(`s12_tls_reveal_value`: the kernel outputs the length and the content up to it, zeros after;
`s12_tls_range_value`: a range below the length is the server's bytes), but the TLS backend's IO
glue that implements the operations is unverified (F17).

Also relevant: the fuel change fails closed if an engine reports a longer record later (D9).

#### 3a.3 Gating: a refusal opens nothing

"Gating": an opened output is forced to zeros when a check fails, so a failure reveals only that
it failed.

| Theorem | Statement |
|---|---|
| `typedOpen_gated` | **K**, the one theorem that quantifies over a deployed kernel's opened fields: for every input with `accepted = 0`, `tls-open-typed`'s opened fields are exactly `[[0], [0, 0]]`. |
| `typedOpen_rejected_independent` | A rejected record's parse is the same for any keys, nonces, contents and length bytes of the same record length. |
| `typedOpen_handshakeBit_cases` | The opened handshake bit is always 0 or 255. |
| `contactOpen_spec`, `contacts_open_released_byte` | `contact-open` releases the decrypted state only under its check flag; what an open releases is one byte, 255 iff `check` is this key's check value. |
| `receiveAccept_receiveText_gated` | **K**: when `receive-text`'s plaintext input is `receive-session`'s plaintext output and the session's opened status is not 255, every output of `receive-text` is zero. |
| `s13_seal_refused_silent` | After a seal's status other than 255 is opened, the send script releases nothing more and keeps the state. |
| `s13_devices_refused_view` | Multi-device send: if some device's status is not 255, nothing more is released to anyone, no envelope of any device is opened, the stored state is kept. |
| `s14_sessionRest_refused` | Once `receive-session`'s status opens to anything but 255, the receive script frees the conversation and plaintext and releases nothing more. |

#### 3a.4 T3: what each scripted operation opens, against any adversary

These are **script-path** theorems (in the model). A "kinds" theorem says every release carries a
declared kind; a "value" theorem says exactly which values the adversary sees.

| Flow | Theorems | What is proved |
|---|---|---|
| Joint randomness, upgrade nonce | `prand_disclosure`, `flows_joint_viewD_kinds`, `flows_publicUpgrade_viewD_kinds` | The adversary's view is a prefix of [our commitment, our opening]. |
| Contact key, seal, open, evict, assign (ops 36–38, 40, 52, 63) | `contacts_key_disclosure`, `contacts_seal_disclosure`, `contacts_open_disclosure`, `contactsTable_opKey_disclosure`, `contactsTable_opSeal_disclosure`, `contactsTable_opOpen_disclosure`, `contactsTable_opEvict_disclosure`, `contactsTable_opAssign_disclosure` | Key, evict, assign: nothing to either party. Seal: at most one `sealedBlob`, the `contact-seal` kernel's output. Open: at most the one `accepted` byte. Seal and open assume `Loaded` (section 4.2). |
| Account (ops 53, 54) | `account_accountKey_disclosure`, `account_accountSeal_disclosure`, `account_opSeal_disclosure_shares`, `flows_account_opSeal_viewD_kinds` | Nothing, or one `sealedBlob`; with credentials from two shares their XOR stays in the engines. |
| State write | `contactsWrite_write_disclosure` | A prefix of [commitment, opening, the one sealed blob under nonce v]. |
| Op 44 (TEST admit) | `j23_admit_disclosure` | Nothing, to either party. |
| Masked quotient, W2F, F2W | `s10_pinv_disclosure`, `s10_pw2f_disclosure` | The quotient: only z·m and the zero flag. Word to field: c and its re-comparison. |
| Curve point exchange, quotient round | `s11_pointExchange_disclosure`, `s11_quotientMany_disclosure` | A prefix of [our commitment, our opening]; a prefix of the masked denominators and the zero flags. Other curve openings are proved only at the level of kinds (F24). |
| TLS seal and open | `s12_tls_sealCtr_disclosure`, `s12_tls_open_disclosure_A`, `s12_ghash_round_disclosure_A` | Value-level, against any adversary; the open and the GHASH round with party A honest (B-honest not written: F20a). |
| Send (ops 41, 42, 61, 62) | `s13_send_reveal`, `s13_seal_view` | Op 41/61 release only `counterWidths` or `sealedEnvelope`; ops 42/62 release nothing; the record phase only `sealedRecord`. Op 41's view by value: [flags, status] on refusal, [flags, status, timestamp ‖ envelope] on acceptance. |
| Receive (ops 50, 51) | `s14_openFirst_reveals`, `s14_session_reveals` | Kinds only, every branch (value-level open: F36). |
| Refresh | `s15_refresh_viewD_kinds`, `join_refresh_reveals` | Kinds only (value-level open: F47). |
| Ceremony (ops 80, 81) | `s16_ceremony_secrets_viewD_kinds`, `s16_ceremony_register_viewD` | Kinds; value-level for op 80 open (K1). |
| Joins | `join_splitAgreeWord_reveals`, `join_ephemeralWord_reveals`, `join_receive_reveals`, `join_refreshOps_reveals`, `join_kinds_registered`, `j12_senderPublic_reveals`, `f32_prepare_reveals` | The S11 curve flows instantiated as the parameters of S12–S15 release only declared, registered kinds. |

**Not covered by any bounding theorem** (PROOF_GAPS G): `handshakeShare` (G1), `assignStatus` (G2),
the legacy `jointRandom` of operation 33 (G4). `prepareStatus` (G3) is closed in the Closed table
for the script path: `s11_prepareStatus_iff` (the lift's status is 255 exactly when the coordinate's
curve polynomial is a nonzero square, under `FieldInverse` and Euler's criterion as named
hypotheses) and `f32_prepareStatus_iff` (op 66's per-contact status byte is 255 exactly when the
contact is prepared in the table).

#### 3a.5 What else leaves the controller

**Requests to the server (T8).** The controller builds every request frame in the clear with zero
slots for the contact's identifiers; only the engines fill them.

| Theorem | Statement |
|---|---|
| `t8_build_two_contacts` | **The privacy link**: two contacts' send frames agree at every position outside the four slots (UUID 36, access key 24, device id 3, registration id 10 bytes). What the controllers know of a send does not depend on the contact. |
| `t8_build_layout` | `build`'s layout depends only on public lengths (envelope, timestamp digits, id varint). |
| `t8_build_public`, `t8_buildFetch_public`, `t8_buildDevices_public` | Outside its slots, the frame is the public frame of the reference request. |
| `t8_build_reference`, `t8_sendMessage_reference`, `t8_fetchMessage_reference`, `t8_devicesMessage_reference` | Filled, the frame is RFC 6455's masked client frame of the reference protobuf request with the reference JSON body. Hypothesis: ids below 2⁷⁰. |
| `t8_close_reference`, `t8_keepalive_reference`, `t8_reply_reference` | The Close, keepalive and reply frames against RFC 6455 and the protobuf reference (`reply`'s id: under a hypothesis, D6). |

**To the other node (T9).** No constructor of a type in `Messages.lean` mentions `Secret`, `Handle`
or a buffer handle, directly or through any type it uses: `Messages.checkPublic` runs at the end of
that file and fails the build otherwise. That is a build check, not a theorem.
`peerMsg_reply_kind`: a peer's reply is decoded as the same constructor this node sent, or the
session ends.

### 3b. Ordering

These are about the deployed session functions themselves: each is defined once over any monad
and run at the session monad with the real operations (`abbrev f := fG realOps`); the theorems
quantify over the model's operations records (**C-gen**; PROOF_GAPS C3 closed; the remaining
step is A8). They apply to **both** paths: the flow functions they call are the same whether or
not a script is selected (`STACK_NOTES.md` 11.2).

| Theorem | Statement |
|---|---|
| `ord1_sendSoft_agreed`, `ord1_sendMessage_acked` | **ORD-1**: every message request handed to the worker comes after the contact's message was sealed, its advanced state sealed for storage, acknowledged by this party's database nodes and (recovery path) reported acknowledged by the other party, with no seal of that contact in between. Hypothesis: the database client is configured. |
| `ord1_deliverJob_sendsAgreed`, `ord1_loop_sendsAcked`, `ord1_serve_sendsAgreed` | The same over every run of `deliverJob`, `loop` and `serve`, refreshes included. |
| `ord2_commitScratch_agreed`, `ord2_commitScratch_outcome` | **ORD-2**: a refresh's scratch is committed only after it was sealed, this party's nodes acknowledged, and the other party reported its acknowledgement; `true` exactly after the commit, `false` after the drop. |
| `ord2_deliverJob_commitsAgreed`, `ord2_loop_commitsAgreed`, `ord2_serve_commitsAgreed` | ORD-2 over every run of the loops. |
| `t11_deliverJob_results`, `t11_resultsTail_spec` | **T11** at `deliverJob`'s level: when it returns, the newest event is the results-digest exchange in which the other party's digest equals ours; on failure the reported results are unchanged. |
| `versions_storeSoft`, `versions_storeAdvanced`, `versions_versionIn_bumpIn` | A contact's version moves to the next exactly when the store was taken; a listed contact gets version + 1. |
| `tlsPolicy_consecutive_application_distinct`, `tlsPolicy_application_reservation`, `tlsPolicy_pending_blocks_application`, `tlsPolicy_aborted_blocks` | TLS record sequence numbers: consecutive records never share one (no AES-GCM nonce reuse within an epoch, as far as the policy goes); nothing is reserved while a KeyUpdate is pending or after an abort. |
| `s13_send_state_order`, `s15_ord2_commit` | Script level: the accepted op 41 returns the new state handle before the envelope is opened; `opCommit` is the only refresh operation that changes a contact's entry. |

What carries these to a real run: the real operations do what their events name
(`Session/Events.lean` header); no code but the deployed records hands a message request to the
worker or commits a scratch (lint `ordering-sites`); A8. Open: T11 at the final-report level (I2);
the non-recovery path checks only its own party's acknowledgement (I1, argued).

### 3c. Circuits compute their reference functions

#### 3c.1 Lowering and printing (T2)

| Theorem | Statement |
|---|---|
| `lower_sound`, `lower_correct` | If `lower` accepts a DAG, the flat gate list is well formed, has the stated inputs and outputs, and every output wire evaluates to the AIG node it came from, for every input. |
| `lowerExpr_correct` | A kernel expression lowers to a flat list whose output k is bit `sel[k]` of the expression's value. |
| `joinExpr_correct` | Joining a kernel's byte outputs into one bit vector is faithful. |
| `flat_parse_render`, `flat_printWith_render`, `flat_lowerExpr_loaded` | What the circuit printer writes parses back to the gate list, and that list computes the lowered expression. |
| `layout_parse`, `layout_openCode` | The printed layout lists exactly the kernel's declared fields; the open mark is 2/3 exactly for party 1/2 only, 1 for a public output, 0 for a private one. |
| `kernel_loaded` | **T2 for every kernel the four emitters lower**: the circuit text parses back to the flat list, the layout to the kernel's fields and marks, and the flat list is `lowerExpr` of the kernel's joined outputs. Not covered: `selection` (which named output bit is which bit of the joined value). |
| `kernel_compiled_correct` | Every exported AIG output bit equals the Lean kernel's definition on the same input (the AIG export path). |
| `boolDag_compile_correct`, `fieldDag_compile_correct` | Accepted Boolean / field DAG compilations (translation validation of the word-mask circuits and field programs) evaluate to their expressions. |

#### 3c.2 V3 field programs (the script path's programs)

| Theorem | Statement |
|---|---|
| `fieldDagV3_parse_render`, `fieldDagV3_render_parse` | A valid program's text parses back to it, and the parser accepts only rendered texts, so a pin names one program. |
| `fieldDagV3_eval_compileAll`, `fieldProgramsV3_decl_values` | A program's outputs are its source expressions' values. Hypothesis `FieldInverse`. |
| `fieldDagV3_masksOk_once`, `fieldDagV3_parse_masksOk`, `fieldProgramsV3_decl_checks` | Every mask is used by exactly one division row; public outputs are exactly the declared checks (P-INV (d), P-FIELDPROG). |
| `fieldDagV3_masked_div`, `fieldDagV3_opening_zero_iff`, `fieldDagV3_opening_bijective`, `fieldDagV3_quotient_spec` | A nonzero opening b·m gives the true quotient; it is 0 iff b or m is; for b ≠ 0, m ↦ b·m is a bijection (uniform opening for a uniform mask); the quotient program opens only z·m. |
| `engine_check_program`, `engine_check_program_openable`, `engine_idealStep_program`, `engine_runProgram_lengths` | The shell accepts a program step only for a loaded program with matching counts, masks live and marked never and consumed; an output is openable exactly when its V3 file marks it public; a step releases exactly one opening per division row per instance. |

The legacy C++ evaluator (`field_program.h`) masks its divisions itself, which is not modelled
(`fieldDag_compile_correct`'s docstring).

#### 3c.3 Kernel specifications (examples; section 2 of `Security.lean` has them all)

Most kernel specifications state the kernel's outputs under every input assignment; several are
against independent references (RFC transcriptions, the sealed-sender reference), most are against
the repository's own compositions (PROOF_GAPS E1).

| Theorem | Statement |
|---|---|
| `contactKey_spec` | `contact-key` is 32 zero bytes then the first 28 bytes of SHA-256(label ‖ (a + b mod 2²⁵⁵ − 19)). **Hypothesis: both shares are below p; nothing in the kernel checks it.** |
| `contactSeal_spec`, `contact_round_trip` | `contact-seal` is AES-CTR of the state under the key and version plus the key's check value; opening what was sealed returns it. |
| `tlsSealCtr_spec`, `gcmTag_spec`, `gcmCheck_spec`, `gcmKeyShare_spec`, `gcmMultiply_spec`, `tlsUpdate_spec` | The TLS record seal, GCM tag from shares, the 255/0 check, GHASH key and product shares, the TLS 1.3 key update. |
| `serverReceives_accepted` | **T7, what the server receives for an accepted send**: when the seal opened status 255 and the controller built the frame with the opened envelope, the reference send step accepts and `signal-request-ctr`'s outputs are the TLS record of the masked frame with the contact's ids in their slots, where the envelope is sealed sender v1 (`Reference.sealV1`) of the reference Signal message. **Hypotheses `hframe`, `hmask`: the worker passes the controller's frame and mask unchanged** (on the default path the C++ does this, trusted; on the script path it is the script's own concatenation, `s13_send_accepted`). |
| `receiveAccept_session_status_iff` | **T13**: `receive-session`'s status is 255 iff every earlier check is 255, no agreement is all zero, the layouts and addresses are as stated, the counter and post-quantum index are within the jump, the MAC verifies under libsignal's keys, and the CBC padding is valid. |
| `receiveAccept_session_accept_certificate` | With the certificate kernels wired in: an accepted session also means the certificate's checks passed, its identity is the sender's, its signer is the trusted one, it has not expired, and the signature's R is the compression of the field engine's [s]B − [h]A. |
| `receiveAcceptText_accepted_iff_reference`, `receiveAcceptText_overlongBody_refused` | `receive-text` accepts exactly what a reference protobuf reading accepts, for length prefixes of at most two bytes (longer prefixes are refused: a completeness gap, E6); the over-long-body counterexample is refused. |
| `kemc_kernels_compose`, `kemc_pipeline_valid_accept`, `kemc_pipeline_invalid` | The six `kem-*` kernels compute `pipeline` **when each input is bound to the output the worker binds it to** (name-binding hypotheses: trusted C++ on the default path; proved for the script's wiring by `s15_kem_pipeline`, under `KemWidths`). On a valid key with sampling within budget `pipeline` is the repository's reference `MlKem.encapsulate`; on an invalid key it is all zeros. That the reference is Kyber-1024 rests on test vectors (E5). |

#### 3c.4 Manifests and pins

Kernels are produced from the Lean emitters into a manifest with SHA-256 pins
(`scripts/produce_circuits.py`); the strict worker loads only manifest kernels, checks pins, and the
two workers compare manifest digests before any request (section 2.3). Trusted: that a cache entry
under a name is that emitter's output for that kernel, and that the loaders parse as
`parseFlat`/`parseLayout` do (B3). The circuit cache is keyed by the emitter binary's hash, which is
why the lint forbids emitters importing controller modules (section 3h).

### 3d. Scripts: well formed, and honest runs compute the references

All of 3d is **script path only**.

#### 3d.1 The engine model and the runner

| Theorem | Statement |
|---|---|
| `engine_T12_skeleton_determinism`, `engine_trace_eq_skeletons` | **T12**: two runs of a script whose replies agree reach the same instructions, whatever the private inputs, the adversary and the engine state. The skeletons (what the peers agree on) do not depend on secrets. |
| `engine_honest_replay` | The honest party's result and store are a function of its script, store and view. |
| `engine_skeletonBytes_inj`, `engine_decodeBatch_encodeBatch` | Equal skeleton bytes are equal skeletons; the batch encoding round-trips (batches below 2⁶⁴ wires, bounded wires). |
| `engine_counters_blocksB_disjoint` | Allocated handles are never reused. |
| `engine_withAdv_bind`, `engine_jointRun_bind` | Runs compose over `bind` (the tool for whole-flow theorems). |
| `engine_nextBatch_admitted`, `engine_nextBatch_bounded`, `engine_fill_bounded`, `engine_nextBatch_ends` | A well-formed script's batches are admitted by the shell's `check`; their wires are bounded. |
| `runner_drive_model` | **The controller sends exactly the batches the model says**: if the honest party's model run returns, the runner's pure core `drive`, fed the values the model released, sends batches whose instructions are the model run's trace, in order, and ends with the model's result and store. |
| `runner_drive_bounded`, `runner_nextBatch_fill_only` | The runner sends only bounded wires; batches depend on the store only through `fill`. |

Not proved: that the runner's IO loop sends `drive`'s batches (J10, J28: a free-only trailing batch
is now sent at the head of the next one; frees release nothing).

#### 3d.2 Per stage: well-formedness (WF) and honest runs (T4)

| Stage / flows | WF and boundedness | Honest runs (`jointRun`) | Notable hypotheses / open |
|---|---|---|---|
| S9 random, upgrade, contacts, account | `contacts_keyScript_wf`, `contacts_sealScript_wf`, `contacts_openScript_wf`, `contactsTable_op*_inv`, `contactsWrite_writeScript_wfp` | `prand_a_honest` (both return r_A ⊕ r_B), `upgrade_honest` (RFC 6455 accept value), `contacts_key_honest`, `contacts_seal_honest`, `contacts_open_honest`, `contacts_key_seal_open` (sealed in one session, opened under a re-derived key in another), `contactsWrite_write_honest` | `Loaded` (the three contact kernels are their Lean kernels); the honest commitments differ (`hc`) |
| S10 conversions, masks | `s10_generate_wf`, `s10_sharedBits_wf`, `s10_quotient_wf`, `s10_challenge_wf` | `s10_pcut_a_run` (whole `generate`, every parameter set with 0 < M and bits ≤ N), `s10_pw2f_honest`, `s10_pf2w_honest`, `s10_pb2f_honest`, `s10_pbits_honest`, `s10_pinv_honest` | `WordLoaded`, `ProgsLoaded`, `FieldInverse`; WF of `wordToField`, `fieldToWord`, `bitsToField`, `Account.openStep` open on main (F8; closed on the branch) |
| S11 curve | `s11_wf_split_offset`, `s11_wf_hinted`, `s11_prepareContacts_wf` | `s11_splitBegin_honest`, `s11_agree_honest` (handles hold `X25519.spec` of the bits and point), `s11_offset_honest`, `s11_hinted_honest`, `s11_lift_agreeHinted_honest`, `s11_offsetPrepare_honest_derived` | `FieldInverse`, `CompleteAddition`, `AddClosed`, `ExtClosed`, `RecipientOnCurve` (each a theorem in `proofs/`); input conditions (F22d); `prepareSecond`, `prepareContacts` through `jointRun` open (F22) |
| S12 TLS | `s12_tls_sealCtr_wf`, `s12_tls_open_wf`, `s12_tls_derive_wf`, `s12_tls_finish_wf`, `s12_ghash_round_wf`, `s12_tls_open_bounded` | `s12_tls_seal_honest` (header ‖ ciphertext ‖ tag is `TlsRecord.sealCore`), `s12_tls_open_binding_honest`, `s12_tls_open_class`, `s12_tls_open_rejected_run`, `s12_tls_derive_honest`, `s12_ghash_ensure_shared` | Handshake record / Finished / reveal / update scripts at function level only (F13a); kernels' signatures as explicit marks (F14a) |
| S13 send | `s13_sealScript_wf`, `s13_requestScript_wf`, `s13_requestCtrScript_wf`, `s13_sealScript_bounded` | `s13_seal_joint`, `s13_send_joint` (one device: op 41, op 42, the CTR phase and tag; the bytes are those of `s13_send_accepted`), `s13_devices_accepted` (multi-device, function level, no wiring hypothesis) | Multi-device through `jointRun` open (F51); the four curve words are inputs (E4); `Table.Inv` for the send's commit (F59b) |
| S14 receive | (main: tested only, F37) | Function level: `s14_accept_certificate`, `s14_text`, `s14_record`, `s14_verified_wiring` (wiring by definition) | Through `jointRun`: on the branch (3d.8) |
| S15 refresh | `s15_drop_inv` | `s15_kem_pipeline` (with `KemWidths`), `s15_parse_device`, `s15_parse_or_refuse`, `s15_first_wired` | KEM and session step through `jointRun` open (F42); widths assumed (F43) |
| S16 ceremony; ops 47, 46, 32, 44 | `s16_ceremony_secrets_wf`, `s16_ceremony_register_wf`, `s16_ceremony_bounded`, `s16_upgrade_wf`, `j23_admit_inv`, `j23_admit_bounded` | `s16_ceremony_secrets_honest`, `s16_ceremony_register_honest`, `s16_ceremony_honest`, `s16_request_shared_value`, `s16_request_plain_value`, `j23_admit_honest` | `SecretsLoaded`; the registration request's record phase not through `jointRun` (K4) |

#### 3d.3 Fresh randomness is read once (J1)

| Theorem | Statement |
|---|---|
| `j1_openFirst_reads_once`, `j1_session_reads_once` | On every run of the joined receive operations, whatever the replies, the field-element slots read are slots of the starting supply, none twice. (Before the fix, two openings z₁·m and z₂·m with one mask m revealed z₁/z₂.) |
| `j1_receiveAgree_once`, `j1_refreshOps_reads_once` | The same for the joined agreements and S15's curve operations. |
| `j1_refresh_pools_disjoint` | The mask pools cut for the three refresh calls share no mask. |
| `j13_release` | A released slot reads as the base store (a script naming it fails the payload check). |
| `j8_receiveAgree_spares`, `j8_agreeG_spares`, `j12_senderPublic_spares` | The joined agreements free or take as masks only what they made or took. |

#### 3d.4 Wiring and widths

`s14_verified_wiring` (the receive session's `verified` input is the certificate kernels' output by
definition), `join_first_wired` (S15's first-message bindings from S13's layout, still assuming
`hcert`/`hpend`, J6), `j21_session_receiver_bits` and `j21_receiverBytes` (the receive script slices
`receive-session`'s receiver record at the kernel's width, 200 bytes), `s13_bundleEnvBytes_eq`.

#### 3d.8 Proved on a branch, not yet merged

Branch `s14-s15-proofs` (worktree `.claude/worktrees/agent-ab9e1fc3873ce8e0c`, notes
`S14_S15_PROOFS.md`, `Security.lean` sections 7m–7zb there). **Not on the main line; not counted in
the 783.** It closes most of the receive flow's run-level gap (F35) and its WF (F37):

| Theorem (branch) | Statement |
|---|---|
| `s1415_openFirst_wfp`, `s1415_session_wfp` | Operations 50 and 51 are well formed (F37). |
| `s1415_wordToField_wf` | Word to field is well formed (part of F8). |
| `s1415_take_honest_bytes` | Operation 48 on two honest parties. |
| `s1415_openFirst_zero` | Op 50 aborts exactly on a zero reference ladder denominator. |
| `s1415_openFirst_cases` | Op 50 on two honest parties, every branch, against the reference `firstRef` (refused: everything made is freed; accepted: the reference's opened values). |
| `s1415_session_cases` | Op 51 on two honest parties, every branch, against `sessionRef`. |
| `s1415_firstRef_accepted` | What op 50's reference accepts has op 51's shapes. |
| `s1415_receive_honest` | **The receive headline**: op 50 then op 51 through `jointRun` with the joined curve; on acceptance the reference's text and 319-byte contact record. |

Their hypotheses are many and named (programs loaded, `FieldInverse`, receive kernels as model
circuits, entry-state conditions, the scalars' swap bits held, nonzero mask sums); still open there:
N3 (entry conditions established by the glue), N9 (coins), and the link to the function-level
`Pipeline.In` theorems.

### 3e. Masks and conversions hide

**The form of hiding.** In the main package hiding is stated without probability, as a bijection on
the honest party's randomness carrying one secret's view to another's (`REORGANIZATION_PLAN.md`
7.0). `hiding_of_bijection` **(proofs/)** turns each such statement into equal output
distributions for uniform randomness.

| Theorem | Statement |
|---|---|
| `prand_b_ideal`, `prand_commit_before_open`, `prand_c_copy_aborts` | **P-RAND**: under `IdealCommit`, every accepted joint value is r ⊕ v for one v fixed before our opening, so it is uniform for uniform r; the adversary committed before seeing our opening; copying our commitment aborts. |
| `s10_generate_hides`, `s10_reRand_bijection` | **P-CUT (c)**: against any adversary, the view of mask generation with honest candidates r (kept references moved by δ) equals the view with re-randomised candidates, and the re-randomisation is a bijection. For **fixed** challenge randomness of the honest party (F7 scope note). |
| `s10_generate_sound` | In any run of `generate` that returns, the other party's candidates are its choice from its view **before** the run (the bad set is fixed before the challenges), every cut candidate is canonical with error 0, every bucket pair passes, every kept reference is canonical. These are the counting model's hypotheses. |
| `s10_arrangement`, `s10_bucket_uniform` | The two challenge permutations compose into the model's single arrangement (a permutation); no mixed bucket survives. That the arrangement is uniform is argued, not proved (F12). |
| `s10_pw2f_hides`, `s10_pf2w_hides`, `s10_pb2f` | The masked values opened by word-to-field, field-to-word and bits-to-field are bijective in the honest mask. |
| `ghash_share_hides` | The masked GHASH key power B sees has exactly one mask explaining it, for any key. |
| `s16_ceremony_masked_hides` | The opened ceremony value: for every password, each opened value comes from exactly one honest mask. |
| `maskedAgreement_mask_hides`, `offsetAgreement_public_key_independent` | Arithmetic models over any ℤ-module (section 6d). |

**Probability bounds (proofs/).**

| Theorem (proofs/) | Statement |
|---|---|
| `cut_and_bucket_probability` | For the protocol layout (2BN candidates, BN opened, N buckets of B) with **one uniform challenge permutation**, a bad set of B·t candidates fixed before the challenge goes undetected with probability exactly C(N, t)/C(2BN, B·t). |
| `cut_bound_le_bound_one`, `undetected_lt_of_bound_t1` | t = 1 is the worst case for B ≥ 2; so bound(1) < 2⁻¹²⁸ implies every bad set goes undetected with probability < 2⁻¹²⁸. |
| `deployed_undetected_lt`, `profile_256_undetected_lt`, `profile_512_undetected_lt`, `profile_1024_undetected_lt` | Instantiated for N = 2¹⁹, B = 8 (the triple batches, NEEDS_REVIEW 1.2) and the profiles 256/14, 512/13, 1024/12. |
| `ghash_share_hides_dist`, `joint_random_uniform`, `word_to_field_open_uniform`, `field_to_word_open_uniform`, `masked_inverse_open_uniform`, `ceremony_masked_uniform` | Distributional forms of the hiding statements. |
| `deployedOffset_uniform` | The offset sampling rule (mine XOR peer) mod 2²⁵² is exactly uniform on [0, 2²⁵²) for uniform `mine` and any fixed `peer`. |
| `ed25519_key_close_uniform`, `ed25519_keys_close` | The resulting public key is within 2⁻¹²⁷ of uniform on the group (B ≠ 0); k messages within k·2⁻¹²⁷. Hypotheses: `idealCommit`; the peer's value fixed per message (an adaptive peer across messages is not covered, A4). |

**Two cautions.** (1) These probability statements are about **models**: the detection rules
(P-CUT (d), (e)) and a single uniform permutation are the model's assumptions; `s10_generate_sound`
discharges the detection rules for the Lean script, but the uniformity of the composed arrangement
and of the permutations (SHA-256 as a random oracle) is argued (F12), and **the legacy C++
generators are not covered** (C4). (2) The script's deployed word-mask profile is N = 16, B = 22
(`S10_NOTES.md`, "Parameters"); no `*_undetected_lt` instance for 16/22 is stated in `proofs/`
(the generic `undetected_lt_of_bound_t1` would give it from the numeric fact bound(1) < 2⁻¹²⁸,
which is not stated there).

### 3f. Curve and field mathematics

All in `proofs/`, with only the standard axioms (`proofs/SECURITY_MATHLIB_AXIOMS.txt`).

| Theorem (proofs/) | Statement |
|---|---|
| `prime_modulus`, `prime_order` | 2²⁵⁵ − 19 and the Ed25519 group order ℓ are prime (Pocklington certificates, evaluated by the kernel; no `native_decide`). |
| `toZMod_inverse` | The main package's field inverse is `ZMod p`'s; this discharges the named hypothesis `FieldInverse` (PROOF_GAPS F2) — by a theorem in a separate package, not linked by import. |
| `two_not_square`, `euler_criterion`, `euler_nonsquare` | H-QR: 2 is a non-square mod p; Euler's criterion. |
| `edwards_complete`, `edwards_add_assoc`, `edwards_group_laws` | H-GROUP: the Edwards addition law on −x² + y² = 1 + d·x²y² is complete (denominators never vanish) and the curve points form a commutative group. |
| `pointAddValue_is_group_add`, `extAddValue_is_group_add`, `curveCheck_zero_iff` | The main package's formulas are the group law; `curveCheck` is zero exactly on the curve. |
| `base_order_nsmul`, `base_addOrderOf`, `curve_subgroup_card` | ℓ·B = 0, B has order exactly ℓ; a nonzero point killed by ℓ generates a subgroup of order ℓ. |
| `x25519_spec_scalar_mult`, `x25519_spec_scalar_mult_all`, `x25519_clampedScalar_rfc` | X25519 as implemented is scalar multiplication by the RFC 7748 clamped scalar, for every u that is the coordinate of a curve point (u = 0 included). **Not** for u on the quadratic twist (H3). |
| `montQ_square_iff`, `liftPoint_valid_point` | u(u² + 486662u + 1) is a square exactly when u is a curve point's coordinate; the lift outputs a curve point. |
| `offsetSum_scalar_mult`, `bitSum_is_x25519`, `xeddsa_doubleScalar` | The table chains compute the stated multiples; XEdDSA's [s]B − [h]A. |

Still open (section 4.4, H): the group order #E = 8ℓ (so "every point killed by ℓ is a multiple of
B" and the torsion reading of `edwards-torsion-hinted`); X25519 on the twist.

### 3g. State

| Theorem | Statement |
|---|---|
| `contactsWrite_write_fresh` | **T10, the worker flows' part** (script path, against any adversary): a state write's nonce is a valid version, not used before in the session, and the blob is nonce ‖ the seal's reply. |
| `contactsWrite_used_nodup` | Adding each write's nonce keeps the session's nonce list duplicate free. |
| `contactsTable_inv_empty`, `contactsTable_opKey_inv`, `contactsTable_opSeal_inv`, `contactsTable_opOpen_inv`, `contactsTable_opEvict_inv`, `contactsTable_opAssign_inv`, `contactsWrite_opWrite_inv` | The contact table's invariant holds at start and is preserved by every table operation. |
| `stock_T14`, `stock_T14_boot`, `stock_stockUses_nodup` | **T14** (model): in every trace of the stock's use rule, with crashes, restarts, reboots, lying or vanishing peers, and a rollback of the disk **or** the boot memory (not both), no precomputed item reaches the engine twice. **M**: the engine instruction and C ABI are specified, not built; restoring both defeats it (C5, `full_rollback_reuse`). |
| `rotation_t15_erase`, `rotation_plan_sends_perm`, `rotation_plan_pool_bound`, `rotation_plan_generations` | **T15** (model): for two input lists of the same length the connection rotation performs the same actions once payloads are erased; every position is sent once. **Not yet used by the session.** |

T10's controller half (every database write is nonce ‖ sealed blob with a fresh joint nonce) is
listed as not proved in `Security.lean` section 8. The database nodes are outside this repository
(A6).

### 3h. Enforcement: what keeps the code inside what the theorems are about

`scripts/lint_node.py` (8 checks, all on by default; 0 findings at `30c2ce3`):

| Check | What it enforces |
|---|---|
| `io-baseline` | I/O primitives (`IO.FS.*`, `IO.Process.*`, `IO.getEnv`, `IO.println`, `IO.getRandomBytes`, …) only in `TlsMpc/Node/Channels.lean` and `Worker.lean`; no site anywhere else under `TlsMpc/Node` or in the controller root; `IO.getEnv` exactly once (`Config.read`). |
| `escape-hatches` | No `sorry`, `admit`, `native_decide`, `bv_decide`, `ofReduceBool`, `implemented_by`, `extern`, `unsafe`, `opaque`, `axiom`, `csimp`, `skipKernelTC` or `partial def` in `TlsMpc/Node` (these would bypass `private` or the proofs). |
| `emitter-isolation` | No circuit emitter imports a `TlsMpc.Node` module (the circuit cache is keyed by the emitter binary). |
| `secret-val` | `Secret.val` / `Secret.mk` / `expose` only in `Secret.lean`, `Engine.lean`, `Channels.lean`, `Reveal.lean`, `Local/*`. |
| `message-fields` | `Messages.lean` mentions neither `Secret` nor `Handle` (with `Messages.checkPublic`, T9). |
| `flow-calls` | The worker pipe (`.call`, `.callArray`, `.pipe`, `.recording`), operation codes, `Legacy.*`, `inputOwn` and the `Reveal.*` makers appear only in the flow implementations (`Flows/*Legacy.lean`, `Flows/*Backend.lean`, `Runner.lean`, `Select.lean`) and where they are defined. |
| `session-state` | The controller root is a three-line file; session state is threaded explicitly (references only in `State.lean`, `Pool.lean`, `Start.lean`). |
| `ordering-sites` | `Flow.Send.request` and `Flow.Send.requestDevices` appear exactly once (`Session/Send.lean`), `Flow.Refresh.scratchCommit` once (`Session/Store.lean`): what makes ORD-1/ORD-2 about every request and commit. |

Other checks:
* `scripts/check_axioms.py` runs `lake env lean TlsMpc/Security.lean`, requires exactly one
  `#print axioms` per restated theorem, and fails on any axiom other than `propext`,
  `Classical.choice`, `Quot.sound` (`Lean.ofReduceBool` allowed only for `bv_decide` dependents;
  today none has it). Output: `SECURITY_AXIOMS.txt`, **783 entries, all standard axioms**; 3
  depend on a `bv_decide` proof and still show only the standard axioms.
  `scripts/check_axioms_mathlib.py` does the same for `proofs/`.
* `Messages.checkPublic` at build time (T9).
* **Golden records** (`tests/golden/`, four sets: malicious and semi-honest, `--runs 2 --signup` and
  `--runs 0 --db`): masked records of what each controller sent to the server and which server
  bytes it revealed or withheld; a later run must compare equal (`scripts/compare_records.py`).
* **Real-engine fixtures** (`node_worker/tests/e2e_s10.py` … `e2e_s16.py`, `e2e_batches.py`,
  `s11_program_checks.py`) run the exported scripts' vectors on the real engines, with injected
  cheating cases that must abort as in Lean.
* **Lean-generated vectors** (`node_worker/tests/*_vectors.txt`): the Rust `check` and interpreter
  against Lean's on generated batches (B1, B2).
* **The strict manifest** and the script kernel layout checks (section 2.3).

---

## 4. What the argument rests on

### 4.1 The trusted base (assumed; not planned to be proved soon)

| Item | Gap id | What is trusted |
|---|---|---|
| Lean kernel and three axioms | — | `propext`, `Classical.choice`, `Quot.sound`; `ShareCommon.shareCommon'` (used by the translation validators). |
| The MPC engines | A1, A3 | emp-ag2pc and the field engine compute what they are asked, reveal nothing else, abort on cheating; OT, garbling, AES, SHA-256 and the statistical parameters; triples produced ahead of use (NEEDS_REVIEW 1, open review items: one Delta across pools, bucket size, ordering). |
| The engines' C ABI and the legacy C++ | A2 | `engine_abi.cpp`, `legacy_abi.cpp`, and **all of the C++ sequencing behind `legacy_dispatch` — i.e. every operation on the default path.** |
| SHA-256 commitments | A4 | Hiding and binding (`IdealCommit`); the peer's value fixed per message. |
| The Lean compiler and runtime; `Channels.lean` I/O | A5 | Including that the deployed monad-generic definitions behave as their model instances (A8). |
| The Rust worker | B1–B5 | `handles.rs` `check` (transcription of Lean's `Engine.check`, tested on 137 Lean-generated batches), `interp.rs`, `program.rs`, `loader.rs`, `agree.rs`, the pipe; `node_stock`; `node_daemon`. |
| File loaders | B3 | The Rust and C++ loaders parse circuit and layout files as `parseFlat`/`parseLayout` do; `selection`. |
| Script backends' IO glue | F17, F39, F55, K6, J10, J28 | `TlsBackend`, `ReceiveBackend`, `SendBackend`, `JoinBackend`, `RefreshBackend`, `Select`; the runner's IO loop. |
| Transcriptions | E3, E5, section J's J1 and J2 (not the join gaps of the same numbers) | Sealed sender v1 and PreKey framing from libsignal; Kyber-1024 reference against libcrux vectors; Signal-Server request formats; RFC transcriptions (TLS key schedule and records, WebSocket, SHA-1, base64, UUID, UTF-8). |
| OS randomness | — | `Channels.random` (the only randomness source on the Lean side). |
| The database nodes | A6 | Outside this repository. |

### 4.2 Named modelling hypotheses that appear in theorem statements

| Hypothesis | Where it appears | Status |
|---|---|---|
| A8: instantiation of monad-generic definitions | Every **C-gen** theorem (T1, ORD-1, ORD-2, T11) | Assumed (free theorem of the type; Lean cannot state it). |
| `Faithful` (D8) | `receivePolicy_t1_all`, `receivePolicy_t1_start` | Assumed for legacy op 43; function-level support for the script backend (3a.2). |
| `Keeps` / `KeepsHead` | T1 | Discharged for the session's steps (`receivePolicy_keeps_afterRecord`, `receivePolicy_keepsHead_afterRecord`). |
| `Loaded`, `WordLoaded`, `ProgsLoaded`, `GhashLoaded`, `SecretsLoaded` (and on the branch `FirstWordLoaded`, `FirstByteLoaded`, `FirstSignalLoaded`, `RestLoaded`) | Script theorems (3a.4, 3d) | "The circuit or program loaded under this name computes its Lean definition with these marks." Partly discharged by `kernel_loaded`; what remains is cache/manifest integrity, the loaders, `selection` (F1, B3, K3). |
| `FieldInverse` | Field-program and curve theorems | True (`toZMod_inverse`, proofs/); kept as a hypothesis in the main package (F2). |
| `CompleteAddition`, `AddClosed`, `ExtClosed`, `RecipientOnCurve`, `EulerCriterion`, `TwoNonSquare` | S11 honest runs and liveness | Each a theorem in `proofs/` (F22a, F28, F33); joined by name, not by import. |
| `IdealCommit` | `prand_b_ideal`; the offset distributions | Assumed (A4). |
| H2: recipient point nonzero and killed by ℓ | Instantiated offset theorems | Proved for the base point only. |
| Width hypotheses `KemWidths`, `SessionWidths`; kernel signatures as explicit marks | S15, S12, S11 WF | Assumed in Lean; the Rust loader checks them at start (F43, F14a, F25c, F38). |
| Wiring (`hframe`, `hmask`, `built`, `paired`, `wired`, `hcert`, `hpend`) | `serverReceives_accepted` and other end-to-end kernel theorems | On the default path the C++ wiring is assumed (E2); on the script path mostly proved (`s13_send_accepted`, `s14_verified_wiring`), except J6 (`hcert`, `hpend`). |
| `contactKey_spec`'s shares below p | The contact key | Not checked by the kernel. |
| SHA-256 keyed by a seed is a PRF | Rotation's shuffle | Stated, not used in proofs (H7). |

### 4.3 What applies to the path that runs by default

| Guarantee | Default (all-legacy) | Script path (`SIGNAL_SCRIPTS` = `closedSet`) |
|---|---|---|
| T1 reveal policy | **Yes** (C-gen), with `Faithful` assumed for C++ op 43 | **Yes**, with `Faithful` supported at function level; IO glue unverified |
| T8 request templates; parsers; TLS reservations | **Yes** (controller code) | **Yes** |
| ORD-1, ORD-2, T11 (deliverJob), versions | **Yes** | **Yes**, plus script-level `s13_send_state_order`, `s15_ord2_commit` |
| Lowering, printing, `kernel_loaded` | **Yes** (same manifest kernels) | **Yes** |
| Kernel specifications, gating, T7, T13 | **Yes** for the kernels; the C++ wiring between kernels is assumed (E2) | **Yes**, wiring mostly proved |
| V3 field programs | **No**: the legacy C++ evaluator's own division masking is not modelled | **Yes** |
| T3 per operation (what is opened, against any adversary) | **No**: bounded only by the kernels' open marks and specs; the C++ that sequences and opens is trusted (A2, F5) | **Yes** in the model (kinds for every flow; values for most, 3a.4) |
| T4 honest runs | **No** | Most flows (3d.2); receive on a branch |
| Mask generation (cut-and-choose) | **No** (C++ `dyn_word_mask.h`; C4) | Lean script proved in the model; probability bound for the model (3e) |
| T12, the open rule, `runner_drive_model` | **No** (legacy operations are not scripts); per-batch agreement still applies (Rust/C++, tested) | **Yes** (model); the runner's IO loop unverified |
| Offset sampling distributions (proofs/) | About the rule (mine XOR peer) mod 2²⁵², which the C++ implements as read from source | The same rule in the scripts |
| Stock T14, rotation T15 | Models; not in the session | Same |

In short: **on the default path, what is proved is the controller (T1, T8, ordering, results) and
the circuits; what each worker operation opens and in what order is the C++'s, trusted.** The
script path replaces that trust by model-level theorems plus the unverified IO glue and the Rust
interpreter.

### 4.4 Open gaps, by severity

Every section of `PROOF_GAPS.md`, summarised. Ids are that file's.

**1. Structural: what keeps this from being one theorem.**
* A7 — no end-to-end theorem with a simulator.
* A2, F5 — the default path's operations are C++; their reveals are bounded by kernel theorems only.
* A1, A3, A4, A5, A8 — engines, cryptography, ideal commitments, compiler, instantiation (4.1).
* F17, F39, F55, K6, J10, J28, J31 — the script backends' and the runner's IO glue (several
  functions are proved equal to their definitions and called by name; the glue itself is not
  modelled).

**2. Assumptions inside theorem statements** (section 4.2): D8 `Faithful`; F1, B3, K3, F53 (`Loaded`
family, loaders, `shapedCircuit`); E2 and J6 wiring; F14a, F25c, F38, F43, J21b widths and signatures
(loader-checked at start, fail closed); E7 (no item field starts with NUL); E1 (most kernel specs are
against the repository's own compositions).

**3. Openings with no value-level bound.**
* G1 `handshakeShare`, G2 `assignStatus`, G4 legacy `jointRandom`: no bounding theorem.
* F24, F36, F47, K1, F20a: value-level T3 missing for the curve flows' other openings, whole receive
  and refresh runs, the ceremony's op 80, the B-honest TLS open; their **kinds** are proved.
* D2 (accepted one-byte allowance); D3, D4 (WebSocket frame and chat-response parsers: no
  whole-message fail-closed theorem; the reverse Utf8 direction); D6 (`reply`'s id under a
  hypothesis); D5 (record splitter limit); D7 (hardening: varint ≥ 2⁷⁰, unchecked one-byte length,
  empty envelope accepted by builders).
* F25d — `lift-point`'s validity bit is public in any flow (by design, noted).

**4. Correctness of honest runs (T4) not yet through `jointRun`.** F22 (`prepareSecond`,
`prepareContacts`), F22c, F22d, F27; F13a (handshake scripts); F35 (receive: closed on the branch);
F42 (refresh KEM and session step); F51 (multi-device send), F59a, F59b; J7, J16 (joins' values); K4
(registration record phase); F8, F37, F44, J15, K5 (WF; most closed on the branch for F8, F37).

**5. Curve and probability.** H1 (#E = 8ℓ), H2, H3 (X25519 on the twist), H5 (two unmodelled aborts
of probability 2⁻²⁵⁶ and 2⁻²⁵²), H7 (PRF), F12 (uniformity of the composed arrangement; SHA-256 as
random oracle), F26 (`randomPoint` uniform), F34, C4, and the missing 16/22 instance (3e).

**6. Session level.** I1 (non-recovery path checks only its own acknowledgement: argued), I2 (T11 at
the report level), I3 (`bumpIn_absent` hardening), I4 (ORD-2 recheck after S15: rebuilt against the
tree, `STACK_NOTES.md` 11.2), I5 (settings agreement, `Secret`, flow-calls: by construction and
lint), I6 (Close only at an orderly end, keepalive timing: tested).

**7. Models not in the running code.** C5 (stock), T15 rotation (not used), C4.

**8. Tested only.** B1, B2, B4, B5, B6 (`openBoolTo` never run), F25a, F29, F30, F37 (main), F54,
J14 (runner test coverage), F19, F40, F48, F56 (pair tests with stand-in circuits; real-engine
fixtures pass).

**9. Small, engineering, or notes.** D9, E6, E10, F3, F4 (model does not enforce marks, `once`,
freshness: argued), F59c, J3 (only the non-hinted curve path is joined), J5, J17, J18, J19
(released on the branch), J20, J22b, J24, J27, J29 (manifests extended by hand from the cache), K2,
K8–K11, F49.

**Closed** (moved to the Closed table, each with theorems): C1, C2, C3, D1, F7, F9, F10/F21/F50,
F11/F31, F13–F16, F18, F20, F22a, F25, F25b, F28, F32, F33, F57, F58, H4, H6/G3, J1, J2, J4, J8,
J9, J11, J12, J13, J21, J22, J23, J25, J26, J30 (engineering), K7, K12.

### 4.5 Known functional defects and limits

* **`bundle-seal` is one byte short for the smallest official text class** (NEEDS_REVIEW 3f item 7,
  PROOF_GAPS F59d): for an 89-byte official text to a contact with an unanswered device, the
  multi-device send aborts (`s13_bundleOut_record_length` proves the width). Fails closed, nothing
  wrong is released; reachable under `--recovery devices --profile libsignal`; not reachable with
  the product's ≥ 200-byte texts. Not fixed.
* A refused send overwrites the stored text slot (ratchet state preserved, record not byte-identical;
  E10).
* J17: an evicted contact's prepared offset state is never freed. J3: hinted programs not joined.
* The produced manifests do not list every shape the stages use; the local and compact sets were
  extended by hand from the circuit cache (J27, J29, K8); production manifests must be regenerated
  from complete deployment settings (`STACK_NOTES.md` 11.3 item 2).
* The ceremony's limits (section 1.3) and the identity key in the clear.

---

## 5. Evidence beyond proofs

### 5.1 What has been run

| What | Path | Result |
|---|---|---|
| Golden records, `--runs 2 --signup` and `--runs 0 --db`, malicious and semi-honest | legacy (default) | Equal to `tests/golden` (re-checked after the last change). |
| The same four, with the closed script selection, `--strict-produced` | scripts | Equal to `tests/golden` in both modes (`STACK_NOTES.md` 11.2). |
| Multi-device, app, sustained/restart, broadcasts with link delay, ceremony (both modes), hinted, fingerprint, circuits 1,3, ten `--recovery` stages (classify, devices, refresh-retry, identity, unauthorized, drop, throttle, bundle-fault, resume, hang) | scripts (malicious; some semi-honest) and legacy | Pass; `--recovery devices --profile libsignal` fails closed on both paths (4.5). Semi-honest not run for most recovery stages (11.3 item 7). |
| Real-engine fixtures `e2e_s10.py` … `e2e_s16.py`, `e2e_batches.py`, `s11_program_checks.py` | scripts | Pass in both modes (where built); injected cut, bucket, bit-block, agreement-share, hinted-lift, bit-table and point-encoding deviations abort as in Lean. `e2e_s12.py handshake`, `e2e_s14.py flow`, `e2e_s15.py refresh` modes not built (the same flows run in the harness). |
| Lean vectors vs Rust (`node_worker/tests/*_vectors.txt`, `RunnerTest.lean` 37/37) | scripts | Byte-identical regeneration; all `check … ok`. |
| Two runs against Signal's real service (2026-11-12), malicious, strict, libsignal profile | **legacy** (scripts were not selectable then) | First: the signup was received, stored and acknowledged; the reply failed closed on a missing `bundle-shape 8192` kernel. Second: signup received (2,265-byte envelope, 484 bytes revealed, nothing refused), reply answered 409, one refresh of three devices, "delivered after device refresh"; the owner confirmed the text arrived. |

### 5.2 Defects found by the proof work (evidence that the proofs bite)

| Defect | How found | Status |
|---|---|---|
| **Reveal-policy leak on an over-long varint**: an 11-byte varint made the scanners read "unfinished", so the controller revealed the rest of the message, including a delivered envelope's sealed content or a prekey response body (NEEDS_REVIEW 3f item 5). | Proving T1 (counterexamples `ReceiveTest.overlongRequest` / `overlongResponse`) | Fixed in the controller; `receivePolicy_scanBody_tooLong` and siblings; T1 now holds. |
| **Mask key reused across control replies in one drain** (RFC 6455 §5.3). | T8/control-frame proofs | Fixed in S4; `wsControl_replies_fresh_masks` (a concrete two-pong case). |
| **`receive-text` opened bytes a protobuf parse rejects** (a body longer than its DataMessage; for a signup a malicious sender chose which bytes count as the token). | T13 proofs (`overlongBody_accepted`) | Fixed in the emitter batch and re-lowered 2026-11-12 (`EMITTER_BATCH.md`); `receiveAcceptText_overlongBody_refused`, `receiveAcceptText_accepted_iff_reference`. |
| **`bundle-slot` accepted inconsistent width bytes**; no kernel-only fix was possible with `0` padding. | Bundle proofs | Fixed (NUL filler), re-lowered; `bundleSlot_inconsistent_width_refused`, `bundleSlot_zero_padding_ambiguous`. |
| **`bundle-seal` one byte short** for the 89-byte official class. | S13 proofs (`s13_bundleOut_record_length`) | Not fixed; fails closed (4.5). |
| **J1: one mask slot for op 50's two agreements** — the openings z₁·m and z₂·m revealed z₁/z₂, a value derived from contact-identifying keys. | Joining S14 with S11 | Fixed; `j1_openFirst_reads_once`, `j1_session_reads_once`. |
| J1's sibling: S15's three curve calls shared one pool (step 0 always aborted). | Same | Fixed; `j1_refresh_pools_disjoint`. |
| **J21: the receive script sliced a 236-byte receiver record; the kernel outputs 200.** | First real-engine layout check, then proved | Fixed; `j21_session_receiver_bits`, `j21_receiverBytes`. |
| **J22: the accepted selection failed at run time** (legacy ops 33, 45 refused); K12: the ceremony's asserted list missed `account`. | Closure proofs | Fixed as a selection rule; `j22_check_closed`, `j22_refusals`, `j22_ceremony_needs`. |
| D9: the record loop's fuel. | C1 proof | Now fails closed if an engine reports a longer record later. |

Found by **runs**, not proofs (listed for completeness): J25 (kernel names read from the wrong
variable), J26 (report counted only pipe operations), J30 (a send dropped its contact's
preparation, so every later send prepared the contact again: twice the legacy time per message;
fixed in the glue, no theorem), J27/J29 (manifest gaps).

---

## 6. How to check this yourself

All heavy jobs go through `scripts/guarded.py` (memory cap); never run two at once.

```
# 1. The theorems and their axioms (light: reads existing .olean files)
python3 scripts/check_axioms.py                 # runs `lake env lean TlsMpc/Security.lean`
#    expect: "783 restated theorems; 3 depend on bv_decide ... OK: only allowed axioms"
#    output: SECURITY_AXIOMS.txt (checked in; a change of axioms shows as a diff)

# 2. The Mathlib package (separate; nothing executable imports it)
cd proofs && python3 ../scripts/guarded.py 12 3600 lake build TlsMpcProofs
python3 scripts/check_axioms_mathlib.py         # writes proofs/SECURITY_MATHLIB_AXIOMS.txt

# 3. The lints (light)
python3 scripts/lint_node.py                    # 8 checks; expect 0 findings
python3 scripts/lint_node.py --report           # what each check sees

# 4. Builds (heavy: through guarded.py --heavy)
python3 scripts/guarded.py --heavy 16 3600 lake build TlsMpc TlsMpcSecurity
cd node_worker && cargo test --offline --no-default-features --release   # Rust tests on Lean vectors

# 5. The local harness against a local Signal-Server, compared with the golden records
python3 local_signal_server/check_signal_service_local.py malicious --runs 2 --signup --record DIR
python3 scripts/compare_records.py tests/golden/malicious-runs2-signup DIR
#    with scripts: add --worker node --strict-produced --scripts <the ten groups of closedSet>

# 6. Real-engine fixtures for the scripts (heavy; arguments and modes in each script's docstring)
python3 node_worker/tests/e2e_s10.py   (… e2e_s16.py, e2e_batches.py, s11_program_checks.py)
```

Where to look:
* **The theorems**: `TlsMpc/Security.lean` (sections 1–7, with section 8 the in-Lean list of what is
  not proved and section 9 the `#print axioms` lines); `proofs/TlsMpcProofs/SecurityMathlib.lean`.
* **What is not proved**: `PROOF_GAPS.md` (and its Closed table); kernel defects in
  `NEEDS_REVIEW.md` 3f.
* **Everything that leaves a node**: `TlsMpc/Node/Messages.lean` (message types),
  `TlsMpc/Node/Channels.lean` (the only I/O), `TlsMpc/Node/Reveal.lean` and `Types.lean`
  (`RevealKind`), `node_worker/src/link.rs` and `server.rs` (what the shell can put on the peer link
  and the server socket).
* **The reference the reveal policy is checked against**: `TlsMpc/Node/Policy/ReceiveSpec.lean`.
* **The ordering assumptions**: `TlsMpc/Node/Session/Events.lean` (header).
* **What runs by default and what is selectable**: `STACK_NOTES.md` sections 10–11;
  `TlsMpc/Node/Flows/Select.lean`.

---

## Appendix: places where the sources are out of date or disagree

These do not change the argument above; they are listed so a reader is not misled by them.

1. **Privacy policy for the identity key.** An earlier split (2026-11-10) kept the identity private
   key secret-shared; `CEREMONY.md` (owner's decision 2026-11-11) puts all account keys in the clear
   on both nodes, and states the consequence (a node colluding with the server can read who signs
   up). This document follows `CEREMONY.md`.
2. **"Takes effect after the re-lowering"** (Security.lean section 3a and section 8, NEEDS_REVIEW 3f
   items 1–2) — `EMITTER_BATCH.md` records the re-lowering of 2026-11-12, with the changed kernels in
   all three manifests.
3. **T10.** Security.lean section 5's header says "the database nonce rule (T10) is NOT proved";
   section 7a proves the worker flows' part (`contactsWrite_write_fresh`); section 8 lists T10 as
   open. Both are right: the worker part is proved for the scripts, the controller's database-write
   part is not.
4. **D8.** PROOF_GAPS D8 says the script backend's `reveal_value`/`range_value` are on an unmerged
   branch; they are on the main line as `s12_tls_reveal_value` and `s12_tls_range_value`
   (function level).
5. **Security.lean header** says no entry states `idealCommit` yet and the commit-then-open
   exchanges are C++ today; `prand_b_ideal` takes `IdealCommit` and the scripts do the exchanges.
   Section 7-reveal's "the flows are still worker operations" is true of the default path only.
6. **`SECURITY_AXIOMS.txt`** ends with "3 of 785 entries" while it lists 783 restated theorems (plus
   three non-restated `bv_decide` entries).
7. **The S10 deployed mask profile (16/22)** has no instance in `proofs/` (section 3e), though the
   notes speak of the cut-and-choose bound as closed for the model.
