# Reorganisation plan: one place to audit what a node sends, and the move out of C++

**Describes commit `d6c6cd9`.** Written 2026-11-11, with `SECURITY_MAP.md` (same commit). Section
references such as "A.2" or "B.4" point to that file.

This is one plan for two requests of the owner:
- **The audit request:** "where are the important theorems? it should be easy to look at all the
  external communication a node is doing and easily verify its security properties".
- **The C++ request** (PRODUCT_TODO 12a): "move the conversion and helper protocols and prove
  things about them too", "minimize unverifiable code", and "a coherent plan along with the
  move of C++".

The owner waived reviewing this plan. It is meant to be executed stage by stage as written.
Where a decision was needed, the default is stated and marked **Default**. Section 12 collects
what I am unsure of.

**When it starts.** PRODUCT_TODO 12a queues this work behind an application that works end to end.
All other work on the code has stopped, so the code will not move under the plan. Stages S0–S7
touch no C++ and can start at once.

---

## 1. Rules every stage follows

1. **Nothing moves twice.**
   - A call site moves once: into `Channels` (S5) or into the flow API (S6).
   - The implementation behind a flow function moves once: from a worker operation to a Lean
     script (S9–S16).
   - The C++ shell moves once, to Rust (S8).
   - Pure logic moves once, to its final module (S2).
2. **The harness passes at the end of every stage**, in both modes. The test sets are defined in
   section 10.1.
3. **Never two heavy jobs at once on this machine** (owner's memory: parallel lowering used over
   100 GB). Heavy jobs are those that genuinely conflict:
   - harness runs (they share the local server, its ports, the database nodes);
   - builds that replace binaries a harness run uses: `lake build` of an executable or of the
     `TlsMpc` library, `build_hybrid_v3.py`, cargo builds of `node_daemon` or the provision tool;
   - circuit lowering or manifest production.

   Light jobs never take the lock and run at any time under plain `guarded.py` with a cap of at
   most 12 GB: `lake env lean ONE_FILE` (reads `.olean` files, writes nothing shared), the lints,
   read-only scripts, `cargo check` in a separate target directory, kernel checks that start no
   server.

   Stage S0 adds the lock: `guarded.py --heavy MAX_GB MAX_SECONDS CMD…` (or `scripts/heavy.sh`,
   which forwards to it). macOS has no `flock(1)`, so it is Python's `fcntl.flock` on
   `.deps/heavy.lock`. Every heavy job goes through it, with a realistic cap (harness runs peak
   around 10 GB: declare 16–20) and kept short (one stage set, under about 8 minutes) so the lock
   turns over. A waiting job names the holder and how long it has held the lock every minute.
4. **Emitter isolation.** No module under `TlsMpc/Node/` may be imported by an emitter
   (`EmitFlatKernel`, `EmitWordMask`, `EmitKemKernel`, `EmitCeremonyKernel`, `CircuitInventory`).
   - The circuit cache is keyed by the emitter binary's hash (`kernel.h:127-133`), and a
     manifest belongs to one emitter binary.
   - So changing a module an emitter imports forces re-lowering everything, which is heavy.
   - S0's lint enforces this. Stages that must change an emitter (P3; field programs in S9) say
     so and schedule one re-lowering, alone.
5. **One source of randomness on the Lean side.** Every random value the Lean code needs comes
   from `Channels.random` (the OS generator). After S9 that covers mask contributions,
   commit-then-open values, scalar summands and program masks.
6. **No new axioms.** The only allowed axioms are `propext`, `Classical.choice` and `Quot.sound`
   (and `Lean.ofReduceBool` for the 5 `bv_decide` uses, if a build shows they need it).
   - Not allowed: `sorry`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`.
   - No new `partial def` in `TlsMpc/Node`.
   - **Superseded 2026-11-12 (owner asked "why not use mathlib?"; decision: use it for proofs).**
     Mathlib is added as a dependency of a separate proof-only library that no executable
     imports (node binaries, the kernel emitter and the circuit cache key must not depend on
     it). Use it to turn the quadratic-residue hypotheses of the hinted lift into theorems, to
     state hiding as real probability where that is clearer than the bijection form of section
     7.0, and for the cut-and-choose counting bound (P7 is no longer "not done" by default).
     The Edwards group law stays a hypothesis unless proved separately (Mathlib has it for
     Weierstrass curves only). The bijection statements of section 7.0 remain acceptable and
     need not be redone. Also: the stage sizes in this document are human-engineer estimates;
     the owner expects agents to go much faster, so do not treat them as schedule.

---

## 2. The final shape

```
┌───────────────────────── Lean controller: TlsMpc/Node/ ─────────────────────────┐
│ Main.lean        argument parsing → one Session; executable root is a 3-line file │
│ Session/*        the loops of today's `main`: Serve, Send(deliverJob), Receive,   │
│                  Ceremony, Delete, Pool (connections); no I/O primitive           │
│ Policy/*         pure decisions: Receive (reveal budget), Request (templates),    │
│                  Recovery, Circuits/Rotation, Journal, Clock, Results             │
│ Flows/*          Lean scripts over the engine instruction set: Random, Masks,     │
│                  Convert, Inversion, Curve, Ghash, Tls, Contacts, Account, Send,  │
│                  Receive, Refresh, Upgrade, Ceremony   (+ Stock later)            │
│ Local/*          arithmetic on public values and on this party's own secrets:    │
│                  Field, Edwards, Ghash, Commit, WebSocketAccept                   │
│ Reveal.lean      THE list of openings: one function per opening (SECURITY_MAP B) │
│ Engine.lean      Instr, Script (free monad), skeletons, the batching interpreter │
│ Engine/Model.lean  ideal two-party semantics of Instr (for the theorems)        │
│ Messages.lean    every message type that leaves the controller (no Secret field) │
│ Channels.lean    THE I/O module: the only file with IO primitives (+ Worker.lean) │
│ Worker.lean      pipe codec and process spawn (today TlsWorkerPipe/Process)      │
│ Secret.lean, Types.lean, Config.lean                                             │
└──────────────────────────────────────────────────────────────────────────────────┘
TlsMpc/Security.lean   every important theorem restated, with plain docstrings and #print axioms
          │ pipe: agreed instruction batches ↓   replies (opened values, exchanges, records) ↑
┌──────────────────────── node_worker/ (Rust, trusted shell) ──────────────────────┐
│ pipe.rs  agree.rs  link.rs (control link to the peer: PeerFrame enum)            │
│ server.rs socks.rs connections.rs (sockets only)  loader.rs (manifest, flat,     │
│ layout, field programs V3)  handles.rs (handle table + open rule)                │
│ interp.rs (executes Instr)  program.rs (field-program evaluator)  engines.rs (FFI)│
└──────────────────────────────────────────────────────────────────────────────────┘
          │ C ABI, handles only (engine_abi.h)
┌──────────────── C++ engines (trusted, unchanged in substance) ───────────────────┐
│ emp-ag2pc DynSession + TripleStock (or ShSession);  FieldEngine (MP-SPDZ based)  │
└──────────────────────────────────────────────────────────────────────────────────┘
node_daemon/src/: channels/{application,peer,controller,disk}.rs (typed), scheduler.rs (no I/O)
```

### 2.1 What a reviewer reads to see "everything leaving a node"

1. **`TlsMpc/Node/Messages.lean`.** Every outbound message type of the controller. Each
   constructor's docstring gives:
   - the class (P, O, OWN, or S to own disk);
   - the theorem that says what it is a function of (section 8).
2. **`TlsMpc/Node/Channels.lean`.** One function per channel and message kind. It is the only
   controller file with an I/O primitive. A lint guarantees this.
3. **`TlsMpc/Node/Reveal.lean`.** The complete list of values released from the engines or from
   this party's own secrets, one function each. Each docstring cites its theorem.
4. **`node_worker/src/link.rs` and `server.rs`.** The two enums of what the trusted shell can put
   on the peer link and on the server socket (section 5.6).
5. **`node_daemon/src/channels/*.rs`.** The daemon's four channels, as typed enums.
6. **`TlsMpc/Security.lean`.** The theorems.

### 2.2 Trusted and unverified at the end

- **The engines and their C ABI:** emp-ag2pc with the validated-v3 patch and triple stock, the
  field engine, and about 400 lines of ABI glue.
- **The Rust worker:** estimate 2,000–2,500 lines. Of these, `interp.rs`, `program.rs` and
  `handles.rs` (the open rule) are the security-relevant part, about 600 lines.
- **The Rust daemon.**
- **`public_auth`, `handoff_client`, the KEM tool and the key tool.**
- **The Lean compiler, its runtime and `ShareCommon.shareCommon'`.**
- **Assumptions stated in theorems:**
  - that the Edwards formulas are the group law;
  - the quadratic-residue facts used by the hinted lift;
  - ideal commitments (SHA-256 as a hiding and binding commitment).

### 2.3 Gone at the end

- `service_kernels.h` (969 lines) and `tls_kernels.h` (311);
- `dyn_word_mask.h`, `x25519_fast.h`, `split_ecdh.h`, `edwards_points.h`, `hinted_points.h`,
  `gcm_shares.h`;
- `field_program.h` (its evaluator moves to Rust, without the special division logic);
- `kernel.h` (to Rust `loader.rs` / `handles.rs`), `peer_link.h`, `profile.h` (to Rust);
- `tls_worker_v3.cpp`;
- libsodium and the C++ use of OpenSSL bignums;
- the Python circuit cache at run time;
- the private-profile and fixture operations (18–29, 31, 34, 35, the TEST producer, the service
  fixture).

---

## 3. The I/O module: `TlsMpc/Node/Channels.lean` and `Messages.lean`

Every `IO.FS.*`, `IO.Process.*`, `IO.getEnv`, `IO.println`, `IO.eprintln`, `IO.getRandomBytes`,
`IO.sleep`, `IO.monoMsNow` and `Std.Time.Timestamp.now` of the controller moves here. Today that
is about 120 sites in `main` (SECURITY_MAP A.9).
- The worker pipe stays in `Worker.lean`. It is reached only through `Engine` (section 5).
- Session code is written against the `Channels` record. That is the pattern
  `TlsClient.Backend` and `TlsApplication.Backend` already use. The real record is built once,
  in `Channels.real`.

### 3.1 Message types (`Messages.lean`)

No type in this file has a field of type `Secret _` or `Handle`. The lint in S0 checks that by
pattern.

```lean
namespace TlsMpc.Node

/-- To the other controller (through the worker's control link). Today's 14 `swap` sites. -/
inductive PeerMsg where
  | clock (ms : Nat)                                   -- agreedNow 1485, agreedClock 2114
  | submitted                                          -- dbSubmit 1537, dbSubmitSoft 1953
  | acknowledged (b : Bool)                            -- dbSubmitSoft 1957
  | parity (file : DbParity)                           -- dbRead 1556: handoff_client output, public by design
  | committedNodes (v : Vector Bool 16)                -- dbDeal 1591
  | absentDigest (h : Hash)                            -- 1674, 2253
  | journal (entries : List JournalEntry)              -- 2756
  | resultsDigest (h : Hash)                           -- 2913
  | serveTick (job : Option Hash) (stop : Bool) (ms : Nat)   -- 2992
  | settingsDigest (h : Hash)                          -- NEW (S4): agreed settings at session start
  | ceremonyInput (name : CeremonyInput) (bytes : ByteArray) -- 3165, 3233; keys.json is OWN
  | flow (m : FlowMsg)                                 -- after S9: commitments and openings of
                                                       -- own secrets, ONLY via Reveal (section 4.3)

/-- To the Signal server. -/
inductive ServerOut where
  | clientHello (h : ClientHelloBytes)   -- built by TlsWire from Config + Opened values
  | record (r : Opened .sealedRecord Bytes)

inductive DbCall where                   -- handoff_client commands (A.3)
  | read (auth : ReadAuthority) | parity | verifySignatures | paritySum | combine
  | deal (token : SignupTokenFile) (id : ContactId) (session : Opened .jointRandom Bytes)
  | writeBlob (auth : WriteAuthority) (id : Option ContactId) (version : Nat) (blob : SealedBlob)
  | tokenId (text : Opened .receivedText String) | delete (request : SignedDelete)

inductive DaemonLine where               -- controller stdout
  | ready (connections : Nat) | jobResult (r : AgreedResults) | signup (id : ContactId)
  | finalReport (r : FinalReport)

inductive RecordEvent where ...          -- one constructor per today's recordEvent kind (17 + recordSend)
inductive LogLine where ...              -- one constructor per stderr site (A.6)
inductive ShareFile where | password | recovery | credentials | testStore (id : ContactId)
```

### 3.2 The channel record (`Channels.lean`)

```lean
structure Channels where
  -- the other node (implemented by Engine.exchange: the worker's control link)
  exchange    : PeerMsg → NodeM PeerMsg          -- the reply's constructor is checked here
  -- database nodes
  db          : DbCall → NodeM DbReply           -- one function, typed calls and replies
  -- application (via the daemon)
  nextJob     : NodeM (Option Job)               -- DIR/job.json + request + message
  stopAsked   : NodeM Bool                       -- DIR/stop
  report      : DaemonLine → NodeM Unit
  -- local tools
  checkCertificate : CertificateQuery → NodeM Bool                    -- public_auth
  kemDecapsulate   : Secret KyberKey → KyberCiphertext → NodeM (Secret KemSecret) -- key on stdin
  -- disk
  record      : RecordEvent → NodeM Unit         -- SIGNAL_RECORD
  journal     : JournalAppend → NodeM Unit
  readJournal : NotifyId → NodeM (List JournalEntry)
  saveShare   : ShareFile → Secret Bytes → NodeM Unit   -- mode 0600, write then fsync then rename
  loadShare   : ShareFile → NodeM (Option (Secret Bytes))
  ceremonyFile : CeremonyInput → NodeM (Option ByteArray)
  readExport  : NodeM (Option ExportFile)        -- TEST: our keys (Secret OwnKey), contacts (Secret)
  -- logs
  log         : LogLine → NodeM Unit
  -- environment of the process
  clock       : NodeM Nat                        -- local milliseconds; agreement is Policy/Clock
  monotonic   : NodeM Nat
  sleep       : Nat → NodeM Unit
  random      : (n : Nat) → NodeM (Secret ByteArray)   -- rule 5: the only randomness
```

`Config` is read once by `Config.read`, which lives in `Channels.lean`; everything else receives
the value. Its fields:
- every `getEnv` of A.7;
- `TestHooks`: all `SIGNAL_LOCAL_*`, the pauses, the timestamp. It is `none` unless the process
  was started with `--test`.

The server, the engines and the worker pipe are **not** in `Channels`. They are `Engine`
instructions (section 5), because what reaches the server is decided by which engine output
the scripts open.

### 3.3 Mapping from today's code (controller line numbers at `d6c6cd9`)

| `Channels` / `Config` | Today |
|---|---|
| `exchange` | `swap` (1467) and its 14 uses |
| `db` | `dbTry`, `db`, `dbParty`, `dbJson`, `dbSubmit`, `dbSubmitSoft`, `dbRead`, `dbDeal` (1455-1597, 1947-1958); `db-delete` (1297-1316); `token-id` (1800-1804) |
| `report` | final report (3333-3347), `emit` (2935), signup event (1852-1854), `ceremony` summary (1293), `recovery-check` (1196) |
| `record` | `recordEvent` (1168) and its 17 uses; `recordSend` (2028) |
| `log` | 1458, 1919, 2172, 2479, 3065 |
| `checkCertificate` | the closure passed to `TlsWorkerProcess.spawn` (1386-1395) |
| `kemDecapsulate` | `decapsulate` (1757-1764): **key moves from argv to stdin** |
| `saveShare` / `loadShare` | 3248, 3249, 3285; 1263; TEST store 1702, 1829, 2295 |
| `nextJob` / `stopAsked` | `serve` (2977-2987) |
| `journal` / `readJournal` | 2894; 2753 |
| `ceremonyFile` | `fileText` (3159-3161), `shared` (3163-3170) |
| `readExport` | 1629, 1749, 1995, 2243 with the parsers 1081-1138 |
| `clock`, `monotonic`, `sleep` | 1484, 2113, 2988, `IO.monoMsNow` (2537, 2999), `IO.sleep` (1315, 2543, 2795, 2802, 3064, 3237, …) |
| `random` | `freshShare` (1433) |
| `Config` | every `getEnv` (36 sites), the ceremony's configuration reader (1240-1288), `officialProfile` (1180) |

### 3.4 The daemon, the same way (S3)

`node_daemon/src/` becomes:
- `channels/application.rs`:
  - `enum AppRequest { Notify, Delete, Wait, Events, Status }` with typed replies;
  - the listener;
  - `read_line` / `write_line`.
- `channels/peer.rs`:
  - `enum PeerMessage { Ping, Agree{job}, Start{job,session,port:Option<u16>}, Receive{session,port}, Serve{session,port}, Ended{session}, Finish{job} }`;
  - `seal` and `open`, **with sealed replies**, a per-message nonce, and a replay cache for the
    60-second window (decision in S3).
- `channels/controller.rs`:
  - `SessionEnv`, a typed struct replacing the `env()` calls (today :611-654), with the
    removal list for session-kind variables;
  - the spawn, `supervise`;
  - `enum ControllerLine { Ready, JobResult, Signup, FinalReport }` and its parser.
- `channels/disk.rs`: the paths under `state/`: work, journal, events, logs, serve.
- `scheduler.rs`: today's `Daemon` state machine (jobs, queue, sessions), calling only
  `channels::*`.
- `request.rs`, from today's `lib.rs` `Request`.

`node-daemon.rs` keeps only the wiring.

---

## 4. Public and secret in the types

### 4.1 The types (`Secret.lean`, `Types.lean`)

```lean
/-- A value only this party may hold: its own share or random contribution, or an OWN key.
    It cannot be printed, serialised, logged or sent. Its eliminators are listed below. -/
structure Secret (α : Type) where private mk :: private val : α

/-- A value that left the engines (or this party's secrets) through a function of
    Reveal.lean; `r` names the opening (SECURITY_MAP B). Public: `.val` is unrestricted. -/
structure Opened (r : RevealKind) (α : Type) where private mk :: val : α

/-- An engine value (Boolean wires or field shares); carries no bytes. Allocated by scripts. -/
structure Handle (e : EngineKind) where id : UInt64
```

**The eliminators of `Secret`.** These are the only places `Secret.val` may appear; the lint in S0
and S4 checks it:
- `Engine.inputOwn*`: own private input to an engine;
- `Channels.saveShare`, `Channels.kemDecapsulate`;
- `Local/*` (arithmetic on own secrets; each function returns `Secret` or goes through `Reveal`);
- `Reveal.ownPublicPoint`, `Reveal.commitOpening` and the other own-secret reveals (section 4.3).

**Why this is enough.**
- Anything the controller holds that is not a `Secret` or a `Handle` is public by construction:
  configuration, the application's request and text, `Opened` values, and values computed from
  those.
- No message type (section 3.1) can carry a `Secret` or a `Handle`.
- `Opened` has a private constructor in `Reveal.lean`. So the `RevealKind` constructors, each
  with its function, are the complete list of openings.

**Lean `private` is enforced per file by the compiler, not a security boundary against
metaprogramming.** The S0 lint rejects `unsafe`, `implemented_by`, `extern` and `opaque` in
`TlsMpc/Node`, which are the bypasses.

### 4.2 Secret material held directly by the controller, and where it ends

This covers SECURITY_MAP D.7.

| # | Secret | Today | Becomes |
|---|---|---|---|
| 1 | each contact's additive key share | `dbShare` 1566, `dbDeal` 1578-1597, `freshShare` 1432, TEST store 1702-1717; to op 36 at 10 sites | `DbReply.shares : Secret KeyShares`; consumed only by `Flows.Contacts.key` → `inputOwn` |
| 2 | the account key share | 1635, 1727-1728 | the same |
| 3 | this party's XOR share of the credentials | env 1332-1335; `credentials.share` 1263; child env 1267, 1272; op 47 at 1605, 1723 | `Secret CredentialShare` from `loadShare`. **The ceremony child gets a file path (`SIGNAL_LOCAL_CREDENTIALS_FILE`), never the value** (S4) |
| 4 | the ceremony's password and recovery shares | 3246-3249, 3284-3285 | before S16: an op-80 reply wrapped as `Secret` by a legacy wrapper; after: `openBoolTo` replies (`Secret`); saved with `saveShare` |
| 5 | OWN: identity key, prekey keys, Kyber key and secret | 1085, 1122-1138, op 46 (1642), op 51 (1788), argv (1760) | `Secret OwnKey`. Policy-allowed in the clear, but typed so that it cannot reach a log, a record or an argv |
| 6 | TEST contact records | `readExport`, op 44 | `Secret`, only under `Config.test` |
| 7 | `keys.json` sent to the peer | 3165 | `PeerMsg.ceremonyInput .keys`, with a docstring citing the owner's policy (CEREMONY.md section 4). **Default:** no split |
| 8 | after S9–S12: own random contributions, scalar summands, mask points, GHASH key-power shares | inside the C++ today | `Secret`, created by `Channels.random` or `Local/*`, consumed by `inputOwn` or an own-secret reveal |

### 4.3 The reveal list (`Reveal.lean`)

There is one function per opening. Each returns `Opened r α`, and its docstring names its
theorem. The kinds are SECURITY_MAP B.1/B.2 plus the own-secret reveals. Until a flow moves to
Lean, its functions are **legacy wrappers** that turn a worker reply into `Opened`. They are
replaced by script openings in S9–S16; the list itself does not change.

| Group | Functions (`RevealKind`) | Source today |
|---|---|---|
| TLS | `handshakeRecord`, `finishedAccepted`, `clientFinished`, `recordKindBit`, `recordEvent`, `sealedRecord` (header, ciphertext, tag, accepted), `serverBytes` (precondition: T1's budget), `ghashMaskedPower` (to BOB only: returns `Secret`) | ops 3, 5, 6, 12, 13, 14, 43; `gcm_shares.h:38` |
| Stored state | `blobAccepted`, `sealedBlob` (check, ciphertext) | ops 37/38/54/55/63/64 |
| Send | `counterWidths`, `sealedEnvelope` (status, timestamp, envelope), `ephemeralPublic` | ops 41, 61 |
| Receive | `certificateLength`, `contentShape`, `prekeyShape`, `prekeyIds` (ids, Kyber ciphertext), `signalShape`, `sessionStatus`, `receivedText`, `accessKeyStatus` | ops 50, 51 |
| Refresh | `bundleShape`, `identityChanged`, `deviceStatus` | ops 59, 60 |
| Ceremony | `maskedPassword` (returns this party's `Secret` shares; the opened XOR is public) | op 80 |
| Conversions | `maskedBit`, `maskedWord`, `maskedFieldValue`, `cutCandidates`, `bucketSums`, `referenceFlags`, `bitBlockChecks`, `scalarBitChecks` | B.2 |
| Curve | `maskedDenominator` (the D/Z nodes of field programs and the quotients), `curveChecks`, `liftW`, `liftZ`, `pointValid`, `linkChecks` | B.2 |
| Own-secret reveals | `commitment`, `commitOpening` (joint randomness, offsets, challenges), `ownPublicPoint` (split-ECDH share kA·B, the K₀ half) | `joint_random`, `split_ecdh.h`, `edwards_points.h` |
| Policy-public | `jointRandom` (the XOR result), `parity` (database parity shares: trusted, designed public) | |

---

## 5. The worker after the move

### 5.1 The instruction set (`Engine.lean`)

```lean
inductive Party | a | b
inductive OpenMark | never | public | toA | toB | revealable   -- set at creation (5.4)

inductive Instr where
  -- inputs (handles are allocated by the script: deterministic counters, both parties alike)
  | boolInput   (out : Handle .bool) (owner : Party) (width : Nat) (once : Bool)
                (mine : Option (Secret Bits))            -- some iff this party is `owner`
  | boolInputBoth (outA outB : Handle .bool) (width : Nat) (mark : OpenMark) (mine : Secret Bits)
  | boolPublic  (out : Handle .bool) (bits : Bits)
  | fieldInputBoth  (outsA outsB : List (Handle .field)) (mark : OpenMark) (mine : Secret (List F))  -- input_elements
  | fieldInputBits  (outsA outsB : List (Handle .field)) (mine : Secret (List Bool))               -- input_coins
  | fieldPublic (out : Handle .field) (v : F)
  -- computation
  | run     (k : KernelName) (args : List (FieldName × Handle .bool)) (outs : List (FieldName × Handle .bool))
  | program (p : ProgramName) (instances : List (List (Handle .field))) (outs : List (List (Handle .field)))
  | plumb   (out : Handle .bool) (op : Plumb)            -- slice / concat / pick / interleave; no gates
  | linear  (out : Handle .field) (op : Linear)          -- add / sub / scale / dividePublic
  | mul     (outs : List (Handle .field)) (pairs : List (Handle .field × Handle .field))
  | check                                                -- field engine MAC check
  -- release (data replies)
  | openBool   (h : Handle .bool)                        -- reply: Bits
  | openBoolTo (h : Handle .bool) (to : Party)           -- reply: Secret Bits to `to`, nothing to the other
  | openField  (hs : List (Handle .field))               -- checked_open; reply: List F
  | exchange   (payload : ByteArray)                     -- reply: the peer's bytes (control link)
  -- the server (leader acts; follower receives what the leader forwards)
  | server  (op : ServerOp)  -- select i | connect endpoint (Option Proxy) | send bytes | poll | receive | reset | close
  | drop    (hs : List AnyHandle)
```

- **The skeleton of a batch** is the batch with every `Secret` payload and every `exchange`
  payload replaced by its length.
- **Agreement:** both workers send `SHA-256(session ‖ batch sequence ‖ skeleton)` on the
  control link and compare, **before executing the batch**. That keeps today's rule (agreement
  precedes any action; ops 36/39/47/53 hash only their public part) in one generic form.
- **Op 8 (abort)** stays local and unagreed.

### 5.2 Scripts and batching

```lean
inductive Script (α : Type) where
  | done (a : α)
  | step (i : Instr) (k : Reply i → Script α)    -- Reply i = Unit for instructions without data
```

- Flows are `StateT Counters Script`, so handle ids come from counters.
- **The IO interpreter** (`Engine.runIO`, in `Worker.lean`) accumulates instructions whose reply
  is `Unit`. It sends one batch when the script needs a data reply (an open, an exchange, a
  server poll).
- **Cost:** about one extra cross-node message delay per data reply, for the agreement. A
  message has 6–8 such points against 1–2 operations today: a few ms per message at a 2 ms
  round trip, against about 1.4 s per message.
- **Measure in S9.** If the regression is over 5 % at the harness's `--link-delay-ms 1`,
  implement *deferred agreement*: send the hash at the batch's start and check it before the
  batch's first opening or exchange. That is still before anything that depends on secrets
  leaves.
- **Default:** plain agreement.

### 5.3 The model (`Engine/Model.lean`)

The ideal two-party semantics of `Instr`. This is what the theorems of sections 7 and 8 quantify
over.
- **State:** a store from handles to values (`Bits`, `F`).
- **A joint run:**
  - takes the two parties' scripts and their private inputs;
  - aborts if the skeletons differ;
  - computes every instruction ideally;
  - appends every released value to the **transcript of the receiving party or parties**.
- **The adversary** controls one party's script and inputs entirely:
  - any private values, independently per input instruction, so the values in the two engines
    may be inconsistent;
  - any exchange payloads, as functions of its view so far;
  - abort at any point.

  It cannot change ideal computation. That is the engines' guarantee, trusted (NEEDS_REVIEW 1).
- **The field `F`** is FieldDag's field type, the integers mod p = 2^255 − 19 as used by
  `FieldBits` and `WordMask`.

### 5.4 The open rule (`node_worker/src/handles.rs`)

Every handle carries an `OpenMark`, fixed at creation:

| How the handle is created | Mark |
|---|---|
| kernel outputs | from the pinned layout (0/1/2/3 → never/public/toA/toB; `kernel.h:25`) |
| field-program outputs | from the program's V3 output marks (5.5) |
| inputs | `never`, or `revealable` when the script declares the input a cut-and-choose candidate |
| `plumb` and `linear` results | `revealable` iff every operand is `revealable`, otherwise `never` |
| inputs created with `once` | additionally refuse a second use as an input to `run` / `program` (replaces `mask.used`, `tls_kernels.h:85`) |

`openBool` / `openField` are refused unless the mark is `public` or `revealable`. `openBoolTo`
needs `toA` / `toB`.

**This rule is defence in depth against a bug in the honest party's own Lean code.** A malicious
node controls its own worker anyway; what protects the honest party is that its honest scripts
open only what Lean proves (T3). For cut-and-choose the rule is necessarily coarse: a
`revealable` reference could be opened. The precise property is Lean's P-CUT(b).

### 5.5 Field programs, format V3, and the evaluator in Rust

**Today.** `field_program.h` hides its division openings inside the evaluator (`D` nodes:
mask·mul, open b·r, abort on zero, `divide_public`), with masks from `RAND_bytes`.

**V3:**
- Program masks become ordinary inputs. Each `D a b m` and `Z a b m` names its mask input `m`.
- `Z` is new: zero-tolerant division. It gives 0 and a public flag output when b·m opens to 0.
  This is the X25519 and hinted quotient behaviour (`x25519_fast.h:49-50`, `hinted_points.h:172`).
- Every output carries a mark (`O idx mark`).
- The evaluator (`program.rs`, about 200 lines) opens exactly one value per `D`/`Z` node, b·m,
  and nothing else.
- Lean proves, per program, by `decide` on the DAG: every `D`/`Z` mask is an input used by no
  other node, and every public output is a declared check value (P-INV, P-FIELDPROG).
- The quotients of `x25519_fast.h` and `hinted_points.h` become `Z` nodes in their programs, so
  `mask_pair` plus the C++ quotient go away.
- **This changes `EmitWordMask` and so re-exports every field program:** one heavy job, in S9,
  alone.
- The scripts draw the mask inputs from `Channels.random` (rule 5).

### 5.6 What the trusted shell can emit, and how a reviewer checks it

**On the peer control link (`link.rs`, a TCP connection of its own at PORT+20, inside
WireGuard):**

```rust
enum PeerFrame { Hello{session:[u8;32], version:u16},   // once, at start
                 Agreement([u8;32]),                     // per batch
                 Exchange(Vec<u8>),                      // exactly an `exchange` payload from Lean
                 ServerRecord(Vec<u8>), ServerClosed }   // leader → follower
```

**On the server socket (`server.rs`):**
- the SOCKS5 handshake built from an agreed `connect`;
- the bytes of agreed `server send` instructions.

**On the engines' own sockets:** nothing. The engines open and use them. The C ABI (section 5.7)
has no function that takes bytes to send.

**How a reviewer checks it:**
1. A lint: only `link.rs` holds the control socket, and only `server.rs` holds server sockets.
2. Read the two enums.
3. Read `engine_abi.h` and confirm no raw send exists.

**What the controller receives:** batch replies only (opened values, exchange replies, server
records, statuses).

### 5.7 The C ABI (`handshake_backend/EmpHybridWork/engine_abi.{h,cpp}`)

About 40 functions:
- **session:** create and destroy (party, ports, peer address, security mode, stocks);
- **Boolean:** `input_private`, `input_both`, `public`, `run(circuit, input)`, `open`, `open_to`,
  `concat`, `pick`, `slice`, `interleave`, `free`;
- **field:** `input_coins`, `input_elements`, `constant`, `public`, `add`, `sub`, `scale`,
  `divide_public`, `mul`, `check`, `checked_open`;
- **loading:** circuits from pinned flat text;
- **counters**, for the profile.

The ABI is compiled once per mode (malicious, semi-honest), as `tls-worker` and `tls-worker-sh`
are today. **Default:** the production field engine object is built **without**
`-DEMP_HYBRID_TEST_FAULTS` (SECURITY_MAP A.7). The fault fixtures get a separate test build.

---

## 6. Every piece of C++ and where it ends

### 6.1 By file

| C++ (file: functions) | What it does | Goes to | Carries |
|---|---|---|---|
| `tls_worker_v3.cpp` `run`, `read_exact`, `write_all`, the pipe loop (407-516) | framing, sequence numbers, failure latch, profile output | Rust `pipe.rs` (S8) | tests; framing stays as TlsWorkerPipe.lean:37-38 |
| `agree`, `await_peer` (130-146) | hash of every request; bounded wait | Rust `agree.rs` on the control link (S8); per batch skeleton (S9) | review; T-AGREE statement in docs |
| `joint_random` (148-154) | commit, then open, then XOR | **Lean** `Flows/Random.lean` (S9) | P-RAND |
| `socks_request`, `socks_connect` (31-75); ops 9, 10, 11, 17 | the server socket, SOCKS5, record forwarding | Rust `server.rs`, `socks.rs` (S8) | tests: `--circuits 1,3`, `--recovery drop` |
| `Connection`, `select`, `exchange`, `drop_connections`, ops 90, 91 | connection table | Rust `connections.rs` holds sockets (S8); the per-connection TLS secrets (Parked) move to Lean `Session/Pool` (S12) | |
| `dispatch` (159-405) | operation → C++ sequencing | `legacy_dispatch` behind the ABI (S8), emptied flow by flow (S9–S16), deleted (S16) | |
| environment parsing (420-490) | settings → session string | Rust `config.rs` (S8); the session string stays part of every agreement | |
| `kernel.h` `Kernel` (24-81) | layout parse, binding by name, the open check | Rust `loader.rs` + `handles.rs` (S8 for loading; S9 for the rule) | T2 (P3) |
| `kernel.h` `KernelCache` strict mode (93-174) | manifest, pins, manifest agreement | Rust `loader.rs` (S8) | |
| `kernel.h` non-strict mode (124-149, 175-185) | on-demand production through Python | **removed from the production binary** (S8); a `--dev` build flag keeps it for development | |
| `tls_kernels.h` `record_capacity` (33) | size class | Lean (`RecordClass.capacity` exists) | `rfl` |
| `take_mask`, `prepare` (38-43); `bits_to_field` (58-72); `word_to_field` (82-90) | conversions | **Lean** `Flows/Masks`, `Flows/Convert` (S10) | P-CUT, P-PAIR, P-B2F, P-W2F |
| `swap_bit`, `public_scalar`, `shared_scalar` (44-80) | ladder bits | **Lean** `Flows/Convert` (S10) | `X25519SwapBits.swapBit_shares` (exists); P-BITS |
| `begin`, `derive`, `open_handshake`, `verify_finished`, `finish`, `retire`, `abort` (102-140) | TLS handshake on the engines | **Lean** `Flows/Tls` (S12), as a `TlsClient.Backend` instance | T3, T4-TLS |
| `open_application` (163-195) | record opening, typed open | **Lean** `Flows/Tls` (S12), as a `TlsApplication.Backend` instance | T3; composed with `tlsOpenTyped_gated`, `typed_pair_refines` |
| `seal_application`, `tagged`, `seal_control` (197-245) | record sealing | **Lean** `Flows/Tls` (S12) | `sealCtr_with_tag_is_seal` now about the running halves |
| `reveal_byte`, `reveal_range`, `take_range`, `public_buffer` (248-288) | server-byte reveal | **Lean** `Flows/Tls` + `Reveal.serverBytes` (S12) | T1 as precondition |
| `rotate`, `fresh`, `exchange` / `Parked` (141-151, 289-298) | key update, fresh randomness, per-connection state | **Lean** (S12) | |
| `test_produce`, `test_echo` (299-309) | TEST | **deleted** (S8) | |
| `gcm_shares.h` (all) | GHASH key-power shares, local halves | **Lean** `Flows/Ghash` + `Local/Ghash` (S12) | P-GHASH |
| `dyn_word_mask.h` `generate_masks` (47-120; semi-honest 20-43) | cut-and-choose masks and bit pairs | **Lean** `Flows/Masks` (S10) | P-CHAL, P-CUT, P-PAIR |
| `dyn_word_mask.h` `field_to_word` (123-131) | conversion | **Lean** `Flows/Convert` (S10) | P-F2W |
| `field_program.h` loader (36-82) | pin, parse | Rust `loader.rs` (S9, format V3) | |
| `field_program.h` `evaluate_all` (112-152) | level-by-level batching; division openings | Rust `program.rs`, V3 semantics (S9) | P-FIELDPROG, P-INV |
| `field_program.h` `evaluate_clear` (87-105) | public evaluation | **Lean**: run the Lean program definition on public values (S11) | `rfl` to the program's semantics |
| `field_program.h` `masks` (25-35) | random masks | program inputs from `Channels.random` (S9) | |
| `x25519_fast.h` (all) | ladder program + masked inversion | the program (V3 `Z` node) + Lean `Flows/Curve.agree` (S11) | P-INV; `X25519Fast.compiled_correct` |
| `split_ecdh.h` (all) | split key agreement; local libsodium | **Lean** `Flows/Curve.split` + `Local/Edwards` (S11) | P-SPLIT |
| `edwards_points.h` (all) | offset agreement: prepare, step, K₀ commit-open | **Lean** `Flows/Curve.offset` (S11) | P-OFFSET |
| `hinted_points.h` (all) | lifts, hints, tables, agreements, signatures, torsion, shared bits; `LocalField`, `Ed` | **Lean** `Flows/Curve.hinted` + `Local/Edwards` (S11) | P-HINT |
| `service_kernels.h` account and contacts (204-257, 413-459, 950-966) | tables, key, seal, open, assign, evict | **Lean** `Flows/Contacts`, `Flows/Account` (S9, S10 for 55) | T4-CONTACT |
| `service_kernels.h` upgrades (403-412, 466-488) | WebSocket accept (SHA-1, base64), upgrade kernels | **Lean** `Flows/Upgrade` + `Local/WebSocketAccept` (S9 for 45, S16 for 32) | T4-UPGRADE |
| `service_kernels.h` send (489-580, 654-665, 894-949) | `seal_open`, `request`, `seal_devices`, `request_devices`, `ephemeral` | **Lean** `Flows/Send` (S13) | T3, T4-SEND, ORD-1 |
| `service_kernels.h` `prepare`, `prepare_hinted`, `prepare_batch` (58-101, 163-177) | per-contact curve preparation | **Lean** `Flows/Curve.prepare` (S11) | |
| `service_kernels.h` receive (258-402) | envelope take, open (steps 1–12), session (13–17) | **Lean** `Flows/Receive` (S14) | T3, T4-RECV, T13 (P6) |
| `service_kernels.h` refresh (625-893) | bundle fetch, take, shape, establish (9 steps), scratch | **Lean** `Flows/Refresh` (S15) | T3, T4-REFRESH, ORD-2 |
| `service_kernels.h` ceremony (677-707) | secrets, register | **Lean** `Flows/Ceremony` (S16) | T4-CEREMONY (`ceremonySecrets_spec`, `masked_hides`) |
| `service_kernels.h` fixture / private profile (186-200, 460-465, 489-510, 581-624) | TEST fixture, ops 18–21, 31, 34, 35 | **deleted** (S8: not forwarded; S16: code removed) | |
| `peer_link.h` | addresses | Rust `config.rs` (S8) | |
| `profile.h` | measurement | Rust `profile.rs` (S8); engine counters through the ABI | |
| `dyn_session.h`, `field_engine.*`, `sh_session.h` | engines | **stay** behind the C ABI | trusted |
| `dabit_generator.h` `Challenge` | transfers, permutations | `transfer` → Rust `link.rs`; `permutation` → **Lean** `Flows/Random.challenge` (S10) | P-CHAL |
| `dabit_generator.h` static generator, `word_mask.h` `WordMaskGeneratorV1`, `WordConverter` | static-width generators (fixtures only) | **stay** for the fixtures; not linked into the worker | |
| `public_auth.cpp` | X.509 | stays. **Default:** C++/OpenSSL; Rust webpki later is optional | |

### 6.2 By worker operation (the ones the controller uses)

| Ops | Flow function (S6 API) | Moves to Lean in |
|---|---|---|
| 1–8 | `Tls.begin/derive/openHandshake/authenticate/verifyFinished/finish/retire/abort` | S12 |
| 9, 10, 11, 17, 90, 91 | `Server.connect/send/receive/poll/select/reset` (Instr `server`) | Rust in S8; the per-connection TLS state in S12 |
| 12, 13, 14, 15, 16 | `Tls.open/seal/sealControl/rotate` | S12 |
| 30, 43 | `Tls.publicBuffer`, `Tls.revealRange` | S12 |
| 33 | `Random.joint` | S9 |
| 36, 37, 38, 40, 52, 63 | `Contacts.key/open/seal/evict/assign/openDevices` | S9 |
| 39 | `Channels.exchange` | Rust in S8 |
| 41, 42, 61, 62 | `Send.seal/request/sealDevices/requestDevices` | S13 |
| 44, 46 (TEST) | `Account.admitTest`, `Contacts.admitTest` | S16 (behind `Config.test`) |
| 45 | `Upgrade.public` | S9 |
| 32, 47 | `Upgrade.authenticated`, `Account.credentials` | S16 |
| 48, 49, 50, 51 | `Receive.take/drop/open/session` | S14 |
| 53, 54, 55 | `Account.key/seal/open` | S9 (53, 54), S10 (55: needs `bits_to_field`) |
| 56–60, 64, 65 | `Refresh.fetch/take/drop/shape/establish/scratchSeal/scratchCommit` | S15 |
| 66 | `Curve.prepareContacts` | S11 |
| 80, 81 | `Ceremony.secrets/register` | S16 |
| 19, 21 (fixture branch 1617-1627) | removed with the fixture session (S7) | |

---

## 7. The conversion and helper protocols: definitions, properties, proofs

### 7.0 How "hiding" is stated without probability

There is no Mathlib, so no distributions. Hiding is stated as **simulation by re-randomisation**:
- For an honest party H with secret s and randomness ρ, and every adversary strategy:
  - for any other secret s′ there is a bijection σ on H's randomness;
  - the transcript (every value released to the adversary) of (s, ρ) equals that of (s′, σ ρ).
- Equivalently: the transcript is independent of s when ρ is uniform.

This is what `GhashShares.share_hides` and `Ceremony.masked_hides` already do for one value. The
plan makes it the form of every hiding theorem.

**Statistical bounds** (the cut-and-choose counting) are **not** in Lean. They stay a written
argument with `check_parameters_128.py`; P7 is optional.
*Update 2026-11-12: now in the Mathlib package `proofs/` (see P7 in 10.2): for the model of
P-CUT steps 2–3, `CutAndChoose.cut_and_bucket_probability` (exact `bound(t)`),
`CutAndChooseAll.bound_le_bound_one` (`t = 1` is the worst case, any `B ≥ 2`) and
`CutAndChooseAll.{deployed,profile_256,profile_512,profile_1024}_undetected_lt` (every bad set
undetected with probability `< 2⁻¹²⁸`). Distributional forms of several hiding statements are
there too (`proofs/README.md`, items 4 and 7); the bijection form stays the main package's form.*

**Commitments are ideal.** The model's commitment is an opaque token, and the adversary's
committed value is a function of what it saw *before* the commitment exchange. A theorem that
relies on this says so in a hypothesis named `idealCommit`.

### 7.1 The properties

Each property below gives its Lean definition, the property to prove, and the proof approach.
"Detection" lemmas are about the joint run of 5.3 with one deviating party D and one honest
party H.

**P-RAND: joint randomness.** `Flows/Random.joint : Script (Opened .jointRandom (Vector Byte 32))`.

Definition:
- draw r (`Channels.random`);
- `exchange (commitment r)`, then `exchange r`, in one batch: the sequential order of a batch
  guarantees the peer's commitment arrives before our opening leaves;
- check `H(r') = c'` and `c' ≠ c`;
- return r ⊕ r′.

**Default:** the commitment is SHA-256("joint-random" ‖ party ‖ nonce ‖ r). This adds what
`split_ecdh.h` already does; NEEDS_REVIEW 3b asked for it. Both parties change together, so
nothing else is affected.

Properties:
- (a) honest run: both return r_A ⊕ r_B;
- (b) `idealCommit` ⇒ for every adversary value v, r ↦ r ⊕ v is a bijection;
- (c) a commitment equal to ours aborts.

Proof approach: direct (XOR involution); about 150 lines.

---

**P-CHAL: cut-and-choose challenge.** `Flows/Random.challenge (domain) (n) : Script (Perm n)`.

Definition: as today's `Challenge::permutation` (`dabit_generator.h:36-56`): commit-then-open
of 32 random bytes plus a domain hash and a phase; the seed is the concatenation in party order;
a Fisher–Yates permutation from SHA-256 counter blocks.

Properties:
- (a) both parties compute the same permutation;
- (b) the result is a permutation of `Fin n`;
- (c) `idealCommit` ⇒ for every adversary half, the map from the honest half to the seed is
  injective. Mirroring is harmless, because the seed is a concatenation.

Proof approach: (a), (b) structural; for Fisher–Yates, a list-permutation lemma (about 300
lines).

---

**P-CUT: word masks by cut-and-choose.** `Flows/Masks.generate (N) (bitBlocks) : Script (MaskPool N)`.

Definition, as `dyn_word_mask.h:47-120`:
1. M = 2·B·N candidates per party: canonical random values. Each is input to both engines
   (`boolInputBoth` and `fieldInputBoth`, marked `revealable`).
2. Challenge permutation; open the first K = B·N (both engines, both parties).
3. Second permutation into N buckets of B. For each bucket member k > 0, open per owner the
   Boolean `modadd(ref, k)` and the field sum `v_ref + v_k`.
4. Finalise the kept references: Boolean `finalize_mask` (or `finalize_bits`), field sum of
   both owners. Open the flag bit per mask.
5. For bit blocks: each party inputs its reference bits as field coins. Open the recomposition
   and bit checks (must be zero). XOR in the field.
6. Return the pool. Masks are `once` handles.

For candidate j of party P, write bP_j for the bits input to the Boolean engine, vP_j for the
field value, and the **error** eP_j = (val(bP_j) − vP_j) mod p.

Properties:
- **(a) Honest correctness.** If both are honest, every output mask (w, f) has val(w) = f < p
  and w = (r_A + r_B) mod p; every bit pair has Boolean bit = field bit.
- **(b) Disclosure.** The values released are exactly:
  - the cut candidates' values in both engines;
  - per bucket member, the two sums;
  - one flag bit per kept reference;
  - the bit-block checks.

  Kept references and remaining candidates are never opened (a T3-style trace lemma).
- **(c) Hiding.** For honest H and every adversary, the transcript is unchanged when H's kept
  references are replaced by any other canonical values. The bijection σ shifts each bucket
  member k of H by the opposite amount, mod p. This is the core lemma: the sums
  `ref + k` are unchanged.
- **(d) Detection, cut.** The run aborts iff some cut candidate (of either party) has e ≠ 0 or
  is not canonical.
- **(e) Detection, bucket.** The check for (ref, k) passes iff e_ref + e_k ≡ 0 (mod p).
  Corollary: a kept reference with e ≠ 0 survives only if every member of its bucket has error
  −e.
- **(f) Detection, flags.** Abort iff a kept Boolean reference is ≥ p, or, for bit blocks, < 32.
- **(g) Bit blocks.** For field inputs c_i with every bit check zero (c_i ∈ {0,1}) and
  Σ c_i·2^i ≡ val(b) (mod p) with 19 ≤ val(b) < p, then c = b. This is uniqueness of the binary
  representation below 2^255; the code requires ≥ 32.
- **(h) Single use.** In any trace of any flow, no mask handle appears as an input of two
  `run`/`program` instructions. Proved generically for `MaskPool.take`, which returns a handle
  and the pool without it.

Proof approach:
- (a) from `WordMask.modAdd_val`, `intoField_val`, `atLeast32_eval`, `belowP_eval`;
- (c) a re-randomisation bijection on lists (about 600 lines);
- (d)–(g) arithmetic mod p on `Nat`, using `WordMask` lemmas;
- (h) linearity by construction.

Size about 2,500 lines. **Strong.**

---

**P-PAIR / P-B2F: Boolean bits to field bits.** `Flows/Convert.bitsToField (bits) : Script (List (Handle .field))`.

Definition: take n bit pairs (ρ_bool, ρ_field) from the pool; run `xor-bit` on (x, ρ_bool); open
o = x ⊕ ρ; return ρ_field if o = 0, else 1 − ρ_field.

Properties:
- (a) for a consistent pair, the result's value is x;
- (b) for fixed x, ρ ↦ o is a bijection;
- (c) every pair is used once.

Proof approach: case analysis (about 200 lines).

---

**P-W2F: Boolean word to field.** `Flows/Convert.wordToField (u) : Script (Handle .field)`.

Definition: take a mask (w, f); run `into-field` on (u, w); open c; return `f.public c − f`.

**Default:** keep the re-comparison of c with the peer's (`tls_kernels.h:88`) as an `exchange`.
It is redundant with an authenticated opening, but it is the current behaviour; drop it later as
a measured optimisation.

Properties:
- (a) consistent mask ⇒ result = u mod p (`WordMask.into_field_roundtrip` exists);
- (b) for fixed u, r ↦ c is a bijection on [0, p);
- (c) the mask is used once.

---

**P-F2W: field to Boolean word.** `Flows/Convert.fieldToWord (v) : Script (Handle .bool)`.

Definition: take a mask; open c = v − f; check canonical; `exchange`-compare; run `modadd(w, c)`.

Properties:
- (a) result = v (`from_field_roundtrip` exists);
- (b) r ↦ c is a bijection;
- (c) the mask is used once.

---

**P-BITS: shared scalars as field bits.** `Flows/Convert.sharedBits (share : Secret Scalar) (range) : Script (List (Handle .field))`.

Covers `shared_scalar` (swap bits, 252) and `shared_bits` (bits 3..253, 251).

Definition: each party inputs its local bits (`fieldInputBits`); open the bit checks of all
2n inputs (`field_bit_checks`); return the field XOR.

Properties:
- (a) the checks open to 0 iff every input of both parties is 0 or 1
  (`FieldBits.bitCheck_bit`, plus the converse lemma, new);
- (b) result = the bits (or swap bits) of s_A ⊕ s_B (`X25519SwapBits.swapBit_shares`,
  `FieldBits.bitXor_bits`);
- (c) for honest inputs the checks are constant 0, so they carry no information.

---

**P-INV: masked inversion** (the `D`/`Z` nodes and the quotients).

Definition: V3 node semantics (5.5): open o = b·m; for `D`, abort if o = 0; for `Z`, output 0
and a public flag; otherwise a·m·o⁻¹.

Properties:
- (a) o ≠ 0 ⇒ the result is a·b⁻¹;
- (b) o = 0 ↔ b = 0 ∨ m = 0;
- (c) for b ≠ 0, m ↦ b·m is a bijection on F;
- (d) per program, by `decide` on the V3 DAG: every mask input feeds exactly one D/Z node and no
  other node.

Proof approach: field lemmas on `F`, plus a checker over the program's node list (about 400
lines).

---

**P-FIELDPROG: what a program releases.**

For every V3 program the worker loads, the public-marked outputs are exactly its declared
checks and flags. The `FieldDag.compile*_correct` theorems (exist) give their values. Stated per
program family in `Flows/Curve*Proofs.lean`.

---

**P-GHASH: GCM tags from key-power shares.** `Flows/Ghash` (engine part) and `Local/Ghash` (halves).

Definition, as `gcm_shares.h`:
- `gcm-key-share` and `gcm-multiply` reshare to B via `openBoolTo`; A keeps its fresh mask;
- even powers by local squaring;
- halves = Σ blocks·powers;
- `gcm-tag` / `gcm-check` take both halves as private inputs.

Properties:
- (a) the shares XOR to H^i for all i ≤ n. From `powers_additive`, `square_additive`,
  `gcmKeyShare_reshare`, `gcmMultiply_reshare`; it becomes a statement about this code.
- (b) halfA ⊕ halfB = GHASH_H(aad, c) (`halves_are_ghash`);
- (c) **`sealCtr_with_tag_is_seal` discharged for the running code** (closes C.3's model gap);
- (d) B's view of H^i is masked by A's fresh mask (`share_hides`);
- (e) a deviating half changes the tag by a fixed nonzero XOR, so the seal is rejected by the
  server and the open check fails (`genuine_rejected`).

Size about 800 lines. Medium–strong.

---

**P-SPLIT: split ECDH for TLS.** `Flows/Curve.split`.

Definition:
- k_A (own scalar, `Secret`);
- `Reveal.ownPublicPoint (k_A·B)`, commit-then-open with party and nonce;
- the key share u(P_A + P_B), computed by `Local/Edwards`;
- agreement: `Local/Edwards` computes T_A = k_A·S. Its coordinates are input with
  `fieldInputBoth`; the on-curve program's checks are opened; `edwards-add-u`; a `Z` quotient.

Properties:
- (a) under hypothesis H-GROUP (the Edwards formulas are the group law; stated, not proved), the
  honest result is u((k_A + k_B)·S);
- (b) the checks open to 0 iff both inputs are curve points (`EdwardsShare.onCurve_eval` plus
  the converse);
- (c) released values: P_A, the checks, the quotient denominator; only P_A depends on k_A;
- (d) `Local/Edwards.add`, `scalarMul`, `toMontgomery` agree with the formulas the field
  programs use (`EdwardsAffine`); checked against libsodium test vectors in tests.

---

**P-OFFSET: the sealed-sender offset agreement.** `Flows/Curve.offset`.

Definition, as `edwards_points.h` and `hinted_points.h:179-234`:
- prepare: the table program with scalar bits as inputs; the checks opened; K₀ halves
  commit-then-open;
- step: offset τ from P-RAND; K₀ + τ·B in `Local/Edwards`; the digit recoding; the sum program.

Properties:
- (a) `OffsetAgreement.public_key_correct` and `agreement_correct` become statements about
  `step` (via the recoding lemma: signed base-16 digits recompose τ; new, about 200 lines);
- (b) `public_key_independent` (exists), now about the script's output;
  *2026-11-12: its probability form for the algebra (not yet for the script's output) is
  `proofs/` `OffsetAgreement.offset_public_key_independent` (offset uniform in `ZMod ℓ`, any
  finite commutative group of order `ℓ`, H-GROUP as that hypothesis) and
  `offset_public_key_uniform` (`ℓ` prime, `B ≠ 0`: the key is uniform). Open: the deployed
  offset is drawn from `[0, 2²⁵²)`, not uniformly mod `ℓ`; and the statement about `step`.*
  *2026-11-12 (later): the deployed sampling is covered in `proofs/TlsMpcProofs/OffsetSampling.lean`.
  As deployed (`service_kernels.h` `seal_open`/`ephemeral`; `edwards_points.h` `step`/`step_inputs`):
  each party draws 32 bytes, commits with SHA-256, the values are exchanged and XORed, and
  `offset[31] &= 15` keeps the low 252 bits, so τ = `(mine XOR peer) mod 2²⁵²`.
  `deployedOffset_uniform`: τ is exactly uniform on `[0, 2²⁵²)` for the honest party's uniform
  `mine` and any peer value independent of it (`idealCommit`). `deployed_key_close`: for any two
  initial scalars the published key's distributions differ on every event by at most
  `(ℓ − 2²⁵²)/2²⁵²`, and `ed25519_key_close` bounds that by `2⁻¹²⁷` for ℓ = the Ed25519 order
  (`order_gap_lt`; `ℓ − 2²⁵² = 27742317777372353535851937790883648493 ≈ 2^124.4`; the bound is
  `/2²⁵²`, not `/ℓ`, because two shifted ranges differ in up to `ℓ − 2²⁵²` points of mass
  `2⁻²⁵²` each). `deployed_key_close_ideal` / `_uniform` / `ed25519_key_close_uniform`: within
  `(ℓ − 2²⁵²)/ℓ < 2⁻¹²⁷` (total variation) of the ideal key and of uniform on `G`. `prime_order`:
  ℓ is prime (Pocklington chain, no hypothesis). Several messages: `offset_public_keys_independent`
  / `_uniform` (offsets uniform mod ℓ: the joint keys do not depend on the initial scalar; uniform
  on `G^k`) and `deployed_keys_close` / `ed25519_keys_close` (deployed offsets: joint keys within
  `k·2⁻¹²⁷`). Still hypotheses: H-GROUP, `idealCommit`, a fixed (non-adaptive) peer value per
  message; not modelled: the aborts on `mine = peer` and on τ = 0 (both independent of the
  initial scalar). Still open: the statement about `step` (the recoding lemma).*
- (c) the checks open 0 iff the bits are bits and the hints are right (`entries_sound`,
  `prepareTable_sound` exist);
- (d) K₀'s commitment binds party and nonce, as P-RAND.

---

**P-HINT: the constant-depth lift and tables.** `Flows/Curve.hinted`.

Definition, as `hinted_points.h:116-158, 237-334`:
- the lift: open checks, then w, then Z;
- hints computed by `Local/Edwards` on own mask points;
- tables, bit sums, signature sums, torsion.

Properties:
- (a) the order of openings in the trace: the checks before w (a trace lemma);
- (b) under hypothesis H-QR (2 is a non-square mod p; Euler's criterion for this p) and
  q ≠ 0: (r, b) ↦ q·r²·2^b maps the nonzero pairs onto F∖{0}, exactly 4 pairs to each value.
  The proof of H-QR is **not** in scope; it is stated as a hypothesis.
  *2026-11-12: H-QR is discharged in `proofs/` (`QuadraticResidue.two_not_square`,
  `euler_criterion`, `euler_nonsquare`, from `Prime25519.prime_modulus`). For the program
  `EdwardsHinted.liftOpen` (not yet for the script `Flows/Curve.hinted`): `lift_select` and
  `liftOpen_square_iff` (validity is `sel xor b`), `lift_fiber_card` and `lift_opened_uniform` /
  `lift_opened_uniform_xor` (the opened w is exactly uniform on F for q ≠ 0). Correction to the
  count above: for the pair (r, b) every value of F (0 included) has exactly **2** preimages; the
  "4" counts (r, b_A, b_B). (a), (d), (e) and the script-level (b) remain with S11.*
- (c) Z = P + M_A + M_B: for fixed P, M_A ↦ Z is a bijection on the group, under H-GROUP;
- (d) `entries_sound` composed: whatever the hints, if the links open to 0 the table equals the
  chain from P;
- (e) the validity bit `valid` is opened only in `prepareContacts` (NEEDS_REVIEW 3b's table),
  as a disclosure lemma.

---

**Commit-then-open sites, unified.**
- `Flows/Random.joint`, `Flows/Random.challenge` and the two point exchanges (P-SPLIT, P-OFFSET)
  use **one** `Local/Commit.commit (label) (party) (nonce) (value)`.
- One theorem `commit_open_sound` (the opening is checked against the commitment; a copied
  commitment aborts) serves all four.
- This replaces the three framings of SECURITY_MAP D.13.

---

## 8. Theorems per channel, and `TlsMpc/Security.lean`

"Exists" means already in the repository (SECURITY_MAP C).

### 8.1 Catalogue

| Id | Statement | Exists? | Stage | Kind |
|---|---|---|---|---|
| **T1** | **Server-byte reveal policy.** `Policy/ReceiveSpec.lean` defines a total reference classifier `hidden : List Byte → Set Nat`: the positions that are body bytes of a server request (field 3), of a response (field 4, unless `openBody`), envelope field payloads, or payload bytes after the second of a message of unknown kind. For every byte stream and every run of `record`'s loop over `budget`, `mayReveal`, `step`, `stepPassed` and `stepSkipped` that does not throw, the revealed positions are disjoint from `hidden`. With `openBody = true`: the same, minus field 4. | no | P1 | strong |
| **T2** | **Open marks and printers.** For every kernel name the inventory can emit, the printed layout's rows and open flags equal the Lean kernel's declared fields and marks; parsing the printed `.flat` gives back `Flat`; field programs: the V3 printer likewise. | no | P3 | medium |
| **T3** | **Disclosure per flow.** The released values in any trace of the flow are exactly the listed `Reveal` kinds, on the listed handles. | by construction plus a per-flow lemma | S9–S16 | mechanical |
| **T4-x** | **Composition per flow** (x ∈ CONTACT, UPGRADE, TLS, SEND, RECV, REFRESH, CEREMONY). Under the ideal model with both parties honest, the flow's result equals its specification, e.g. `Contacts.seal` = `ContactKernel.seal` of the state under the key from both shares (`contactKey_spec`, `contactSeal_spec`). | parts | S9–S16 | medium; strong for TLS and SEND |
| **T5** | P-RAND, P-CHAL, P-CUT, P-PAIR, P-B2F, P-W2F, P-F2W, P-BITS, P-INV, P-FIELDPROG, P-GHASH, P-SPLIT, P-OFFSET, P-HINT (section 7) | model pieces | S9–S12 | strong |
| **T6 / ORD-1** | **Send ordering.** Over the events Seal(c), StoreAck(c) and Send(c) of a Session trace, every Send(c) is preceded by a StoreAck(c) after the last Seal(c) before it; and no two Send events carry the same sealed envelope (a resend always reseals). Holds for `deliverJob`, `serve` and `loop`. | no | P4 (stated after S7, restated after S13) | medium |
| **ORD-2** | A refresh's scratch becomes the contact's state (`scratchCommit`) only after both parties saw the nodes acknowledge it; otherwise it is dropped. | no | P4, S15 | medium |
| **T7** | **What the server receives.** (a) `signal-request-ctr`, `bundle-request-ctr` and `bundle-fetch-ctr`: the sealed plaintext equals the frame with slot i replaced by the WebSocket-masked bytes of the record's field i, and nothing else changes; (b) `signal-seal-official` / `-built` compute `SealedSenderV1` encryption of the Signal message produced by `ChainSend` / `SpqrSend` from the stored state. | no | P5 | strong |
| **T8** | **Request templates.** `Policy/Request.build`, `buildDevices`, `buildFetch` and `assemble`: unmasking gives a WebSocket binary frame whose payload is the protobuf message with the stated fields; every slot offset points at a zero run of its width, inside the payload, without overlap; the bytes outside the slots are a function of (envelope, timestamp, id, profile) only. Also `reply`, `keepalive`, `ping`, `clientFrame`. | no | P2 | medium |
| **T9** | **Peer messages are public.** No `PeerMsg` field has a `Secret` or `Handle` type (by type); `PeerMsg.flow` is constructible only in `Reveal.lean`. | by types | S5 | mechanical |
| **T10** | **Database writes.** Every `DbCall.writeBlob` blob = nonce ‖ `Opened.sealedBlob`, with the nonce an `Opened.jointRandom` not used before in the session (state nonces never repeat; NEEDS_REVIEW 3b asked); versions per contact increase by one per acknowledged write. | `contactSeal_spec` | S9 | medium |
| **T11** | **Application results.** Every `DaemonLine.jobResult` carries exactly the entries whose digest both controllers exchanged and found equal; each entry's result is `Recovery.onSend` / `onFetch` of revealed statuses or a fixed reason. | no | P4 | medium |
| **T12** | **Skeleton determinism (noninterference of scripts).** For any script, two runs whose public arguments and data replies agree produce identical skeletons (and hence identical agreement hashes and identical `exchange` payloads). By induction on `Script`; generic. | no | S9 | mechanical |
| **T13** | **Receive gating, accept direction.** If `receive-session`'s opened status is 255 then the message MAC verified and the sender certificate's signature verified under the trusted server key; `receive-text` outputs are zero unless the session's status is 255 (the missing `_rejects` lemmas). | no | P6 | strong |
| **T14** | **Stock used once** (11a; section 9). | no | X1 | strong |
| **T15** | **Rotation reveals nothing about ids** (section 8; section 9). | no | X2 | medium |

**What each channel's guarantee consists of:**

| Channel | Theorems |
|---|---|
| Signal server | T9-style types (`ServerOut` holds only `Opened`), T1, T3/T4-TLS, T7, T8, ORD-1, T15 |
| Other node | T9, T12, T5 (every own-secret reveal), the agreement rule (5.1, reviewed in Rust) |
| Database nodes | T10; parity is a trusted `handoff_client` output |
| Application | T11; daemon channels by types (Rust) |
| Disk, logs | by types (`RecordEvent`, `LogLine` have no `Secret` field); share files only via `saveShare` |

### 8.2 `TlsMpc/Security.lean`

One file that imports the theorem files and restates each important theorem under a short
name. Each restatement is `theorem X : <statement> := Original.name`, so renaming or weakening
the original breaks the build.

**Sections:**
1. lowering and artifacts;
2. kernels compute their specification;
3. gating and what each opening reveals;
4. the controller: parsers, the reveal policy, templates, results;
5. state and ordering;
6. conversions and helper protocols;
7. flows and channels.

**Per entry:**
- a plain-language docstring (one or two sentences);
- its status, **K / C / M** and **[hyp: …]** (the hypotheses, e.g. `idealCommit`, `H-GROUP`);
- the SECURITY_MAP section.

`scripts/check_axioms.py` runs `lake env lean TlsMpc/Security.lean` (heavy). It parses the
`#print axioms` output and fails on anything beyond `propext`, `Classical.choice`, `Quot.sound`
and the allow-listed `Lean.ofReduceBool`. The output is committed as `SECURITY_AXIOMS.txt`.

S1 builds version 1 from C.1–C.5. Each later stage adds its theorems in the same commit.

---

## 9. Room for the two queued features

**X1: the encrypted stock of circuits made ahead (PRODUCT_TODO 11a).** It slots in as follows:
- **Lean:**
  - `Node/Stock/Journal.lean`: a pure model of a durable "consumed" journal with crash
    semantics (a synced prefix survives);
  - `Node/Stock/Use.lean`: the rule "confirm the index in the batch skeleton, skip forward, never
    back";
  - `Channels.stockJournal` (`append`, `sync`, `read`).
- **Engine:** an instruction `stockUse (shape) (index)` in the skeleton, so both nodes agree the
  index inside the existing agreement (5.1). No new channel.
- **Rust:** `stock.rs` holds the encrypted store, the per-item key chain (advanced and erased on
  use) and the in-memory boot id.
- **C ABI:** `export_preprocessing` / `import_preprocessing`. This is the engine work 11a needs
  (split of emp-ag2pc's function-independent part, as `TriplePool::mint` already does for
  triples).
- **T14:** in every trace of `Stock.Use` over the journal model, including crashes and
  restarts, no index reaches `stockUse` twice; when the two nodes' journals differ, both use
  max+1.
- **Placement:** after S16. Nothing in S0–S16 has to change for it.

**X2: connection rotation over Tor with a pool (PRODUCT_TODO 8).** It slots in as follows:
- **Lean:**
  - `Node/Session/Pool.lean`, created in S7 from today's `apps`, `states`, `slots`, `counters`,
    `parkedStates`, `openCircuits`, `openConnection`, `reconnect`;
  - `Node/Policy/Rotation.lean`: pure. It decides when to rotate (a random count around the
    mean, from `Random.joint`), which pool connection a message takes, and the order and hold
    window. It replaces `Circuits.assign`.
- **Engine and Rust:** `ServerOp.close` (S8 adds it to Rust; there is no close operation today,
  only reset after a close).
- **Configuration:** `Config.rotation {mean, poolSize, hold}`; fresh SOCKS credentials per
  connection generation (`Circuits.labels` gains a generation counter).
- **T15:** the assignment of messages to connections, the send order and the rotation points
  are functions of joint randomness, the message count and the configuration only, not of ids,
  texts or results.
- **Placement:** any time after S7 and S8.

---

## 10. Stages

### 10.1 Test sets used below

- **Q (quick):**
  - `lake build public_service_controller` (heavy: take the lock);
  - `public_service_controller recovery-check`;
  - `cargo test` in `node_daemon` (and `node_worker` from S8);
  - the S0 lints.
- **L (local):** `check_signal_service_local.py MODE --runs 2 --signup --db` for MODE in
  `malicious`, `semi-honest`.
- **F (full):** L plus, in both modes, each as its own run:
  - `--runs 0 --multi-device --db`, `--runs 0 --app`, `--runs 0 --sustained 16 --restart-after 8`;
  - `--runs 0 --recovery classify,devices,refresh-retry,identity,unauthorized,drop,throttle,bundle-fault,resume,hang`;
  - `--runs 1 --circuits 1,3 --db`, `--runs 0 --ceremony`;
  - `--runs 1 --db --profile libsignal --fingerprint`, `--runs 1 --db --hinted`;
  - `--runs 1 --db --strict-produced` (needs `state/circuits`; produce once in S0, heavy).
- **K (kernel fixtures):** `check_typed_open.py`, `check_bundle_kernels.py`,
  `check_contact_kernels.py`, `check_receive_kernels.py`, `hinted_program_checks.py`,
  `check_tls_worker_v3.py`.
- **E (engine fixtures, from S10):**
  - the new `node_worker` conversion fixture (round trips, both modes);
  - `rounds_fixture` scenarios ported to scripts;
  - the cheating-party fixtures re-pointed at the scripts. A `Config.test` flag
    `deviate=<name>` makes party B's script misbehave, as `EMP_TEST_WORD_*` do today.
- **D (differential):** `scripts/compare_records.py` compares the `SIGNAL_RECORD` files of an L
  run before and after a stage. It masks times, masks, nonces and joint randomness, and fails on
  any other difference in what was sent or revealed.

### 10.2 The stages

Sizes are engineer-time for one engineer who knows the area. Proof sizes are honest guesses and
could double.

---

**S0. Guard rails and baselines.**

Goal: tools every later stage relies on.

Scope (all new files):
- `scripts/heavy.sh` (the `flock` wrapper);
- `scripts/lint_node.py`:
  - (a) baseline mode: lists today's I/O primitive sites in the controller and fails on new
    ones outside the allowed files;
  - (b) escape hatches in `TlsMpc/Node`;
  - (c) emitter isolation: no emitter imports `TlsMpc.Node`;
  - (d) later stages switch on: `Secret.val` only in allowed files, no `Secret`/`Handle` field in
    `Messages.lean`.
- `scripts/compare_records.py`;
- golden L-run records stored under `tests/golden/` (masked);
- one manifest production for `--strict-produced` (heavy, alone).

Theorems: none.

Tests: lints on today's tree pass in baseline mode; `compare_records.py` on two runs of the same
tree passes.

Depends on nothing. **3–4 days. Mechanical.**

**Status (2026-11-12).** Done:
- the lock is `guarded.py --heavy` (rule 3; `heavy.sh` forwards to it, as macOS has no `flock(1)`);
- `scripts/lint_node.py` with `scripts/lint_node_baseline.json` (127 I/O sites in 4 files of the
  controller's 122-module import closure); checks (d) behind `--enable`;
- `scripts/compare_records.py` (`--mask` writes the golden form);
- `check_signal_service_local.py --record DIR` writes each session's `SIGNAL_RECORD` per party
  (the harness wrote none before); golden records in `tests/golden/` (malicious only so far,
  recorded before the device-refresh change: regenerate, and add semi-honest, see its README);
- the manifest for `--strict-produced` already existed in `local_signal_server/state/circuits`.

Brought forward from later stages, small and independent of the reorganisation:
- `Policy/Clock.lean` (S4): `agreedClock` now has the two-minute check, with `agreed_within`;
- the daemon link fixes 1 and 2 of S3 (sealed replies, nonce and replay cache, and refusal of a
  reflected message), and **one listener per channel**: `peer_listen` for the other daemon,
  separate from the application's `listen` (this replaces S3's default 3 of one listener);
- R14: the production field-engine objects are built without `EMP_HYBRID_TEST_FAULTS`; only the
  test object `field_engine.o` (for `field-roundtrip-fixture`) keeps the hook.

---

**S1. `Security.lean` version 1 and the axioms check.**

Goal: the one-file answer to "where are the important theorems", for what exists today.

Scope:
- new `TlsMpc/Security.lean`: about 90 restatements, every K/C entry of SECURITY_MAP C plus the
  important M entries marked M;
- `scripts/check_axioms.py`;
- `SECURITY_AXIOMS.txt`.

Theorems: none new. This stage settles whether the 5 `bv_decide` uses need `ofReduceBool`.

Tests: `check_axioms.py` (heavy: a full build).

Depends on S0. **4–6 days. Mechanical.** Concurrent with S2 and S3 (separate files; builds take
turns).

---

**S2. Pure logic to its final modules.**

Goal: the controller's pure parts leave `main`'s file once, to where they stay.

Scope:
- `PublicReceive` (55-681) → `TlsMpc/Node/Policy/Receive.lean`;
- `PublicRequest` (688-803) → `Policy/Request.lean`;
- `Circuits` (821-836) → `Policy/Circuits.lean`;
- `Recovery` (859-1049, including `checks`) → `Policy/Recovery.lean`;
- `fromHex`, `toBits`, `toBytes`, `natural`, `sessionBytes` → `Node/Bytes.lean`;
- `readExport`, `readSelf`, `readReceive`, `ReceiveKeys` (1077-1138) → `Node/Export.lean`
  (parsers);
- `parseBench` → `Node/Bench.lean`;
- `officialProfile` → `Node/Config.lean` (stub; filled in S4).

Namespaces become `TlsMpc.Node.Policy.*`. The controller file imports them. `fast_eq` moves with
its code.

Theorems: the moved ones, unchanged.

Tests: Q, L, D.

Depends on S0. **3 days. Mechanical.** Must not run concurrently with any stage editing the
controller.

**Status (2026-11-12).** Done, in four steps, each building with recovery-check 29/29,
parse-bench, the lints and `check_axioms.py`:
- `PublicRequest` → `Node/Policy/Request.lean`. Each builder is now split into the message it
  frames (`sendMessage`, `fetchMessage`, `devicesMessage`, new names) and the framing (`build`,
  `assemble`); same bytes. `KernelSpecs/RequestFrame.lean` states its theorems about these
  definitions; the restated copy (`Mirror`) and `RequestFrameBridge.lean` are deleted.
- `PublicReceive.fast` (with `fast_eq`) → `Node/Bytes.lean` (from `Node/PassOver.lean`), so that
  `Policy/Request.lean` does not import the receive side.
- `PublicReceive` (including `passOne`/`passRun`/`passRoom`/`passBulk` and their theorems, and the
  replies `reply`/`keepalive`/`ping`/`replies`) → `Node/Policy/Receive.lean`; `Circuits` →
  `Node/Policy/Circuits.lean`; `Recovery` (with `checks`, `responseFrame`, `feed`, `walk`,
  `digest`) → `Node/Policy/Recovery.lean`.
- `fromHex`, `toBits`, `toBytes`, `natural`, `sessionBytes` → `Node/Bytes.lean`; `readExport`,
  `readSelf`, `readReceive`, `ReceiveKeys` → `Node/Export.lean`; `parseBench` → `Node/Bench.lean`;
  `officialProfile` → `Node/Config.lean`. These were `private` or top level in the controller; they
  are now in namespaces `TlsMpc.Node.{Bytes,Export,Bench,Config}`, which the controller opens.
  The four I/O sites of `parseBench` and `officialProfile` moved with them (baseline updated).
- Namespaces: `PublicReceive`, `PublicRequest`, `Circuits` and `Recovery` kept their names (the
  owner asked for the same names in the controller), not `TlsMpc.Node.Policy.*` as written above.
- `Security.lean` restates `controller_fast_eq`, the pass-over theorems (`passOver_*`) and
  `passOne_bulk`, `passRun_bulk`, `passRun_add`.
- Left in the controller: `establishTail` (the argument encoder of worker operation 60, not
  listed above; it moves with that operation's flow) and `recordEvent` (I/O; S5).

---

**S3. Daemon channels.**

Goal: the daemon's external I/O typed and in one module (3.4), and the link fixes.

Scope: `node_daemon/src/**` only. Fixes:
1. **Peer replies sealed and checked.**
2. **Nonce and replay cache** (60 s).
3. `wait`, `events` and `status`: **Default** stays unauthenticated on the listener, but the
   listener binds only to `config.listen`, documented as "localhost or the WireGuard address".
   A bearer token in the config is optional.
4. **Default:** the peer link stays HMAC'd plaintext inside WireGuard. TLS is deferred to
   PRODUCT_TODO 7's link work.

Theorems: none (Rust). Unit tests for each `PeerMessage` and replay.

Tests: `cargo test`; F's `--app`, `--sustained 16 --restart-after 8` and `--recovery hang`, both
modes.

Depends on S0. **1.5 weeks. Mechanical**, with medium protocol care for the replay cache.
Concurrent with S1, S2 and S4–S7 (no shared files).

---

**S4. Types, secrets, configuration.**

Goal: `Secret`, `Opened` (constructor private, still empty of kinds), `Handle`, typed `Config`;
the secret material of 4.2 confined.

Scope:
- new `Node/Secret.lean`, `Node/Types.lean`; `Node/Config.lean` (all 36 `getEnv` sites through
  one `Config.read`; `TestHooks` behind `--test`);
- the controller's secret-holding variables retyped (4.2 rows 1–6);
- `Node/Export.lean` returns `Secret` for keys and records;
- the KEM tool takes the key on stdin. `local_signal_server/provision/src/main.rs` changes; it
  is in-repo.
- the ceremony child gets `SIGNAL_LOCAL_CREDENTIALS_FILE`;
- `Policy/Clock.lean`: `agreedClock` gets the two-minute check;
- **the settings agreement:** at session start the controllers exchange the SHA-256 of
  (`SIGNAL_ACK_REFUSED`, `SIGNAL_RECOVERY`, `SIGNAL_CLIENT_PROFILE`, `SIGNAL_PREPARE_BATCH`,
  rotation settings later) and abort on difference (SECURITY_MAP D.11).

Theorems:
- `Clock.agreed_within`: the agreed clock is within 2 minutes of the local one, or the session
  aborted;
- `Config.read` is the only reader (lint).

Tests: Q, F (both modes; the ceremony stage especially), D.

Depends on S2. **1 week. Mechanical / medium.** Not concurrent with S5–S7.

---

**S5. `Channels.lean` and `Messages.lean`.**

Goal: section 3 complete for everything except the server and the engines.

Scope:
- new `Node/Messages.lean`, `Node/Channels.lean`;
- every site of 3.3 rewritten to call `ch.*`;
- `swap` replaced by `ch.exchange` with typed `PeerMsg` (still op 39 underneath);
- `RecordEvent` and `LogLine` constructors for all sites;
- the lint switches to strict for the controller.

Theorems:
- **T9** (by type);
- `Messages.noSecret`: a `#guard`-style meta check that no constructor field type mentions
  `Secret` or `Handle`, run by the lint.

Tests: Q, F, D (the record transcript must be identical modulo masks).

Depends on S4. **2 weeks. Mechanical**, with medium design care in the message types.

---

**S6. The flow API and `Reveal.lean` (legacy implementations).**

Goal: the final call sites for every worker operation.

Scope:
- new `Node/Flows/{Tls,Server,Random,Contacts,Account,Send,Receive,Refresh,Upgrade,Ceremony,Curve}.lean`.
  These hold **signatures** (with `Opened`/`Secret`/`Handle` types) and implementations through
  today's operations (`Legacy.call`).
- new `Node/Reveal.lean` with all `RevealKind`s of 4.3, the legacy wrappers for those reached
  through operations, and the rest declared;
- every one of the 108 RPC lines of the controller replaced by a flow call;
- `TlsWorker.backend` and `applicationBackend` become `Flows/Tls.legacyBackend`.

The signatures must already be the final ones. Rule of thumb: a flow function returns `Opened`
for what is opened, `Secret` for what is own-private, `Handle` for engine values that stay; it
takes `ContactId`, `Opened` and `Secret` values, never raw `Bytes` for anything secret.

Theorems: none new. The `Reveal` docstrings cite existing theorems or "none (SECURITY_MAP D)".

Tests: Q, F, D.

Depends on S5. **2 weeks.** Mechanical, but **a careful API review first**: the senior engineer
writes the signatures, the other reviews them against sections 6.2 and 7.

---

**S7. Session split.**

Goal: `main` becomes the ~10-line `Node/Main.lean`; the loops become functions of `Channels` and
the flow API.

Scope:
- `Node/Session/{Common,Pool,Send,Serve,Receive,Ceremony,Delete}.lean`;
- `Common`: `record`, `receiveSoft`, `awaitReply`/`awaitSoft`, keepalive, `drainOne`;
- `Pool`: connections, per-connection parser state and counters; X2 builds on it;
- `Send`: `notify`, `restamp`, `sendSoft`, `refreshSoft`, `deliverJob`, `loop`;
- `Serve`: `serve`, `loadJob`;
- `Receive`: `receiveFirst`, `handleEnvelope`, `waiting`;
- `Ceremony`, `Delete`;
- **removed:** the fixture branch (1617-1627) and the TEST in-memory fixture texts (2320-2324).
  **Default:** retire `check_signal_service_v3.py` and `check_tls_application_v3.py`; keep
  `check_tls_worker_v3.py`.
- `handshake_backend/EmpHybridWork/PublicServiceController.lean` becomes
  `def main := TlsMpc.Node.Main.main`. The executable name is unchanged.

Theorems: none required here. The session functions are written so that P4 can state ORD-1 and
T11 over them: no `IO.Ref` escapes a session function's signature; state is a record threaded
explicitly or a `StateT`.

Tests: Q, F, D.

Depends on S6. **3 weeks. Mechanical** (behaviour-preserving) **but large.** A reordering of
public requests shows up as a request disagreement (fails loudly) or in D.

---

**S8. Rust worker shell, engine C ABI, legacy library.**

Goal: the C++ shell moves to Rust, once. All sequencing stays in C++ for now, behind
`legacy_dispatch`.

Scope:
- **new crate `node_worker/`:** `pipe.rs`, `agree.rs`, `link.rs` (the control link, PORT+20),
  `server.rs`, `socks.rs`, `connections.rs`, `loader.rs`, `config.rs`, `profile.rs`, `engines.rs`;
- **new C++:** `engine_abi.{h,cpp}` and `legacy_abi.cpp`, which is today's `Worker::dispatch`
  minus the shell, plus `legacy_select` and `legacy_reset` for the parked TLS state of ops 90/91.
- **Rust handles:**
  - ops 8, 9, 10, 11, 17, 39, 90, 91 (sockets; forwarding on the control link);
  - the agreement (with today's private-prefix rule for ops 36/39/47/53);
  - strict-mode loading.

  It forwards the rest to `legacy_dispatch`.
- **Not forwarded:** ops 18–29, 31, 34, 35, the TEST producer and the service fixture.
- **Adds** `ServerOp.close`, for X2.
- **The build:** `build_hybrid_v3.py` builds `engine_abi` and `legacy_abi` as a static library
  per mode; `node_worker/build.rs` links it. The production field-engine object is built
  without `EMP_HYBRID_TEST_FAULTS`; a `-test` variant keeps it.
- The controller spawns `node_worker` instead of `tls_worker_v3` (`Worker.lean`). The pipe
  protocol is unchanged.

Theorems: none (Rust). The control-link frame set (5.6) is documented in `link.rs`, with a lint
that only `link.rs` and `server.rs` own sockets.

Tests: Q, F (both modes, with `--link-delay-ms 1` once to compare latency), K
(`check_tls_worker_v3.py` against the new binary). `cargo test`: the pipe framing, SOCKS against
`socks5_test_proxy.py`.

Depends on S7 (for `Worker.lean` and the retired fixtures). It can start in parallel with S6–S7
on the Rust side, because S8's Lean change is two lines.

**5–6 weeks. Medium engineering, protocol care** (identical agreement semantics; leader/follower
record forwarding; the closed-connection signal).

---

**S9. Engine framework and the first flows in Lean.**

Goal: the instruction set, scripts, the ideal model, the Rust interpreter and the open rule;
field programs V3; the pilot flows.

Scope:
- **Lean:** `Node/Engine.lean`, `Node/Engine/Model.lean`, `Worker.lean` (batch codec, `runIO`);
- **Rust:** `interp.rs`, `handles.rs`, `program.rs`;
- **field programs V3:** `TlsMpc/FieldDag*.lean` printer and evaluation semantics, and
  `EmitWordMask` (D/Z nodes with explicit mask inputs, output marks). **One re-export of the
  field programs, heavy, alone.** The C++ `field_program.h` stays for the legacy library until
  S11, reading V2 files kept beside V3 ones.
- **Flows moved:**
  - `Random.joint` (op 33, and the jointly random parts of the legacy ops keep their C++ copy);
  - `Upgrade.public` (op 45: nonce and accept value; `Local/WebSocketAccept.lean` with SHA-1 and
    base64);
  - `Contacts.key/open/seal/evict/assign/openDevices` (36, 37, 38, 40, 52, 63);
  - `Account.key/seal` (53, 54).

  **Handle sharing between Lean flows and the legacy library:** the contact table's Boolean
  wires live in the Rust handle table; `legacy_dispatch` gets them through `legacy_get(id)` and
  `legacy_put(id, wires)`. **This is the one coupling of the migration.** It is deleted in S16.

Theorems:
- **T12** (skeleton determinism);
- **T3** for the moved flows;
- **T4-CONTACT:** `Contacts.seal` / `open` / `key` against `contactKey_spec`, `contactSeal_spec`,
  `contactOpen_accepted_iff`, under the model;
- **P-RAND** (a)–(c);
- **T10;**
- **P-INV (d)** and **P-FIELDPROG** for the re-exported programs (statements; proofs by
  `decide` per program);
- `Local/WebSocketAccept.accept_spec` against RFC 6455's definition (SHA-1 as specified in
  Lean, test vectors in tests).

Tests:
- Q, F (both modes), D;
- the latency check of 5.2 at `--link-delay-ms 1`;
- a fixture comparing the legacy op and the Lean flow on the same inputs during the stage.

Depends on S8. **5–6 weeks. Strong** (the semantics and model must be right; everything after
builds on them).

---

**S10. Conversions, masks, inversion.**

Goal: section 7's P-CHAL, P-CUT, P-PAIR, P-B2F, P-W2F, P-F2W, P-BITS and P-INV as Lean scripts
with their theorems; op 55.

Scope:
- `Flows/{Masks,Convert,Inversion}.lean`, `Flows/Random.challenge`, their `*Proofs.lean`;
- `Account.open` (op 55: `swap-bits` circuit + `bitsToField`);
- the E fixtures;
- `Config.test` deviations for the cheating tests.

The legacy library keeps its own conversions until S11–S16 delete their callers. **Masks of the
two implementations come from separate pools.**

Theorems: as listed in 7.1, all of (a)–(h) of P-CUT, plus `commit_open_sound`. P7 (the counting
bound) is not included. *(2026-11-12: P7 is now done separately in `proofs/`, for the model;
see 10.2. S10 still owes P-CUT (d), (e) — the detection rules that model assumes.)*

Tests: Q, F, E (cheating fixtures: a wrong cut candidate, a wrong bucket member, a non-bit, a
reference ≥ p, a wrong bit block; each must abort), D.

Depends on S9. **8–10 weeks.** Strong (P-CUT (c), (e), (g) are the hard ones). Split: one
engineer on scripts and fixtures, one on proofs.

---

**S11. Local arithmetic and the curve helpers.**

Goal: split ECDH, ladder agreements, the offset agreement, the hinted programs, contact
preparation in Lean; libsodium and OpenSSL bignums out.

Scope:
- `Local/{Field,Edwards}.lean`: affine and extended coordinates, add, double, scalar
  multiplication, encode/decode, the Montgomery map, sqrt, Legendre symbol;
- `Flows/Curve.lean` with `split`, `agree` (x25519-fast + `Z`), `offset.prepare/step`,
  `hinted.{lift,hints,tables,agree,signatures,torsion,sharedBits}`, `prepareContacts` (op 66);
- the `evaluate_clear` uses replaced by running the Lean program definitions;
- Rust `program.rs` replaces `field_program.h` everywhere; the V2 files are deleted.

Theorems:
- P-SPLIT, P-OFFSET (including the recoding lemma), P-HINT;
- `Local/Edwards` agrees with the `EdwardsAffine` formulas (proved);
- `Local/Edwards` agrees with libsodium on test vectors (tests).

Tests: Q, F (with and without `--hinted`), E (`rounds_fixture` scenarios as scripts:
nine agreements, a signature point, torsion, tables, an invalid key in a batch),
`hinted_program_checks.py`, D. **Measure** the per-message time of the local arithmetic (risk
R2).

Depends on S10. **5–6 weeks. Strong.**

---

**S12. GHASH shares and TLS.**

Goal: handshake, record open and seal, key update and server-byte reveal in Lean, as
`TlsClient.Backend` and `TlsApplication.Backend` instances.

Scope:
- `Flows/{Ghash,Tls}.lean`, `Local/Ghash.lean`;
- the per-connection secret state (traffic-key handles, parser handle, GHASH `Secret` shares)
  moves into `Session/Pool`, replacing the C++ `Parked`;
- the 64-record buffer window and the drop-after-seal rule (`tls_worker_v3.cpp:318-336`) move to
  `Flows/Tls` (`drop`);
- `check_tls_worker_v3.py`'s handshake fixture moves to the new backend.

Theorems:
- P-GHASH (a)–(e);
- **T3/T4-TLS:**
  - derive and open handshake: function level, composed with `TlsKdfPrepared` and
    `verifyHash_value`;
  - open: `tlsOpenTyped_gated`, `typed_pair_refines`, `class_fields`;
  - seal: `sealCtr_with_tag_is_seal` with the halves hypothesis discharged by P-GHASH (c);
- `Reveal.serverBytes` takes T1's invariant as its precondition when P1 is done; otherwise its
  docstring says "budget unproved".

Tests: Q, F, K (`check_typed_open.py`, `check_tls_worker_v3.py`), D.

Depends on S11. **4–5 weeks. Medium–strong.**

---

**S13. Send.**

Goal: `seal_open`, `request`, `seal_devices`, `request_devices` in Lean.

Scope: `Flows/Send.lean`: ops 41, 42, 61, 62; the widths opening, kernel selection by name, the
status gate, ephemeral pairs.

Theorems:
- **T3** (released: widths, status, timestamp, envelope, ephemeral public key);
- **T4-SEND** relative to the kernels (`bundleSeal_spec`, `buildPublicOfficial_spec`);
- **ORD-1** restated over the Lean flow (P4's theorem applies unchanged if P4 is done).

Tests: Q, F, D.

Depends on S12. **3–4 weeks. Medium.** T7 (P5) is separate and can trail.

---

**S14. Receive a first message.**

Goal: ops 48–51 in Lean.

Scope: `Flows/Receive.lean`: steps 1–17 of `ReceiveKernels.lean` with shape-driven kernel
selection; the provisional-id rule moves next to `contactAssign`.

Theorems:
- **T3** (the opened shapes as listed in B.1);
- **T4-RECV** from ReceiveProofs `*_spec` / `*_rejects`;
- the provisional-id lemma: ids are distinct within a session and never collide with
  application ids < 2^128 − 2^64. **Default** range: 2^128 − 3 downward, as today; the lemma
  needs fewer than 2^64 messages.

Tests: Q, F (signup, ceremony), K (`check_receive_kernels.py`), D.

Depends on S12. **3 weeks. Medium.** Concurrent with S13 and S15 if two engineers take one each
(separate flow files; builds take turns).

---

**S15. Device refresh.**

Goal: ops 56–60, 64, 65 in Lean.

Scope: `Flows/Refresh.lean`: fetch, take, shape, the 9-step establish, scratch seal and commit.

Theorems:
- **T3;**
- **T4-REFRESH** (`bundleShape_spec`, `structural_value`, `bundleRebind_spec`, `rebind_rejects`,
  `establishSession_spec`, the kem specs; the `encapsulate` composition stays open: PRODUCT_TODO
  10);
- **ORD-2.**

Tests: Q, F (`--multi-device`, `--recovery devices,refresh-retry,identity,bundle-fault`), K
(`check_bundle_kernels.py`), D.

Depends on S12. **3 weeks. Medium–strong.**

---

**S16. Upgrade, account, ceremony; closing the C++.**

Goal: the last operations (32, 47, 80, 81, the TEST admissions 44 and 46 behind `Config.test`);
then delete the legacy library.

Scope:
- `Flows/{Upgrade,Account,Ceremony}.lean`;
- delete `legacy_abi.cpp`, `service_kernels.h`, `tls_kernels.h`, `dyn_word_mask.h`,
  `x25519_fast.h`, `split_ecdh.h`, `edwards_points.h`, `hinted_points.h`, `gcm_shares.h`,
  `field_program.h`, `kernel.h`, `tls_worker_v3.cpp`;
- remove the legacy wrappers from `Reveal.lean`;
- the lint forbids `Legacy`;
- `Security.lean` version 2: sections 6–7 complete.

Theorems:
- **T4-CEREMONY** (`ceremonySecrets_spec`, `masked_hides`, `registerPlaintext_spec`);
- **T4-UPGRADE;**
- **T3** for both.

Tests: Q, F, K, E, D. Then, once, the whole F set in both modes with `--strict-produced` and
`--link-delay-ms 1`.

Depends on S13, S14 and S15. **2–3 weeks. Medium.**

---

**Proof tracks.** These are Lean-only, in new `*Proofs.lean` files, and touch no file the
engineering stages edit, except where noted.

- **P1. T1, the reveal policy.**
  - Scope: new `Node/Policy/ReceiveSpec.lean` and `ReceiveProofs.lean`. If proofs need it,
    restructure `Policy/Receive.lean` without changing behaviour; then D must stay identical.
    Extend `Recovery.checks` into a property test: random streams against the reference
    classifier.
  - Depends on S2. **3–5 weeks. Strong.**
- **P2. T8, request templates.**
  - Scope: `Node/Policy/RequestProofs.lean`.
  - Depends on S2. **2 weeks. Medium.**
- **P3. T2, printers and marks.**
  - Scope: `FlatLowering.lean` (a parser and a round-trip theorem), `EmitFlatKernel.lean`
    (`layoutText` derived from the kernel's declared fields, with a theorem), `EmitWordMask`'s
    V3 printer.
  - **Touches the emitters:** after it, one full re-lowering and manifest production, heavy and
    alone. The new manifest must be byte-identical to the old (a check that the change preserved
    outputs).
  - Depends on S1; best after S9, which also changes `EmitWordMask`, so the re-export happens
    once. **3 weeks + one re-lowering. Medium.**
- **P4. ORD-1, ORD-2, T11.**
  - Scope: `Node/Session/*Proofs.lean`, over an event abstraction of `Channels` and the flow API.
  - Depends on S7; ORD-2 again after S15. **2–3 weeks. Medium.**
- **P5. T7, what the server receives.**
  - Scope: new proof files about the deployed `signal-seal-*`, `*-request-ctr` and
    `bundle-fetch-ctr` definitions, composing `boundSeal` (a value theorem to write),
    `SpqrSend` / `ChainSend` (bridged by `Sha256Ripple.evaluationHom`), and the slot insertion.
  - **Default:** prove about the definitions as they are. If a definition must change, schedule a
    re-lowering with P3's.
  - Depends on S1. **5–8 weeks. Strong.**
- **P6. T13, receive gating, accept direction.**
  - Scope: new proof files on `ReceiveFirst`.
  - Depends on S1. **4–6 weeks. Strong.**
- **P7. Optional: the cut-and-choose counting bound in Lean.**
  - **Default: not done** (no Mathlib). The written argument and `check_parameters_128.py` stay.
  - **Done 2026-11-12 in `proofs/` (Mathlib), for the model** (a bad set fixed before one uniform
    challenge permutation of the `2BN` positions; first `BN` opened, the rest `N` buckets of `B`;
    undetected iff it lands on a nonempty union of whole buckets):
    `CutAndChoose.cut_and_bucket_probability` (probability exactly `C(N,t)/C(2BN,Bt)`,
    `parameters.py`'s `bound(t)`), `undetected_count_zero` (`B ∤ |S|` or `S = ∅`: never);
    `CutAndChooseAll.bound_step` / `bound_le_bound_one` (`bound` non-increasing on `1 ≤ t ≤ N`
    for every `N` and `B ≥ 2`, so `t = 1` is the worst case); `CutAndChoose.*_bound_t1` and
    `CutAndChooseAll.*_bound_all_t` (`bound(t) < 2⁻¹²⁸` for every `t`, profiles 2¹⁹/8, 256/14,
    512/13, 1024/12); `CutAndChooseAll.*_undetected_lt` (every bad set: probability `< 2⁻¹²⁸`).
    **Not covered:** that `dyn_word_mask.h` / `dabit_generator.h` implement the model (P-CUT (d),
    (e) and the composition of the two challenge permutations are assumptions there).

**Future: X1 (stock) after S16; X2 (rotation) after S7 and S8** (section 9).

### 10.3 Order and concurrency (two engineers, one heavy job at a time)

| Period | Engineer A (engineering) | Engineer B (proofs, daemon) | Files shared? |
|---|---|---|---|
| 1 | S0 | — | — |
| 2 | S2 | S1 | no |
| 3 | S4 | S3 | no |
| 4 | S5 | P1 (after S2) | P1 may restructure `Policy/Receive.lean`; S5 does not edit it |
| 5 | S6 | P2, then P6 | no |
| 6 | S7 | P5 | no |
| 7 | S8 | P4 (after S7) | no |
| 8 | S9 (Rust, Lean flows) | S9 (model, T12, P-RAND, T4-CONTACT) | split by file: flows vs `*Proofs.lean` |
| 9 | S10 scripts and fixtures | S10 proofs | as above |
| 10 | S11 | S11 proofs; then P3 (re-lowering scheduled alone) | P3 touches emitters only |
| 11 | S12 | S12 proofs | as above |
| 12 | S13 | S14 | separate flow files |
| 13 | S15 | S15 / ORD-2 proofs | as above |
| 14 | S16 | `Security.lean` v2 | |

**Totals.** Engineering about 40–48 weeks; proofs about 35–50 weeks. Run in two tracks, that is
about 11–13 months of calendar time.

**The one-heavy-job rule** means harness runs of one engineer and full builds of the other take
turns through `scripts/heavy.sh`. Each F run takes about 1–2 hours of machine time for both
modes. Plan stage ends accordingly.

---

## 11. What changes for the people running it

- **Binaries:** the controller name is unchanged; the worker is `node_worker`.
- **The daemon:** the configuration gains `worker.control_port` (default `port_base + 20`). The
  firewall and WireGuard rules must allow it.
- **Settings:** `SIGNAL_LOCAL_*` work only with `--test`. A mismatch of the agreed settings
  aborts at session start with a message naming the setting.
- **Development:** the non-strict circuit production needs the `--dev` build of `node_worker`.

---

## 12. Risks, open questions, and the defaults chosen

| # | Risk or question | Default |
|---|---|---|
| R1 | **Latency from finer batches.** Each data reply costs one agreement message delay. | Plain agreement. Measure in S9 at `--link-delay-ms 1`. If over 5 %, deferred agreement (5.2). |
| R2 | **Local curve arithmetic in compiled Lean** may be slow: hint computation is about 63 window bases per point (each four doublings), a few points per message received or contact prepared. Lean `Nat` is GMP-backed. | Extended coordinates, no square roots except the lift's one public root. Measure in S11. If over 50 ms per message, precompute window tables per point. |
| R3 | **Field-program re-export (S9) and the re-lowering in P3** are heavy (memory). | Each alone, through `heavy.sh`, at night. P3's manifest must come out byte-identical. |
| R4 | **The legacy/Lean handle coupling in S9–S16** (contacts' wires shared through `legacy_get` / `legacy_put`). A bug can confuse handles. | Handles are never reused (as today). The S9 differential fixture compares both paths on the same inputs. |
| R5 | **Two mask pools during S10–S16** (legacy C++ and Lean) cost extra mask generation. | Accept (about 0.6 s per session today). |
| R6 | **Proof sizes are guesses.** T1, P-CUT, T7 and T13 could double. | The engineering stages do not wait for proofs, except where a stage names its theorem as a deliverable (S9–S16: T3/T4/P-*). If such a proof overruns by 2×, the stage ships with the theorem stated, the proof as a tracked hole in `Security.lean`'s "open" list, **never as `sorry`**. Owner to be told. |
| R7 | **Assumptions that stay hypotheses:** H-GROUP (Edwards law), H-QR, `idealCommit`; the engines' ideal behaviour. *2026-11-12: H-QR is no longer a hypothesis — discharged in `proofs/` by `Prime25519.prime_modulus` and `QuadraticResidue.{two_not_square, euler_criterion, euler_nonsquare, sqrtMinusOne_eq_power, candidate_fourth_iff, candidate_sq}`, applied to the programs by `recipient_check_zero_iff` / `recipient_x_mul_self` (`EdwardsAffine.recipient`), `lift_select` / `liftOpen_square_iff` (`EdwardsHinted.liftOpen`) and `XEdDsaRecover.recover_valid_iff` / `recover_x_mul_self` (`XEdDsaField.recover`). H-GROUP, `idealCommit` and the engines' ideal behaviour stay.* | Stated in theorem hypotheses and listed in `Security.lean`'s header. |
| R8 | **Rust linking emp and MP-SPDZ** through `build.rs` may be fiddly (C++20, OpenSSL 3.5, thread pools, the 1 GB stack of `big_stack.h`). | Build the ABI as a static library with the existing `build_hybrid_v3.py` and link it. Run the engines on a thread with the 1 GB stack, as `run_with_stack` does. |
| R9 | **Semi-honest mode.** The instruction set must run on `ShSession` too. | `engine_abi` per mode. The scripts are the same. The cut-and-choose has a semi-honest variant (`dyn_word_mask.h:20-43`), kept as `Masks.generateSemiHonest` with only P-CUT (a). |
| R10 | **The retired fixture checks** (`check_signal_service_v3.py`, `check_tls_application_v3.py`) test undeployed paths. | Retire in S7. Keep `check_tls_worker_v3.py`. |
| R11 | **Daemon link authentication.** | Sealed replies and a replay cache in S3. TLS deferred to PRODUCT_TODO 7. |
| R12 | **`keys.json` to the peer.** | Keep, typed as OWN (owner's policy). If the owner later erases the identity key after `store` (CEREMONY.md section 8), it is `Channels.saveShare`'s inverse, a one-function change. |
| R13 | **State nonce reuse** (NEEDS_REVIEW 3b: "should the state seal refuse a nonce it has used"). | T10 requires distinct nonces within a session. Across sessions, rely on 64-bit joint randomness, as today. |
| R14 | **The TEST hook compiled into the field engine** (`EMP_HYBRID_TEST_FAULTS`). | Removed from the production build in S8. |
| R15 | **Unsure: whether the 5 `bv_decide` proofs need `Lean.ofReduceBool`.** Untracked logs say no. | S1 settles it. |
| R16 | **Unsure: what `handoff_client`'s parity shares reveal.** Not read; outside this repository. | Treated as trusted and public by design, named `Reveal.parity`. A review of `secret-shared-db` is outside this plan. |
| R17 | **Unsure: the field engine's behaviour on handles dropped by Lean.** It never frees shares (PERFORMANCE.md). | `drop` of field handles is a no-op until the engine frees; memory bounds stay with the daemon's `max_megabytes`. |
| R18 | **The `Challenge` domain string grows on every mask generation** (`dyn_word_mask.h:52` prepends to it). Harmless but unbounded. | The Lean port uses a fixed domain per call (P-CHAL). |
| R19 | **Deferred agreement (if R1 triggers) is a change to what the peer may receive before agreement.** | Allowed only for instructions before the batch's first opening or exchange. Recorded in NEEDS_REVIEW when switched on. |
| R20 | **Owner decisions still open elsewhere** (CEREMONY.md section 8; NEEDS_REVIEW 3, 3b; PRODUCT_TODO 8) do not block any stage. | Rotation is X2. The hinted programs stay behind their switch. |

**Not in this plan:**
- the engines' own correctness (NEEDS_REVIEW 1);
- `secret-shared-db`;
- the Signal-identity index (PRODUCT_TODO 3);
- the stock's engine work (X1 only reserves its place);
- HTTP/2 and other fingerprint work.
