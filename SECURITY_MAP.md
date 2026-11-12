# Security map: what a node sends, what it opens, what is proved

**Describes commit `d6c6cd9`** (branch `two-party-hybrid-worker`, 2026-11-11). The tracked tree
was clean when this was checked. `PublicServiceController.lean` is identical at `fda5c3d` and
`d6c6cd9`. Every `file:line` below was re-read against `d6c6cd9`. If the code moves, trust the
names, not the line numbers.

Companion: `REORGANIZATION_PLAN.md`. It turns sections B to D into work.

**How this was made.**
- **Read whole:**
  - `PublicServiceController.lean` (3,349 lines);
  - `TlsWorker.lean`, `TlsWorkerPipe.lean`, `TlsWorkerProcess.lean`, `TlsApplication.lean`;
  - the end of `TlsClient.lean` (150-249);
  - `tls_worker_v3.cpp`, `tls_kernels.h`, `service_kernels.h`, `kernel.h`, `dyn_word_mask.h`,
    `field_program.h`, `peer_link.h`, `profile.h`, `gcm_shares.h`, `split_ecdh.h`,
    `edwards_points.h`, `x25519_fast.h`, `hinted_points.h`, `dyn_session.h`, `field_engine.h`;
  - `node_daemon/src/lib.rs` and `node_daemon/src/bin/node-daemon.rs`;
  - `PRODUCT_TODO.md`, `NEEDS_REVIEW.md`, `CEREMONY.md`.
- **Read in part:**
  - `dabit_generator.h` (`Challenge`, the static generator);
  - `build_hybrid_v3.py`;
  - `SEALED_SENDER_AGREEMENT.md` (variant C, the table proposal);
  - `PERFORMANCE.md` (the last three sections);
  - the option list of `check_signal_service_local.py`.
- **Section C** was checked by a separate read-only pass over the theorem files. It marks
  each entry **[R]** (statement read) or **[N]** (name and line confirmed by search only).
- **Not read:**
  - `handoff_client` (in the `secret-shared-db` repository);
  - the EMP and MP-SPDZ engine sources, `field_engine.cpp` (apart from one test hook) and
    `public_auth.cpp`;
  - the Python scripts, apart from the lines cited.

**Classification used for every value.**
- **P (public by design):** both nodes may know it, and so may the receiving party.
- **S (secret):** secret-shared between the nodes, or one node's own share.
- **O (opening):** derived from secrets and released by an explicit opening. Section B lists
  every opening.
- **OWN:** our own Signal private keys. The owner's policy allows these in the clear on both
  nodes. Only the contact list must stay secret.

---

## 0. The node in one picture

```
 application ─┐  plaintext TCP, one JSON line each way, no TLS, replies unsigned
              ▼
        node-daemon (Rust)  ── one listener (config.listen) serves the application AND the
              │                other daemon (ops "peer-*", HMAC-SHA256, node-daemon.rs:1185)
              │ spawns, env, files, reads stdout; stderr → state/logs/*.log
              ▼
  public_service_controller (Lean)    ← opens NO socket itself
     │ pipe (stdin/stdout, TlsWorkerPipe)     subprocesses: public_auth, handoff_client,
     ▼                                        KEM tool, a second controller (ceremony stages)
  tls_worker_v3 (C++)   stderr inherited → the daemon's log
     ├─ Boolean engine NetIO, plain TCP, PORT (+ siblings, triple-stock factories)  ─▶ peer worker
     │     also carries: request agreement, op 39 exchanges, server records, commit-then-open,
     │     manifest/pin agreement, conversion comparisons
     ├─ field engine (MP-SPDZ based), TLS with Player-Data certificates, PORT+10 (+ stock lines) ─▶ peer
     ├─ leader only: TCP to the Signal server (direct, or SOCKS5 to a local Tor)
     └─ non-strict mode only: popen("python3 circuit_cache.py kernel …")
                    handoff_client (other repo) ─▶ the five database nodes
```

The controller does no network I/O. Everything it says to the Signal server or to the other
node goes as an RPC to its own worker (`TlsWorkerPipe.make`, TlsWorkerPipe.lean:57-90). The
worker owns every socket.

---

## A. Every external communication

### A.1 The Signal server

**Who touches the socket: the leader worker (party 0) only.**
- **Operation 9** sets up the connection (`tls_worker_v3.cpp:368-384`):
  - direct: `getaddrinfo` on the hostname (`:377-381`), so the leader's resolver sees the hostname;
  - or a SOCKS5 handshake (`socks_connect`, `:48-75`). Username/password is the only method
    offered; the server is named by hostname (address type 3); the proxy address must be
    numeric.
  - The whole request is agreed between the workers. Every connection of a worker must go
    the same way (`:375`).
- **Operation 10** writes the agreed bytes verbatim (`:385-391`). A failed write is dropped; the
  next poll reports the closure.
- **Reads:**
  - `server_record` (`:108-113`) for operation 11, which ends the session on a close;
  - `server_record_soft` (`:116-120`) for operation 17, which reports `[0]` to both parties.

**What the worker checks.** Both workers agree each request's bytes before acting (A.2 (a)). The
worker does **not** check that an operation-10 payload is a record the engines sealed: whatever
both controllers hand it goes to the server.

The controllers hand operation 10 only bytes produced by `TlsWorker.transport`,
`applicationTransport` or `waitingTransport` (TlsWorker.lean:172-207):

| Bytes on the wire | Produced by | Class |
|---|---|---|
| ClientHello (1 or 2) | `TlsClient.runWithScalar` (TlsClient.lean:204-212). Under the libsignal profile, the random and session id are two hashes of the joint random value from op 1 (:202-203). The key share is the public sum of the split-ECDH halves (`split_ecdh.h:82-97`) | P |
| Client Finished record | op 6 `tls-finish`, output `record` (TlsClient.lean:225-227) | O |
| Application records | `TlsApplication.send` → op 13: `tls-seal-class`, the slot sealers, or `tls-seal-ctr`, then `tagged` (`tls_kernels.h:197-240`): header, ciphertext, tag | O |
| KeyUpdate, close_notify | op 14 (`tls_kernels.h:242-245`). Content restricted to three constants (TlsWorker.lean:240-242, `tls_worker_v3.cpp:338-341`). A KeyUpdate is also sent by `TlsApplication.send` itself when the record policy requires one (TlsApplication.lean:95; `TlsApplicationPolicy.needsUpdate`, :34) | O (ciphertext of P content) |

**The plaintexts inside those records.** Every call to `TlsApplication.send` hands over a buffer
handle of one of two kinds.

1. **Public buffer (op 30; the controller's bytes; all P).** Sites, by what is sent:
   - the anonymous upgrade request: `anonymousUpgrade`, controller 1322-1324, sent at 1613,
     1740, 2367, 2522;
   - control replies: `PublicReceive.replies` (668-679);
   - `200 OK` replies to server requests: `PublicReceive.reply` (642-651);
   - keepalives (655-660) and WebSocket pings (664-665);
   - the ceremony's public requests (`call`, 3186-3203).

   The 4-byte WebSocket masks come from joint randomness (op 33).
2. **Private buffer, filled by a slot sealer.** These are:
   - the authenticated upgrade (op 32, kernels `signal-upgrade(-shared)`, credentials inside);
   - a send's request frame (op 42 `signal-request-ctr`; op 62 `bundle-request-ctr`);
   - the prekey fetch (op 56 `bundle-fetch-ctr`);
   - the registration request (op 81 `ceremony-register-ctr`).

   For each, the controller builds a frame with **zeroed slots**:
   - `PublicRequest.build` 727-753, `assemble` 762-777, `buildFetch` 780-784,
     `buildDevices` 787-801;
   - the ceremony frame at 3255-3262.

   The kernel inserts the contact's UUID, access key, and device and registration ids, or the
   password and recovery password, at the public offsets. The bytes outside the slots are P.
   The slots are S. The envelope inside a send frame is O (B.1, ops 41 and 61).

**Call sites in the controller.**
- `TlsApplication.send`: 14 direct (1423, 1608, 1626, 1735, 2059, 2076, 2145, 2364, 2504, 2525,
  2621, 2716, 2731, 3272).
- `sendPublic` / `sendOn` (both wrap op 30 + send): 22 uses.
- `TlsClient.run`: 1406, 2357, 2516.
- `TlsWorker.connectVia`: 1404, 2356, 2515.
- `TlsApplication.keyUpdate`: 2448, 2890.
- `TlsApplication.abort`: 3300, 3306, 3319.

All of them are local closures inside the one `main` do-block (1189-3349).

**Server → node (reads).** The server's records reach the controller only as:
- the record bytes (P), returned by ops 11 and 17;
- opened event bytes (op 12; B.1);
- opened byte ranges (op 43; call sites 1876 and 1910 in `record`).

**Which** bytes of a record are revealed is decided only by the controllers (B.4).

**Metadata visible to the server or the network.**
- Record sizes. These are size classes, apart from the request kernels, whose sizes are exact.
- Timing; how many connections there are.
- The SOCKS credentials, `tls-mpc-<16 hex of the session id>` / `send-i-of-N` / `receive`
  (`Circuits.labels`, 830-834). Only the local Tor client sees them.
- Which contacts go on which connection (`Circuits.assign`, 823-825).
- Request ids: 2^63 + n per connection, and 2^63 + 2^32 + n for refresh requests (2110).
- Message timestamps from the agreed clock (`restamp`, 2008-2024).
- The keepalive or ping cadence (25 s, 31 s).

### A.2 The other MPC node

Four transports reach the other node. Only the field engine's is encrypted:

1. **The Boolean engine's main `NetIO`.** Plain TCP; `peer_link.h:16-19` says to restrict it
   with the firewall or tunnel. The worker reuses it for (a)-(d), (f) and (g) below.
2. **Its sibling channels** (the triple-stock factories, `dyn_session.h:75-86`). They carry (h)
   and engine traffic.
3. **The field engine's connections:** TLS with the parties' certificates (`peer_link.h:16-19`).
4. **The daemons' link** (row (i)):
   - line JSON with HMAC-SHA256 and a 60-second freshness window (`lib.rs:227-250`);
   - not encrypted, no replay cache;
   - **the replies are neither sealed nor checked** (`peer_call` → `call`, node-daemon.rs:355-357,
     lib.rs:215-222).

| # | What | Where | Content | Class |
|---|---|---|---|---|
| a | Request agreement, every operation except 8 | `agree`, `tls_worker_v3.cpp:137-146` | SHA-256("tls-worker-v3:"+session‖op‖seq‖len‖payload). For ops 36, 39, 47 and 53, only a public prefix (16 bytes for op 36, none for the others) and the length are hashed (`:160-166`). Op 8 (abort) is local and not agreed (`:498`) | P (hash; see note) |
| b | Controller-to-controller exchange, op 39 | `:268`, `channel.transfer` of the raw payload | Whatever the controller's `swap` passes (14 call sites, table below) | per row |
| c | Commit-then-open | see the list below this table | commitments, nonces, values; the public points kA·B | P |
| d | Server records, leader → follower | ops 11 and 17: `:111`, `:353-358`, `:396` | 4-byte size (0xFFFFFFFF = "closed"), then the record | P (TLS ciphertext) |
| e | Engine protocol traffic | `dyn_session.h` (emp-ag2pc inputs, garbling, `decode` openings); the field engine (inputs, multiplications, `checked_open` with MAC checks) | engine-internal | S / O; trusted engines |
| f | Re-comparison of opened values | `tls_kernels.h:88`; `dyn_word_mask.h:127`; `x25519_fast.h:46`, `:61`; `hinted_points.h:170` | values already opened (B.2), sent again and compared | O |
| g | Circuit pins | `kernel.h:157` (manifest digest, strict mode) or `:183` (128 bytes per kernel, non-strict) | SHA-256 pins | P |
| h | Triple-stock announcements | `dyn_session.h:61-62` | 1 byte per batch | P |
| i | Daemon peer messages | sent by `peer_call` (node-daemon.rs:355-357), handled at `:446-567` | see the list below this table | P |

**Commit-then-open sites, row (c):**
- `joint_random` (`:148-154`): ops 1, 20, 32, 33, 45;
- the sealed-sender offset (`service_kernels.h:532-538`, `:656-661`);
- the split-ECDH share exchange (`split_ecdh.h:82-97`);
- the offset agreement's K₀ (`edwards_points.h:74-86`, `hinted_points.h:204-220`);
- the cut-and-choose challenge (`Challenge::permutation`, `dabit_generator.h:36-56`). It is a
  concatenation, not an XOR, so a mirrored commitment does not bias it.

**Daemon peer messages, row (i).** Each message carries `at` and `mac`:
- `peer-ping`;
- `peer-agree {job}`;
- `peer-start {job, session, port}`. In long-lived mode `port` is absent (`:1125`).
- `peer-receive {session, port}`;
- `peer-serve {session, port}`;
- `peer-ended {session}`;
- `peer-finish {job}`.

**Note on (a).** A hash of every request goes to the peer. That includes requests whose payload
holds values the two parties hold in the clear:
- op 44: a TEST contact record;
- op 46: our identity private key;
- op 51: our prekey private keys and the decapsulated Kyber secret.

Both parties must hold the same bytes anyway for the hashes to match.

**The 14 `swap` call sites.** `swap` is defined at 1467. Each call is two or more op-39 RPCs.

| Line | Function | Sent | Class |
|---|---|---|---|
| 1485 | `agreedNow` | this party's clock (8 bytes); skew checked (2 min) | P |
| 1537 | `dbSubmit` | `[1]` "submitted" | P |
| 1556 | `dbRead` | **parity shares of a database read** (the file written by `handoff_client parity`) | P by design; depends on `handoff_client` |
| 1591 | `dbDeal` | 16-byte vector: which database nodes reported "committed" | P |
| 1674 | session start (daemon notify) | SHA-256 of the ids absent or not yet readable | P |
| 1953, 1957 | `dbSubmitSoft` | `[1]`, then this party's acknowledgement bit | P |
| 2114 | `agreedClock` | clock. **No skew check** (unlike 1486 and 2995) | P |
| 2253 | `loadJob` | hash of the absent ids | P |
| 2756 | `deliverJob` | journal entries (message number, contact id, result code) | P |
| 2913 | `deliverJob` | SHA-256 of the canonical per-id results | P |
| 2992 | `serve` | hash of the job name, stop flag, clock (skew checked at 2995) | P |
| 3165 | ceremony `shared` | contents of `number.txt`, `captcha.txt` and **`keys.json` (whole file, private keys included; CEREMONY.md:61-62)** | P / OWN |
| 3233 | ceremony | contents of `code.txt` (the SMS code) | P |

The worker does not inspect op-39 payloads. Op 39 is the controller's free-form channel to the
peer: only the controller decides what goes into it.

### A.3 The five database nodes

The node reaches the database nodes only through `handoff_client`, run as a subprocess
(`SIGNAL_DB_CLIENT`). There are **12 call sites in 6 functions**:

| Line | Function | Command | Bytes that reach the nodes (sent by the client) | Class |
|---|---|---|---|---|
| 1536, 1538 | `dbSubmit` | `write-blob` (twice: submit, then learn the commit) | blob file = nonce(8) ‖ check(16) ‖ ciphertext (‖ kinds ‖ count), from `contact-seal` / `account-seal` / `scratch-seal` | O (kinds P) |
| 1952, 1954 | `dbSubmitSoft` | `write-blob` | same | O |
| 1554 | `dbRead` | `read` (`--request FILE` or `--account`) | the application's signed request | P |
| 1555, 1558, 1559, 1560 | `dbRead` | `parity`, `verify-signatures`, `parity-sum`, `combine` | local computation on this party's read. Its output, `*-shares.json`, is **this party's combined key shares** | S (local) |
| 1581 | `dbDeal` | `deal --signup-token --id --session` | the token (P), a session id from joint randomness; output: **this party's summand** | S (local) |
| 1306 | `main` `db-delete` | `delete` (up to 40 times) | the application's signed delete request | P |
| 1803 | `receiveFirst` | `token-id --signup-token FILE --require-fixed` | local parse of the revealed text | P |

Every call passes `--key` with the path of this node's database client key (`dbParty`,
1462-1463). The controller never reads that file. What the database nodes learn is decided by
`handoff_client`, which lies outside this repository and was not read.

### A.4 The application

**Channel.** The application talks only to the daemon:
- listener `config.listen` (node-daemon.rs:1235); the same socket takes the peer daemon's ops;
- one JSON line in and one out per connection (`lib.rs:199-212`);
- plaintext;
- dispatch at node-daemon.rs:1183-1199.

| Op | In | Out | Authenticated? |
|---|---|---|---|
| `notify` | signed request (ids, message hash, nonce, issued_at, signature), message text | `{ok, job, state}` | Ed25519 signature, freshness and the message hash (`submit`, :361-399) |
| `delete` | signed delete request | `{ok, job, state}` | the same |
| `wait` | job digest, timeout | the job's `result`: per-id `result` and `reason`, `result_digest`, `node.detail`, `node.evidence` (the database nodes' signed delete report) | **no** |
| `events` | `after`, `wait` | signup events `{seq, event, id, at}` | **no** |
| `status` | — | counters, session state, pid, memory | **no** |

Anyone who can reach the port can read every job's per-id results and every signed-up id. The
ids are the application's u128 ids. The mapping from id to Signal account is not exposed.

**Daemon → controller.**
- The argument list and the environment (`session_command`, :623-654). The session-kind
  variables are removed after the configuration's `environment` object is applied (:631-636),
  so the configuration cannot set them.
- Files:
  - `request.json` and `message.txt` (`run_notify`, :756-787);
  - `jobs/*-request.json`, `*-message.txt`, then `job.json` through `job.staged` and a rename
    (`hand_over`, :961-992);
  - `stop` (`maintain_send`, :1047).
- For deletes: `db-delete` with `delete.json` (`run_delete`, :789-811).

**Controller → daemon (stdout lines).**
- The final report (3333-3347). It includes `received` (the revealed texts), `results`,
  `circuit_sends`, `unknown` and `not_yet_readable`.
- `ready` and per-job result lines (`emit`, 2935; sent at 2963 and 3019).
- Signup events (1853).

The daemon reads them in:
- `supervise` (:660-736);
- `send_line` (:924-958);
- `notify_results` (:283-300);
- the receive callback (:827-841).

### A.5 Local disk

**Controller writes** (with class):

| Line(s) | File | Class |
|---|---|---|
| 1172 | `SIGNAL_RECORD` JSONL (`recordEvent`, 17 call sites plus `recordSend` at 2028): revealed server bytes, the certificate chain, request templates with zeroed slots, statuses; in the ceremony also the captcha, the SMS code, response bodies | P (the code's own claim, 1163-1167) |
| 1254, 1289, 1290 | ceremony `hosts`, `STAGE.log` (the child's stderr), `STAGE.json` | P |
| 3169 | ceremony: copies of `number.txt`, `captcha.txt`, `keys.json` received from the peer | P / **OWN** |
| 3248, 3249 | ceremony **`password.share`, `recovery.share`** | **S** |
| 3285 | ceremony **`credentials.share`** (account id share ‖ password share, hex) | **S** |
| 3286, 3294 | `account.json`, `certificate.b64` | P |
| 1533, 1949 | database `blob-*` | O |
| 1557 | database `*-parity-theirs.json` | P (by design) |
| 1801, 1810 | `token-received`, `token-ID` (the revealed text) | P |
| 1829, 2295 | TEST store `SIGNAL_LOCAL_STORE/ID` = hex(**key share** ‖ version ‖ sealed state) | **S** |
| 2894 | journal line per settled result | P |
| (via `handoff_client`) | `*-read.json`, **`*-shares.json`**, **`deal-*.json` (summand)** in `SIGNAL_DB_WORK` | **S** |

**Controller reads:**
- the node configuration (ceremony, 1240);
- `credentials.share` (1263);
- the TEST export `SIGNAL_LOCAL_EXPORT` (1629, 1749, 1995, 2243). It holds **our identity
  private key** (OWN), **our prekey private keys** (OWN) and TEST contact records (S). Parsers:
  `readExport` 1081-1097, `readSelf` 1101-1106, `readReceive` 1122-1138.
- the request and message files (1652-1653, 2236, 2331, 3000);
- `job.json` and `stop` (2977-2987);
- the database client's JSON outputs (1465), the parity file (1556), `delete.json` (1309);
- journals (2753);
- the TEST store (1702);
- the ceremony inputs (3161).

**Worker:**
- Reads the manifest and the `.flat` / `.layout` files (`kernel.h:99-112`, `:30-45`).
- Reads the field programs and `swap-bits.flat`. Their SHA-256 pins are compile-time
  constants:
  - `field_program.h:36-42`;
  - `x25519_fast.h:14-16`;
  - `split_ecdh.h:76-77`;
  - `edwards_points.h:13-14`;
  - `hinted_points.h:91-95`;
  - `service_kernels.h:107-109`.
- The field engine reads its TLS material (`Player-Data/`).
- Appends kernel names to `CIRCUIT_CACHE_LOG` / `CIRCUIT_REFUSED_LOG` (`kernel.h:146`, `:164`,
  `:170`).
- In non-strict mode: reads the cache directory (`:124-149`) or runs `popen("python3 …")`
  (`:176`).

**Daemon:**
- Writes:
  - `state/work/*` and `hosts` (:625);
  - `logs/*.log`: each controller's stderr, which includes its worker's inherited stderr
    (:661-666);
  - `journal/`: removed on completion at :942 and :784; cleaned after a day at :1227-1234;
  - `events.jsonl` (:835);
  - the `serve/` directory.
- Reads the configuration, the database network file and **the peer HMAC key file**
  (:107-182).

### A.6 Logs (stdout, stderr)

- **Controller stderr:**
  - the database client's stderr (1458);
  - `revealed HEX` under `SIGNAL_LOCAL_TRACE` (1919);
  - the device-refresh count (2172);
  - recovery notes (`note`, 2479), which include contact ids and results;
  - the serve summary (3065).
- **Worker stderr:**
  - per operation: code, seconds, gate counts, bytes, busy time (`tls_worker_v3.cpp:507`);
  - exception texts (`:509`);
  - the profile (`:511`), the peer address (`:425`), the mode (`:491`), totals (`:512-513`);
  - refused kernel names (`kernel.h:163`).

  The worker moves its own stdout to stderr (`:409`), so anything a linked library prints
  goes to the log. No value is printed by the worker. Op 80's reply (this party's password
  share) goes only over the pipe.
- **Daemon stderr** (`log`, node-daemon.rs:27-29): request digests, session names, signup ids
  (`:839`), memory figures. Stdout: `listening ADDR` (`:1246`).
- **Controller stdout:** A.4. The final report includes the `received` texts and per-id results.

### A.7 Environment variables

**Read by the controller:** 36 `IO.getEnv` sites, 34 distinct variables. `dbEnv` and the
`db-delete` `setting` helper read further `SIGNAL_DB_*` names.

| Variable | Effect | Notes |
|---|---|---|
| `SIGNAL_LOCAL_CREDENTIALS` (1333) | **this party's XOR share of the account credentials, as hex** | **S in an environment variable.** The ceremony's parent controller puts it into a child controller's environment (1267, 1272) |
| `SIGNAL_LOCAL_RECEIVE`, `_EXPECT`, `_EVENTS`, `_EXPORT`, `_STORE`, `_EXTRA_CONTACTS`, `_NEW_CONTACT`, `_BROADCASTS`, `_KEM` | session kind; TEST scaffolding | `_KEM` names the tool that receives the **Kyber private key on its argv** (1760) |
| `SIGNAL_LOCAL_TIMESTAMP` (1481, 2010) | fixes the clock (TEST) | must match on both nodes |
| `SIGNAL_LOCAL_TRACE` (1918) | prints revealed bytes | P |
| `SIGNAL_LOCAL_PAUSE_AFTER` (2782), `SIGNAL_LOCAL_PAUSE_REFRESH` (2681) | **TEST pauses in the middle of a session** | on production code paths |
| `SIGNAL_RECOVERY` (2476) | `0`: the old fail-fast loop | must match; not checked up front |
| `SIGNAL_ACK_REFUSED` (1841) | `0`: leave refused messages on the server | must match; not checked up front |
| `SIGNAL_CLIENT_PROFILE` (1181) | `libsignal` / `legacy` wire profile | must match; not checked up front (requests then differ and agreement (a) fails) |
| `SIGNAL_TOR_SOCKS`, `SIGNAL_TOR_CIRCUITS` (1344-1358) | proxy and circuit count | agreed through op 9's payload |
| `SIGNAL_PREPARE_BATCH`, `TLS_WORKER_HINTED` (2208-2209) | batching | `TLS_WORKER_HINTED` is in the worker's session string; `SIGNAL_PREPARE_BATCH` is not |
| `SIGNAL_RECORD` (1169) | event log file | |
| `SIGNAL_CEREMONY` (1370), `SIGNAL_CEREMONY_DIR` (3156) | ceremony stage | |
| `SIGNAL_NOTIFY_MESSAGE_FILE`, `SIGNAL_SERVE_DIR`, `SIGNAL_NOTIFY_ID`, `SIGNAL_NOTIFY_JOURNAL` | the daemon's interface | |
| `SIGNAL_DB_CLIENT`, `_NETWORK`, `_KEY`, `_WORK`, `_REQUEST`, `_TOKENS` | database client | `_TOKENS` is TEST |

**Read by the worker** (`tls_worker_v3.cpp:421-484`, `peer_link.h:40`, `kernel.h:115-170`):
- `TLS_WORKER_TEST_LINK_SHIFT` (TEST);
- `TLS_WORKER_KEY_AGREEMENT`;
- `TLS_WORKER_SERVICE_FIXTURE` (TEST);
- `TLS_WORKER_FIELD_BATCH`, `_TRIPLE_STOCK`, `_FIELD_STOCK`, `_FIELD_DIRECT`;
- `TLS_WORKER_PEER_WAIT`;
- `TLS_WORKER_TEST_PRODUCER` (TEST);
- `TLS_WORKER_TYPED_OPEN`, `_HINTED`;
- `TLS_WORKER_PEER`, `_LISTEN`;
- `CIRCUIT_MANIFEST`, `CIRCUIT_CACHE_LOG`, `CIRCUIT_REFUSED_LOG`.

Hinted, field-direct, key agreement, typed open, the stocks and the field batch are folded into
the session string, which every agreed request carries (`:485-490`). So a mismatch there is
detected at the first request. The TEST switches, the peer wait and the addresses are not.

**Test fault switches.**
- `EMP_TEST_NATIVE_OPEN_MAC` (`field_engine.cpp:260`) is guarded by `EMP_HYBRID_TEST_FAULTS`.
  **The production worker's field-engine object is built with `-DEMP_HYBRID_TEST_FAULTS=1`**
  (`build_hybrid_v3.py:47-48` reuses the recorded field build command, which contains it). So
  this hook is compiled into the worker.
- The engine attack hooks are behind `#ifdef EMP_HYBRID_TEST_ATTACKS`:
  - `EMP_TEST_LAMBDA_LEAK`, `EMP_TEST_FALSE_GAMMA`, `EMP_TEST_OPEN_LIE` (validated-v3 patch);
  - `EMP_TEST_OUTPUT_SHARE_LIE` (`output_phase_v3.inc:31-33`);
  - `EMP_TEST_NONCANONICAL_*` (`input_phase_v2.inc:30-52`).

  The worker's compile command does not define that macro (`build_hybrid_v3.py:59`).
- `EMP_TEST_BAD_NATIVE_COINS` (`dabit_generator.h:93`) and `EMP_TEST_WORD_*` /
  `EMP_TEST_BITBLOCK_*` (`word_mask.h:84-85`, `:151-152`) are not guarded. They live in the
  templates `DaBitGeneratorV1` and `WordMaskGeneratorV1`, which only fixtures instantiate. A
  search found no use in the worker's headers.

Each hook makes the setting party (BOB) cheat, so it weakens only that party's own behaviour.

**Daemon.** It reads no environment variable. It reads a JSON configuration; that
configuration's `environment` object is passed to the controller, minus the session-kind
variables (:631-636). It sets `TLS_WORKER_PEER_WAIT`, `CIRCUIT_MANIFEST`, `SIGNAL_TOR_*`,
`SIGNAL_LOCAL_EXPORT` and `SIGNAL_LOCAL_KEM`.

### A.8 Subprocesses

| Spawned by | Program | Line | Arguments / input | Class |
|---|---|---|---|---|
| controller | worker | `TlsWorkerProcess.spawn` (controller 1383; TlsWorkerProcess.lean:33-37) | party, hosts, port, circuit tool path, session id | P |
| controller | certificate checker (`handshake_backend/public_auth.cpp`, OpenSSL) | 1387-1395 | hostname, trust root, scheme, transcript hash, signature, chain | P |
| controller | `handoff_client` | A.3 (12 sites) | | |
| controller | KEM tool `kem-decapsulate` | 1760 | **Kyber private key hex on argv**, ciphertext | OWN; visible in `ps` |
| controller | a second controller (ceremony) | 1281-1288 | **`SIGNAL_LOCAL_CREDENTIALS` = this party's share** in its environment | S |
| worker | `python3 circuit_cache.py` | `kernel.h:176` (non-strict mode only) | kernel name (restricted to `[A-Za-z0-9 -]`, `:153`) | P |
| daemon | controller | `:626`, `:795` | A.4 | |
| daemon | `ps` | `:266`, `:310` | | |

### A.9 Count and scatter (controller)

| Channel | Sites | Where |
|---|---|---|
| Worker RPC (`rpc.call`, `on.call`, `emptyReply`, `.call .x`) | **108 lines** | about 30 closures in `main` |
| TLS sends to the server | 14 direct + 22 public-buffer uses, 3 handshakes, 3 connects, 2 key updates | 14 closures |
| Exchange with the other node (`swap`) | 14 | 10 closures |
| Database client | 12 | 6 functions |
| Other subprocesses | 4 | `main` |
| `getEnv` | 36 | throughout |
| `recordEvent` / `recordSend` | 17 / 4 | throughout |
| File writes, reads, `pathExists` | about 20 / 20 / 8 | throughout |
| stdout / stderr | 8 / 6 | throughout |

**Every external channel of the controller passes through the one 2,160-line `main`
(1189-3349).** Nothing in its types distinguishes a public byte list from a secret one: `Bytes`
is used for both.

---

## B. Every value opened out of the MPC

### B.1 Kernel outputs opened through `Kernel::open` / `open_to`

`kernel.h:64-80` refuses to open an output unless the Lean layout marks it public (or for that
party). The worker performs these openings:

| Op | C++ site | Kernel → opened field | What it is | Gate | Theorem constraining it |
|---|---|---|---|---|---|
| 3 | `tls_kernels.h:124-127` | `tls-open-handshake` → `result` | type and contents of a handshake or alert record | zeroed unless inner type 21/22 and tag checked | function level only: `TlsPublicHandshake.gate_value` (:26), `application_not_released` (:42) [N] |
| 5 | `:128-132` | `tls-verify-finished` → `accepted` | the server's Finished is correct | — | `TlsHandshake.verifyHash_value` (:115), `reject_wrong_finished` (:124), function level |
| 6 | `:133-137` | `tls-finish` → `record` | client Finished ciphertext | — | function-level KDF theorems only |
| 12 | `:177-191` | `tls-open-typed` → `handshake` (1 bit), then `event` (2 bytes) from `tls-open-typed` / `tls-frame`, or `tls-open-application-class` → `event` | record kind | `accepted` from `gcm-check` | `TypedOpenProofs.tlsOpenTyped_gated` (:231), `typed_pair_refines` (:284), `class_fields` (:247), `frame_fields` (:265); `HybridKernelsProofs.tlsOpenApplication_event_private` (:106); `TlsPostHandshake.application_event_independent` (:230) |
| 13 | `:205`, `:212`, `:224`, `tagged` `:233-237` | sealers → `accepted`; `header`, `ciphertext`; `gcm-tag` → `tag` | record ciphertext; acceptance byte | — | `tlsSealCtr_spec` (SealCtrProofs:58), `gcmTag_spec` (:82), `sealCtr_with_tag_is_seal` (:139, given the halves), `sealCiphertext_padded` (RecordClassProofs:580) |
| 14 | `:242-245` | `tls-seal-ctr` → `header`, `ciphertext`; `tag` | KeyUpdate / close ciphertext | — | as op 13 |
| 12-14 (inside) | `gcm_shares.h:38` | `gcm-key-share`, `gcm-multiply` → `masked`, **to BOB only** | H^i ⊕ ALICE's fresh mask | — | `gcmKeyShare_reshare` (:366), `gcmMultiply_reshare` (:380); `GhashShares.share_hides` (model) |
| 43 | `:259-276` | `tls-reveal-masked` → `length`, then a **slice of `bytes`** opened directly by `s.open` | the received record's length and **any range both controllers ask for** | none in the kernel: every byte below the length is marked public (HybridKernels.lean:160-173) | `TlsWebSocketActivity.run_correct` (:67) for the length mask only; **no policy theorem** (B.4) |
| 29 | `:248-256` | `tls-reveal` → `length`, `byte` | one byte (older path, not used by this controller) | as above | none |
| 37 / 63 / 55 | `service_kernels.h:443`, `:958`, `:237` | `contact-open` → `accepted` | the stored blob's key check | — | `contactOpen_accepted_iff` (:275), `contactOpen_rejected` (:286) |
| 38 / 64 / 54 | `:433`, `:882`, `:229` | `contact-seal` → `check`, `ciphertext` | sealed state for the database nodes | — | `contactSeal_spec` (:217), `contact_round_trip` (:300). A key check only; **no ciphertext integrity** (file header) |
| 41 / 61 | `:545-551`, `:911-917` | `signal-widths` → `counter`, `previous`, `epoch`, `index` | varint widths of the contact's counters (about log₁₂₈ of each) | — | **none** |
| 41 / 61 | `:561-563`, `:926-929` | `signal-seal-official` / `-built` / `-fixed`, `bundle-seal` → `status`, `timestamp`, `envelope` | sealed-sender envelope ciphertext; ok bit | envelope released under `status` (`TlsProviderGate.gate`) | `buildPublic_spec` (size class); `bundleSeal_spec` (:112). **Update 2026-11-12:** value theorems now: `signal-seal-*` = sealed sender v1 (`Reference.sealV1`, a transcription of libsignal) of the reference send step's message (`KernelSpecs/SealValue.lean`, `SealSend.lean`; Security.lean `signalSeal_value`, `sealValue_accepted`); `bundle-seal` = the reference PreKey message sealed the same way (`KernelSpecs/EstablishSealValue.lean`; `establishSeal_bundleSeal_value`, `_accepted`); composed with the request frames (`serverReceives_accepted`, `establishRequest_serverReceives_refresh*`) |
| 41 / 61 (inside) | `:539-541`, `:662-664` | (field engine, `OffsetAgreement::step`) | **ephemeral public key** u(K₀ + offset·B), computed in the clear | — | `OffsetAgreement.public_key_independent` (:69; model) |
| 31 / 20 (fixture path) | `:504-506` | `signal-send(-open)` → `status`, `requestIdUsed` | | | none |
| 18 (private profile; refused by this controller) | `:589`, `:601`, `:611-612` | `ws-activity` → `accepted`; `ws-*-byte` → `status`; `ws-control-status` → `valid`, `queue` | | | |
| 50 | `:293` | `receive-unseal-message` → `certificateLength` | the **sender's** certificate length (2 bytes) | zero unless valid | `unsealMessage_rejects` (ReceiveProofs) |
| 50 | `:296` | `receive-content-shape` → `shape` (4 bytes) | plain or hinted; phone number present; phone number length | | `contentShape_spec` (no rejects) |
| 50 | `:320` | `receive-prekey-shape` → `shape` (21 flags) | id widths | | `prekeyShape_spec` (no rejects) |
| 50 | `:326` | `receive-prekey-open` → `oneTimePrekeyId`, `signedPrekeyId`, `kyberPrekeyId`, `kyberCiphertext` | our prekey ids; the 1,568-byte Kyber ciphertext | zero unless valid | `prekeyOpen_spec`, `prekeyOpen_rejects` |
| 51 | `:375` | `receive-signal-shape` → `shape` (13 bytes) | counter widths, ciphertext length, address flag | | `signalShape_spec` (no rejects) |
| 51 | `:385` | `receive-session` → `status` | | | `session_spec`, `session_rejects` |
| 51 | `:390-391` | `receive-text` → `status`, `length`, **`text`**, `layout` | **the message text** (by design: the signup token) | | `text_spec`. **No rejects theorem:** nothing says these are zero when the session failed |
| 51 | `:398` | `receive-access-key` → `status` | "one of 72 layouts matched" (Android layouts, fda5c3d) | | `accessKey_spec` via `withAccessKey_map` only; no theorem on which layout is chosen |
| 59 | `:724` | `bundle-shape` → `shape` | one flag per prekey-response byte: JSON punctuation | — | `bundleShape_spec` (:73), `BundleKernel.structural_value` (:171): 255 exactly on `" , : [ ] { }`; `layout?_sound` (:252) for the controller's parse |
| 60 | `:800` | `bundle-rebind` → `changed` | **the contact's identity key changed** | 0 unless parsed and verified | `bundleRebind_spec` (:102), `rebind_rejects` |
| 60 | `:857` | `establish-session` → `status` | one byte per device | | `establishSession_spec` (EstablishProofs:83), `establish_rejects` |
| 80 | `:691` | `ceremony-secrets` → `masked` | password ⊕ maskA ⊕ maskB | — | `ceremonySecrets_spec` (CeremonyProofs:130), `masked_hides` (:102; a per-byte bijection only) |
| 81 | via op 13 | `ceremony-register-ctr` → `accepted`, `header`, `ciphertext` | | | `registerPlaintext_spec` (:140, plaintext only) |

**Not opened, but available.**
- `signal-seal-probe` opens `text`, `wire`, `state` (chain keys) and `accepted`
  (HybridKernels.lean:470-492). It is in `HybridKernel.find` (:746) but in no inventory, so
  strict mode refuses it. Without a manifest only the absence of a caller keeps it out.

### B.2 Openings that bypass `Kernel::open` (C++ calls `s.open` / `f.checked_open` directly)

| Site | Opened | Hiding argument | Lean |
|---|---|---|---|
| `tls_kernels.h:69` `bits_to_field` | bit ⊕ ρ for each Boolean→field bit (ρ from a bit pair) | uniform ρ | none for the protocol; `FieldBits.bitXor_bits` for the program |
| `tls_kernels.h:78` `shared_scalar`; `hinted_points.h:329` `shared_bits` | bit checks of each party's scalar contribution (zero if honest) | | `FieldBits.bitCheck_bit` |
| `tls_kernels.h:86-88` `word_to_field` | (u mod p + r) mod p, then re-compared with the peer's | uniform r | `WordMask.intoField_val` (given inputs < p); `ConversionSemantics.masked_*` (model) |
| `dyn_word_mask.h:126-127` `field_to_word` | value − mask, then re-compared | uniform mask | `WordMask.from_field_roundtrip` (arithmetic only) |
| `dyn_word_mask.h:64`, `:78`, `:94`, `:115` `generate_masks` | cut candidates (both engines), bucket sums, the "kept reference in range" flags, bit-block zero checks | cut-and-choose | **none**: "the cut/bucket protocol is not modelled" |
| `field_program.h:136` | b·r for each division node (zero aborts) | uniform r | none for the protocol |
| `x25519_fast.h:44`, `:61` | z·r for each X25519 (zero ⇒ result 0, reported as `zero`) | uniform r | `X25519Fast.compiled_correct` (:229; value only) |
| `split_ecdh.h:110`; `edwards_points.h:72`; `hinted_points.h:126`, `:203`, `:247` | zero checks: on curve, bit, hint | zero if honest | `EdwardsShare.onCurve_eval`, `EdwardsHinted.entries_sound`, `compiled_correct` (:433) (programs only) |
| `hinted_points.h:127`, `:136` | w (uniform, or **zero when u = 0**); the masked point Z | mask point | none (NEEDS_REVIEW 3b) |
| `hinted_points.h:186` | **validity of a lifted point: is the contact's key a curve point** | — | none |
| `hinted_points.h:168` | masked denominators | uniform | none |
| `service_kernels.h:122` | `xeddsa-recover` of the PUBLIC server key (without `TLS_WORKER_HINTED`) | public input | `EstablishField.recover_correct` |
| `tls_kernels.h:273` `reveal_range` | slice of the public-marked `bytes` | — | B.4 |
| `tls_kernels.h:304-307` `test_echo` (TEST producer only) | length; echo ⊕ sent | — | — |

### B.3 Facts revealed by control flow

- **Refusals.** A reply `{0}` from ops 37, 41, 50, 51, 60, 61 and 63, produced by `Rejected`,
  `KernelRefused` or a gated status. Which kernel was loaded next is public anyway: it is chosen
  from the opened shapes.
- **`contactsPrepare` statuses** (255 / 0 / 1; `service_kernels.h:163-177`).
- **Op 17's `[0]`:** the leader's socket closed.
- **Provisional ids** (controller 1752-1811). Both nodes count opened messages; a refused signup
  shows which provisional id was refused.
- **Timing** of every operation, and the size of each opened ciphertext.

### B.4 The reveal budget for server bytes

**What the worker does.** It reveals any range of a received buffer that both controllers
request (`tls_kernels.h:259-276`). The kernel marks the whole content public.

**Where the policy lives.** In both controllers, which must issue identical requests:
- `PublicReceive.mayReveal` (441-442);
- `budget` (482-494), `replyBudget` (415-436), `fieldMissing` (446-462);
- `scan` (213-240), `replyScan` (323-349), `envelopeScan` (259-288);
- `step` (498-581), which throws "a request body byte was revealed" (507);
- `record`, which checks that what is left of a step stays within budget (1908-1925).

**What is passed over.**
- Bodies of server requests and of responses: `stepSkipped`, `stepPassed`.
- A delivered envelope's sealed content goes to the engines unopened (op 48).
- The 200 body of a prekey fetch goes the same way (op 57).
- Exception: `openBody` reveals response bodies. It is set only on the ceremony branch (3174).

**No theorem covers any of this.** PRODUCT_TODO section 10 lists it as open.

---

## C. Theorem index

**Counts.** Method: `rg -c '^\s*(private |protected )?theorem '`; the repository has no `lemma`
declarations.

| Location | Theorems |
|---|---|
| `TlsMpc/` total | 2,526 |
| — `TlsMpc/Signal/` | 1,436 |
| — `TlsMpc/` outside `Signal/` (Sharing/ is 34 of these) | 1,090 |
| `handshake_backend/EmpHybridWork/*.lean` | 18 |
| other `handshake_backend` | 8 |

Of the names, 61 % in `Signal/` and 35 % elsewhere contain `_map` or `length`.

**The pattern.** Each algorithm is written once over an "ops" record:
- the `symbolic` instance builds circuit expressions;
- the `concrete` instance runs on values;
- `*_map` / `*_refines` theorems prove the two agree.

The "spec" is usually the concrete function: the repository's own transcription of the
standard, not an independent statement. No theorem checks a spec against official test vectors.

**Running status:**
- **K:** about a term lowered into a kernel or field program that a deployment uses.
- **C:** about a function the controller executes, directly or through a variant proved equal.
- **M:** a model, or code not on the running path.
- **[R] / [N]:** statement read / name and line only.

**Deployed set** (CircuitInventory.lean, `scripts/produce_circuits.py`). There are no named
profiles: a deployment JSON plus `profile` = legacy|libsignal.
- `real_signal/deployment-production.json`: libsignal, certificate 134, handshake 1122, typed
  records, two send classes, devices, bundle items, signups.
- `local_signal_server/deployment-compact.json`: libsignal, certificate 138, handshake 621, no
  devices.

Production lists:
- tls-derive, tls-verify-finished, tls-update, tls-parser-initial, ws-initial;
- gcm-key-share, gcm-multiply, gcm-tag, gcm-check;
- contact-key, contact-seal, contact-open;
- tls-finish, tls-seal-ctr (KeyUpdate, close), tls-open-handshake 1122, tls-open-application-class,
  tls-reveal-masked, tls-seal-class, tls-open-typed, tls-frame;
- signal-upgrade(-shared), signal-conversation-view, signal-widths, **signal-seal-official**,
  bundle-seal;
- establish-challenges, establish-verified, establish-points, establish-session;
- bundle-rebind, bundle-shape, bundle-item;
- kem-ntt, kem-v, kem-hash, kem-finish, kem-matrix 0-3, kem-u 0-3;
- the 13 receive-* kernels;
- signal-request-ctr, bundle-fetch-ctr, bundle-request-ctr.

The ceremony kernels are listed only with `ceremony=1`, which no deployment sets.

**Loaded but not in any manifest:** the field programs and `swap-bits` emitted by
`EmitWordMask` (x25519-fast, edwards-*, xeddsa-*, receive-torsion, lift-*, field-mask-pair, …).
The C++ pins them by compile-time hashes. The kernel `kem-*` go through `flat_kernel_emitter`
(EmitFlatKernel.lean:81-83), not `EmitKemKernel`.

### C.1 Circuit lowering

**Proved:**
- `FlatLowering.lower_sound` (FlatLowering.lean:1021) [R]: if `lower` returns a gate list, it is
  well formed and every output wire evaluates to its graph node, for every input. Hypotheses: a
  DAG; input wires agree with the assignment. **K** (generic).
- `lower_correct` (:1053), against `AIG.denote` [R]. **K**.
- `lowerExpr_correct` (:1074) [R]: flat output k = bit `sel[k]` of `expr.eval`, given matching
  input wire offsets. **K**. `EmitFlatKernel.lean:64` and `EmitCeremonyKernel.lean:50` call exactly
  `lowerExpr (joinExpr bytes)`.
- `Flat.run_eq_eval` (:569) [R]: the loader's one-pass evaluation equals `Flat.eval` for
  well-formed lists. **K**.
- `ByteCircuit.joinExpr_correct` (ByteCircuit.lean:28). **K** glue.
- `HybridKernel.compiled_correct` (HybridKernelsProofs:27) [R]: every exported AIG output bit of
  a kernel equals the Lean definition. Per-family wrappers: ReceiveProofs:39, EstablishProofs:38,
  BundleProofs:63, CeremonyProofs:122, MlKemFastProofs:599. **K** (the AIG path).
- `BoolDag.compile_correct` (:166), `FieldDag.compile_correct` (:164),
  `FieldDag.compileAll_correct` (FieldDagMulti.lean:42) [R]: an accepted compilation evaluates to
  the expression. **K**: `EmitWordMask.lean:67/78/91` call these.

**Proved since the emitter batch (EMITTER_BATCH.md; Security.lean section 1b):** the printer
`Flat.print` (`printWith_render`, `parseFlat_render`, `lowerExpr_loaded`, FlatLowering.lean) and
the layout text with the **open/private marks** (`TlsMpc/FlatKernelLayout.lean`:
`parseLayout_layoutText`, `openCode_spec`, `lowerKernel_loaded`), for the four kernel emitters,
which now share `layoutText` / `lowerKernel`. Trusted instead: that the C++/Rust loaders parse the
files as `parseFlat` / `parseLayout` do.

**Not proved:**
- `EmitWordMask`'s `render` / `renderField` (EmitWordMask.lean:15-16);
- which flat outputs form which named field (`selection`);
- termination of `lower`;
- that `ShareCommon.shareCommon'`, used by the translation validators, is correct (it is trusted
  at run time, FlatLowering.lean:44).

**No theorem composes** `lowerExpr_correct`, `joinExpr_correct` and a kernel `_spec` into "the
loaded flat file computes the spec".

**Models:** `Padding.pad_original_outputs` (PaddingSemantics.lean:148), and `Artifact.*` /
`Boolean.*` (prototype). **M**.

### C.2 Kernels compute the specified function

**Primitives (function level; reach kernels through `compiled_correct`).**
- `Aes.compiled_encryptCore_correct` (Aes.lean:228) [N];
- `AesSbox.packed_correct` (:310, `decide +kernel`) [N];
- `Sha256.hash_refines` / `hmac_refines` (:292/:296) [N];
- `TlsKdfPrepared.handshakeSecretsFast_correct` (:80), `applicationSecretsFast_correct` (:67),
  `expandLabelFast_correct` (:50) [N];
- `Gcm.compiled_sealCore_correct` (:204) [N];
- `TlsReceive.openCore_correct` (:116) [N];
- `TlsHandshake.verifyHash_value` (:115) [R];
- `EstablishField.recover_correct` / `check_correct` (:31/:36) [R]. These are formulas only,
  "not proved to be the group law".
- `EdwardsHinted.entries_sound` (:192) [N] and `compiled_correct` (:433) [N];
- `WordMask.intoField_val` (:351) and `modAddCircuit_val` (:361) [R]. Both require inputs < p.
- **`X25519Fast.compiled_correct` (:229) [R]:** the emitted `x25519-fast` program outputs (x, z)
  with RFC 7748's result = x·z⁻¹. The division happens in C++. **K**.
- **`X25519.compiled_compute_correct` (X25519.lean:203) [R]:** about `FieldDag.compile X25519.expr`.
  Only the `emit_mpc` executable compiles that (Main.lean:96). **The worker loads `x25519-fast`
  instead.** **M**.

**In `Signal/`** [N]:
- `Pqxdh.deriveCore_specification` (:62);
- `Symmetric.deriveFast_correct` (:71);
- `DhRatchet.materialFast_correct` (:26);
- `SpqrChain.materialFast_correct` (:31);
- `Establish.keys_specification` (:398);
- `XEdDsaScalar.reduce_bytes_spec` (:88);
- `MessageMac.verifyMask_value` (:61);
- `XEdDsa.scalarMask_spec` (:68).

**Kernel-level `_spec`** (the kernel's outputs under every assignment equal the spec). All are
**K** and [R] unless marked:

| Kernel | Theorem(s) |
|---|---|
| `tls-update` | `HybridKernelsProofs.tlsUpdate_spec` :44 (the only TLS key-schedule kernel with one) |
| `tls-seal-ctr` | `tlsSealCtr_spec` (SealCtrProofs:58) |
| `gcm-tag`, `gcm-check` | `gcmTag_spec` :82, `gcmCheck_spec` :96 (iff in value form) |
| `gcm-key-share`, `gcm-multiply` | `gcmKeyShare_spec`, `gcmMultiply_spec` (GcmShareKernelsProofs:40, :54) |
| `contact-key` | `contactKey_spec` :189, **given both shares < 2^255−19** (:190-191) |
| `contact-seal`, `contact-open` | `contactSeal_spec` :217, `contactOpen_spec` :253 |
| class kernels | `open_padded` (RecordClassProofs:490, given a record followed by zeros); `sealCiphertext_padded` (:580) |
| `tls-open-application-class` | `TypedOpenKernel.class_fields` (TypedOpenProofs:247) |
| `tls-open-typed` + `tls-frame` | `typed_pair_refines` (:284), `frame_fields` (:265) |
| `kem-*` | `kemHash_spec` … (MlKemFastProofs:607-664). `kemSample_spec` is about a kernel not deployed. **The composition into `MlKem.encapsulate` is not proved** (header 35-48) |
| `receive-*` (13) | ReceiveProofs `*_spec` (:53-183). The "spec" is the same `ReceiveFirst` definition on concrete ops; the header says "Nothing here is a security statement" (:14-18, :28-32). The only independent formula is `keys_specification` (:276) |
| `establish-*` | `establishChallenges_spec` (:57), `establishVerified_spec` (:72), `establishSession_spec` (:83) |
| `bundle-shape`, `bundle-rebind`, `bundle-seal` | `bundleShape_spec` :73, `bundleRebind_spec` :102, `bundleSeal_spec` :112 (against `Establish.sealMessage`; its value, 2026-11-12: `KernelSpecs/EstablishSealValue.lean` `sealMessage_value`, `bundleSeal_value`, `bundleSeal_accepted`, against `Reference` transcriptions of libsignal's PreKey message and sealed sender v1) |
| `ceremony-secrets` | `ceremonySecrets_spec` (:130) |
| `ceremony-register-ctr` | `registerPlaintext_spec` (:140, plaintext only) |

**About kernels not deployed:**
- `bundleDevice_spec` (:79), `bundleBind_spec` (:92), `bind_rejects` (:141): `bundle-device`
  and `bundle-bind` were replaced by `bundle-item` and `bundle-rebind`;
- `establishSeal_spec` (:125);
- the `TlsPrivateSeal` theorems (`tls-seal-private-ctr`).

All **M**.

**Update 2026-11-12:** every kernel in the list below now has a kernel-level spec in
`TlsMpc/KernelSpecs/` (restated in `TlsMpc/Security.lean` section 2c). Most are stated against
the kernel's own composition on concrete values; only the four TLS handshake kernels are stated
against the RFC transcriptions. Still open (Security.lean section 8): `bundle-item` against
`BundleResponse.device` on the whole body, the meaning of the `signal-widths` flags, the slot
encoders against their RFCs, and value theorems for `boundSeal`/`prepare`.

**Update 2026-11-12 (later):** closed in `TlsMpc/Security.lean` section 2d: the three request
sealers composed with the frames the controller builds (`*_built`: slots zero and non-overlapping,
8-byte header proved for every frame `build` returns, the opened ciphertext encrypts exactly the
masked frame of the filled request; stated in `KernelSpecs/RequestFrame.lean` about the
controller's own builders, which stage S2 moved to `TlsMpc/Node/Policy/Request.lean`; the earlier
restated copy and its bridge are gone); `bundle-item` against
`device` on the whole body (`bundleItem_whole`, locality lemma `bundleDevice_local`); the
`signal-widths` flags (`signalWidths_value`); the UUID, base64 and padded-decimal slot encoders
against independent references with round trips. Still open: `bundle-slot`'s spliced item against
`device` on the original, and `boundSeal`/`prepare`.

**Deployed kernels that had no kernel-level spec when this map was written:**
- tls-derive, tls-verify-finished, tls-open-handshake, tls-finish;
- ws-initial, tls-parser-initial;
- tls-reveal-masked (mask only);
- establish-points, bundle-item. `bundle-item` calls `BundleResponse.device` on a reassembled
  body (BundleItemKernels.lean:49-51); no theorem links them.
- **signal-request-ctr, bundle-request-ctr, bundle-fetch-ctr** (BundleProofs.lean:52-53 says so);
- signal-upgrade(-shared). Function level only: `RelayUpgrade.request_map` (:50),
  `compiled_request_correct` (:55) [N].
- signal-conversation-view, signal-widths;
- **signal-seal-official / -built.** HybridKernels.lean:454-461 recomposes
  `SpqrSend.acceptedMask`, `SpqrSend.prepare`, `SealedSenderV1.boundSeal` and
  `ChainSend.selectState`, gated twice by `TlsProviderGate.gate` (:458) [R].
  - `sealCore_concrete_correct` and `reject_preserves_*` (SpqrSend:211/:230, ChainSend:199/:214,
    Send:72) are about the sibling `sealCore`, which the kernel never calls.
  - `SealedSenderV1.boundSeal_map` (:139) is generic over `Sha256.Hom`, and
    `Sha256Ripple.evaluationHom` (Sha256Ripple.lean:128) bridges it to the kernel's instance.
    What is missing is any value theorem for `boundSeal` and any composition.

### C.3 Reveal and open gating

- `TypedOpenProofs.tlsOpenTyped_gated` (:231) [R]: for every input assignment with
  `accepted` = 0, the kernel's opened fields evaluate to `[[0],[0,0]]`. **K**. The only theorem
  that quantifies over a kernel's opened-field flags.
  - Companions: `rejected_parse` (:106), `rejected_independent` (:144), `gating` (:190),
    `handshakeBit_cases` (:68), `rejected_parse_length` (:127).
- `HybridKernelsProofs.tlsOpenApplication_event_private` (:106) and
  `TlsPostHandshake.application_event_independent` (:230) [R]: on an authenticated application
  record, the opened event does not depend on the content. **K** (through `class_fields` /
  `frame_fields`). Also `process_application_event_independent` (:242),
  `reject_unauthenticated` (:208), `reject_failed` (:219).
- `TlsPublicHandshake.gate_value` (:26), `application_not_released` (:42) [N]. Function level,
  under `tls-open-handshake`.
- `TlsReceive.bad_header_zero` (:141), `bad_tag_zero` (:149) [N]. They concern `openCore`, used by
  the exact-size `tls-open-application`, which is not deployed. **Indirect** (the deployed kernels
  use `RecordClass.openParsed`, covered by `rejected_parse`).
- **"Status 0 ⇒ every output zero"**, spec level, reaching kernels through `_spec`:
  - `ReceiveProofs.*_rejects` (:195-262), but none for `receive-text`, `-certificate`,
    `-certificate-verified`, `-access-key` or the three `-shape` kernels;
  - `BundleProofs.rebind_rejects`;
  - `EstablishKernel.establish_rejects` (:100);
  - `MlKemFast.finish_rejects` (:553);
  - `contactOpen_rejected` (:286);
  - `OpenResult.finish_reject_auth` (:98), `finish_reject_padding` (:106).
- **The accept direction** exists for a few:
  - `contactOpen_accepted_iff` (:275);
  - `gcmCheck_spec` (iff);
  - `MlKemFast.finish_accepts` (:565);
  - `verifyHash_value`;
  - `SpqrSend` / `ChainSend.acceptedMask_value`;
  - `MessageMac.verifyMask_value` (function level).

  **Not proved:** that `receive-session` status 255 implies the MAC verified, or that
  `receive-certificate-verified` implies the signature verified.
- `BundleKernel.structural_value` (BundleProofs:171) [R]: the opened shape flag is 255 exactly on
  punctuation. **K**. Also `shape_length` (:246), `BundleItemKernel.shape_padded` (:79).
- **Models (M):**
  - `GhashShares.accept_unique_pad` (:108), `genuine_rejected` (:131), `honest_accepts` (:144),
    `share_hides` (:81), `halves_are_ghash` (:274). These model `gcm_shares.h`.
  - `GcmShareKernelsProofs.shared_halves_are_ghash_proved` (:258) and `scheduled_halves_are_ghash`
    discharge the halves hypothesis of `sealCtr_with_tag_is_seal` for a modelled schedule, not
    for the C++.
  - `MaskedAgreement.*`, `OffsetAgreement.*` (`public_key_independent` :69,
    `candidate_needs_initial` :74), `ConversionSemantics.*` ("not a circuit or security proof"),
    `Sharing/*`.
- `Ceremony.masked_hides` (CeremonyProofs:102) [R]: a per-byte one-time-pad bijection. **K**
  (ceremony only).

### C.4 Controller side (code the controller executes)

**With a theorem:**
- `PublicReceive.fast_eq` (controller :95, with :68, :73, :77): `fast = ByteAuth.concrete`. **C**.
  These four are the controller's only theorems.
- `Word64.fast_eq` (Word64Fast.lean:71). **C**.
- `VarintDecode.Spqr.decodeCore_spec` (:179). **C** (the response parser, 538 and 595).
- The parsers are proved only symbolic = concrete (TlsWebSocketUpgrade, TlsWebSocketFrame,
  TlsWebSocketControl, TlsChatResponse). Since 2026-11-12 the frame parser, the control queue, the
  TLS record splitter and the upgrade's accept value also have RFC references
  (`TlsMpc/KernelSpecs/ParseWebSocketFrame.lean`, `ParseWebSocketControl.lean`,
  `ParseTlsRecord.lean`, `TlsMpc/Node/Local/WebSocketAccept.lean`; `TlsMpc/Security.lean` section
  4c). **Nothing relates `TlsChatResponse` or the upgrade response parser to RFC 6455 or HTTP.**
- `PrivateTextNotification.buildPublic_spec` (:247), `buildPublicOfficial_spec` (:390),
  `buildPublic_short` (:404), `firstFit_spec` (:226) [R]. **C** (used at 2021 and 2314).
- `BundleProofs.layout?_sound` (:252). **C** (2159, 2651).
- `TlsClient.accepted_session_authenticated` (TlsClient.lean:246): a structure projection.
  **C**, weak.
- `TlsApplicationPolicy`: `application_reservation` :82, `consecutive_application_distinct` :95,
  `update_uses_old_epoch` :102, `pending_blocks_application` :130, `aborted_blocks` :137,
  `receive_reservation` :142 [N]. **C**: TlsApplication.lean:58-149 calls the reservations.

**No theorem about:**
- `PublicReceive.scan`, `replyScan`, `envelopeScan`, `envelopeAdvance`, `budget`,
  `replyBudget`, `fieldMissing`, `mayReveal`, `step`, `stepPassed`, `stepSkipped`, `replies`;
- `PublicRequest.build`, `buildDevices`, `buildFetch`, `assemble`, `officialJson`,
  `clientFrame`;
- `RelayUpgrade.anonymousRequest` (:39). Its two theorems are about `request`.
- `Recovery.*` (a runtime self-test, `checks` :1006, is not a theorem);
- `Circuits.*`;
- `CeremonyRequests.*`;
- the provisional ids.

### C.5 State and ratchet

- `ChainSend.selectState_accept` / `_reject` (:176/:165), `acceptedMask_value` (:157);
  `SpqrSend.acceptedMask_value` (:179), `prepare_concrete_correct` (:200). Function level: the
  same functions the seal kernel calls, bridged by `_map` + `Sha256Ripple.evaluationHom`, never
  composed. **K-adjacent.**
- `ReceiveAdvance.*`, `SkippedKeys.*`, `ReceiverStore.*`, `SpqrEpoch.*`,
  `PreKeyValidation.finish_spec`: meaningful specs, but **M** (the deployment does not use them).

### C.6 Axioms and escape hatches

Searched: `TlsMpc/`, all of `handshake_backend/`, the root `.lean` files.

| Pattern | Code occurrences | Notes |
|---|---|---|
| `sorry`, `native_decide`, `axiom` (declaration), `unsafe`, `implemented_by`, `extern`, `opaque`, `ofReduceBool`, `csimp` | **none** | only in comments (e.g. MlKemFastProofs:8, FlatLowering:46) |
| `admit` | none as a tactic | a def name (TlsChatResponseMux.lean:90); strings in EmitMux.lean |
| `bv_decide` | **5** | TlsWebSocketActivity.lean:8, :11 (behind `activity_valid` → `run_correct`, `RecordClassProofs.within_value` → `openParsed_padded`, `sealCiphertext_padded`); TlsPrivateSeal.lean:113, :116, :176 (not deployed) |
| `partial def` | 2 | CircuitInventory.lean:71 (tooling); `handshake_backend/WebSocketWork/MuxFixture.lean:9` (not built) |
| `decide +kernel` | 47 | 23 outside `Signal/`, 24 in it; kernel reduction, adds no axiom |
| `#print axioms` | 203 lines in 38 files | No recorded output exists for deployed-path theorems. Untracked benchmark logs (`benchmarks/results/raw/websocket-activity/proof.log`, `…/tls-private-seal/proof.log`) show `[propext, Classical.choice, Quot.sound]` for the `bv_decide` theorems, without `Lean.ofReduceBool`. Unconfirmed without a build |

**Trusted for everything:**
- the Lean compiler and runtime, which run the controller;
- `ShareCommon.shareCommon'`;
- the field-program printer (`EmitWordMask`) and the loaders' parsing of the `.flat` / `.layout`
  text (the flat and layout printers are proved since the emitter batch, C.1).

---

## D. Gaps, stated bluntly

1. **No end-to-end statement, for any channel, of the form "everything this node sends to X is a
   function of public values and the listed openings."**
   - The pieces that exist are local: kernel specs, one gating theorem, parser refinements.
   - The channels they would feed live in one 2,160-line `do` block. It has four theorems, all
     about byte operations, and uses `Bytes` for public and secret data alike.

2. **The server-byte reveal policy is unproved and enforced only in the controller** (B.4).
   - The worker opens any range both controllers ask for.
   - A bug shared by both controllers in `budget`, `scan` or `replyScan` reveals request or
     response bodies: sender-identifying envelopes, prekey bundles, 409 device lists.
   - A single malicious node cannot cause this alone: the honest controller would not issue the
     same request.

3. **No kernel is proved as a whole down to the file the worker loads.**
   - The field selection and the field-program printer are outside Lean (C.1); the flat printer
     and the layout text with the open marks are proved since the emitter batch
     (`FlatKernelLayout.lowerKernel_loaded`).
   - The open marks are the security boundary of B.1. No theorem covers them except
     `tlsOpenTyped_gated`, for one kernel.

4. **What goes to the Signal server has no value theorem on the send path.**
   - The seal kernels `signal-seal-official` and `-built` have none.
   - The slot sealers `signal-request-ctr`, `bundle-request-ctr` and `bundle-fetch-ctr` have
     none.
   - The request templates (`PublicRequest.*`) have none. Their agreement with libsignal is
     tested, not proved.

5. **The whole C++ sequencing is unverified.** That is:
   - `service_kernels.h` (969 lines) and `tls_kernels.h` (311);
   - the conversions (`dyn_word_mask.h`, cut-and-choose included);
   - the masked inversions, split ECDH, the offset agreement, the hinted programs;
   - the GHASH share arithmetic (`gcm_shares.h`, modelled in GhashShares.lean, not extracted);
   - the field-program evaluator's division openings.

   This is where B.2's openings happen, none through the layout check. Their hiding arguments
   are comments; the cut-and-choose is "not modelled".

6. **Trusted and unverified:**
   - EMP ag2pc (validated-v3 patch, triple stock) and the MP-SPDZ-based field engine, including
     MAC checks and OT;
   - the C++ worker shell: pipe, agreement, sockets, SOCKS, record forwarding, connection table,
     the loaders, the field-program evaluator;
   - local public arithmetic through libsodium and OpenSSL bignums (`LocalCurve`, `LocalField`,
     `Ed`);
   - `public_auth` (OpenSSL X.509);
   - the Rust daemon;
   - `handoff_client` and the database nodes;
   - the KEM decapsulation tool and the key tool (`lss-provision`, a test tool);
   - the Python circuit cache (non-strict mode only) and `produce_circuits.py`;
   - the Lean compiler and runtime.

7. **Secret material held directly by the controller** (the types do not mark it):
   - (a) each contact's additive key share: from the database read (`dbShare`, 1566), from
     `dbDeal` (1578-1597), from `freshShare` (1432-1435), or from TEST store files. It is passed to
     op 36 at 1684, 1694, 1709, 1716, 1816, 1824, 2186, 2193, 2268, 2279.
   - (b) the account key share (1635, 1727-1728).
   - (c) this party's XOR share of the account credentials, as a hex `String`:
     - read from the environment (1332-1335) and from `credentials.share` (1263);
     - put into a child process's environment (1267, 1272);
     - sent to op 47 (1605, 1723).
   - (d) the ceremony's password and recovery-password shares (op 80 reply, 3246-3249,
     3284-3285), written to disk.
   - (e) OWN keys:
     - the identity private key (TEST export → op 46, 1642);
     - prekey private keys (export → op 51, 1788);
     - the Kyber private key, put on a subprocess argv (1760);
     - the decapsulated Kyber secret (→ op 51).
   - (f) TEST contact records in the clear (export → op 44: 1693, 1715, 2278).
   - (g) `keys.json`, private keys included, sent whole to the peer through op 39 (3165;
     allowed by the owner's policy, CEREMONY.md section 4).

   Everything else the controller holds is a public value or a handle.

8. **Secret material held by the daemon and the worker.**
   - Daemon: the peer HMAC key (read in the clear at node-daemon.rs:131-135) and the path of the
     database client key.
   - Worker: every engine share; the TEST admissions' private keys; its own random
     contributions (PRG).

9. **Unauthenticated or unencrypted links.**
   - The Boolean-engine link carries the worker's own messages (A.2 (a)-(d)). It is plain TCP;
     the deployment relies on WireGuard.
   - The daemons' link has a MAC but no encryption and no replay cache, and **its replies are
     not authenticated**. A replayed `peer-serve`, `peer-receive` or `peer-ended` within 60 s
     kills a session.
   - The application's link is plaintext. `wait`, `events` and `status` have no authentication.

10. **Revealed by design but worth a reviewer's eye:**
    - the sender's certificate length, phone-number presence and length (op 50);
    - counter widths per contact (op 41);
    - the identity-key-changed byte (op 60);
    - whether a contact's key is a curve point (`hinted_points.h:186`);
    - u = 0 (`:127`);
    - the received message text (the signup token);
    - the hostname, to the leader's DNS resolver in direct mode.

11. **Settings that must match on both nodes but are not checked up front:**
    `SIGNAL_ACK_REFUSED`, `SIGNAL_RECOVERY`, `SIGNAL_CLIENT_PROFILE`, `SIGNAL_PREPARE_BATCH`.
    - A mismatch shows only at the first request that differs, which ends the session.
    - Separately, **`agreedClock` (2112-2114) takes the later of the two clocks without the
      two-minute check** that `agreedNow` (1486) and `serve` (2995) apply. A peer can push the
      session's back-off and keepalive clock arbitrarily far: a liveness and timing lever, not a
      privacy one.

12. **TEST hooks on production paths:**
    - `SIGNAL_LOCAL_PAUSE_*`, `SIGNAL_LOCAL_TIMESTAMP`;
    - the TEST admission ops 44 and 46;
    - the `EMP_HYBRID_TEST_FAULTS` field-engine hook compiled into the worker (A.7);
    - the `signal-seal-probe` kernel (opens chain keys), findable by name outside strict mode.

13. **Duplicated security-relevant logic in C++ with no Lean counterpart:**
    - three hand-written commit-then-open exchanges with three different framings (`joint_random`
      without party or nonce; `split_ecdh` and the K₀ exchange with both);
    - the WebSocket accept value (SHA-1 and base64, `service_kernels.h:407-410`, `:480-482`).

14. **Formerly D.12 (signal-seal-official missing from the inventory) is resolved:**
    CircuitInventory.lean:119-137 lists it under `profile=libsignal`, which both deployment files
    set.

**What an end-to-end statement would take** (laid out in `REORGANIZATION_PLAN.md`):
- every external I/O of the controller behind one typed module, with secrets in types the
  messages cannot hold;
- the C++ sequencing and conversion protocols as Lean scripts over a small engine instruction
  set, so that every opening is a Lean call with a theorem;
- the remaining shell in Rust, the engines behind a C ABI, and per-channel theorems collected in
  `TlsMpc/Security.lean`.
