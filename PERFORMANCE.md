# Where the time goes

Measured 2026-11-11 on one machine (12 cores; both computation nodes, the five database test
nodes and the local Signal-Server on localhost), with
`local_signal_server/check_signal_service_local.py MODE --runs 0 --db --broadcasts 6` and
`scripts/session_profile.py`. A real deployment adds network latency between the two nodes, which
these numbers do not contain (see "Rounds").

"Before" is the tree at the start of the performance work (commit 301dba6 with the controller
fixes described at the end); "after" is with the changes listed under "What changed". The
controllers were being changed by other work during the day, so the time outside the workers is
not comparable between runs to the tenth of a second; the workers' own categories are.

## Headline

| Malicious mode (statistical 128) | Before | After |
|---|---|---|
| Steady state, one message to a prepared contact (send to send) | 2.42 s | 0.97 s |
| A contact's first send, more than a later one | 2.1 s | about 0.5 s |
| A new contact's first message received (the record that carries it and the two receive operations) | 24.8 s | 5.9 s |
| Fixed cost of a session before the first send (3.3 s of it the local server answering the upgrade) | 11.5 s | 6.8 s |
| Worker time of a 12-send session | 62 s | 24 s |
| Worker time of a session that receives one first message | 36 s | 11.7 s |

| Semi-honest mode | Before | After |
|---|---|---|
| Steady state, one message (send to send) | 0.45 s | 0.36 s |
| A new contact's first message received | 3.1 s | 1.9 s |
| Worker time of a 12-send session | 12.9 s | 10.4 s |
| Worker time of a session that receives one first message | 7.2 s | 4.8 s |

Semi-honest mode was not profiled at the start of this work. Its "before" column is a run taken after the field stock and the first loader change but before the cached-kernel lookup and the framing circuit, so it understates the gain; the earlier figure was about 20 s for a 4-send session. The Boolean engine there is plain garbling with nothing to prepare, and its field triples are cheap (1.3 s per send session with the stock off), so what helps is the loader (2.7–3.6 s → 1.3–1.5 s per process), the framing circuit and the shared rounds. Its workers are busy about 0.11 s per message; the rest of the 0.36 s is the server and the controllers.

In steady state the malicious workers are now busy about 0.5 s per message; the rest is the
local server answering (0.26 s) and the controllers.

## One broadcast session: 2 contacts, 6 messages each (12 sends), malicious

| Where (worker time) | Stocks off | Stocks on | Notes |
|---|---|---|---|
| Boolean circuits: the part that needs the circuit | 8.0 s | 9.7 s | 39.1M AND gates, 0.20–0.25 s per million |
| Boolean triples made inside circuit runs | 22.3 s | 0 | made ahead by background pools; circuits waited 0.2 s for them |
| Field triples made when a round ran out | 10.3 s | 0 | made ahead; rounds waited 0.4 s |
| Field rounds and local field work | 1.6 s | 2.8 s | slower beside the generators on a shared machine |
| Loading circuits | 1.7 s | 2.1 s | once per worker process; 10.6 s at the start of this work |
| Conversion masks | 0.4 s | 0.7 s | |
| Everything else in the workers | 0.4 s | 0.9 s | |
| Waiting for the controller, the server, the database client | 5.9 s | 6.9 s | |
| **Session** | **50.6 s** | **23.8 s** | 62.1 s at the start of this work |

Both columns are today's tree; "stocks off" is `TLS_WORKER_TRIPLE_STOCK=0 TLS_WORKER_FIELD_STOCK=0`,
which is how the engines worked before. It gives the split of the Boolean engine that had not
been measured: of 0.77 s per million AND gates, 0.57 s (74%) is making the AND triples, which
does not depend on the circuit, and 0.20 s is the circuit itself (wire masks, the authenticated
Beaver openings, garbling, evaluation, the output checks).

### What each thing costs, by how often it is paid

**Once per worker process (was about 11 s, now about 3 s):**
- Start-up of both engines, their background pools and the first conversion masks: 0.6 s.
- Loading circuits: 2.1 s for a send session (28 kernels), about half of it the 100 MB send
  circuit. Was 10.6 s.
- Stocks start empty and fill while the handshake runs.

**Once per connection:**
- TLS handshake: 2.6 s (was 5.7 s), 3.1M AND gates.
- WebSocket upgrade: 3.3 s of waiting for the local server's answer (not ours), 0.6 s of work.

**Once per contact per session (was about 2.1 s more than a later send, now about 0.5 s):**
- About 14,000 field products (the long-term agreement, 2,800; the curve table, 11,150) in about
  2,800 sequential field rounds. The triples now come from stock; what is left is the rounds
  themselves and their local work.
- Loading its key and state from the database nodes: 0.05 s in the workers.

**Per message (steady state):**

| Step | Before | After | Notes |
|---|---|---|---|
| Sealed-sender send circuit | 1.48 s | 0.45 s | 2.18M AND |
| Field work for the ephemeral key | 0.2 s | 0.05 s | 638 products, 31 rounds |
| Request frame and sealing its record | 0.26 s | 0.09 s | 0.31M + 0.07M AND |
| Opening the response record | 0.18 s | 0.04 s | 0.13M AND (was 0.20M) |
| Storing the contact's state | 0.10 s | 0.03 s | 0.09M AND |
| Waiting for the server's response | 0.26 s | 0.26 s | local server |
| Controllers (reveal steps, parsing, building the request) | 0.1–0.2 s | 0.1–0.3 s | varies with other work in progress |
| **Send to send** | **2.42 s** | **0.97 s** | |

A message needs about 2.9M AND triples and 640 field triples. On this machine two background
pools make about 2.5M AND triples per second while the circuits run beside them, so in a long
broadcast with no pauses the pools, not the circuits, set the pace (about 1.2 s per message with
two pools; the waits for the server and the controllers are when they catch up). On separate
machines each node has its cores to itself; `TLS_WORKER_TRIPLE_STOCK=3` or `4` adds pools.
A sustained run is now measured: "The long-lived send session" below (there the database
writes before each send, not the pools, set the pace).

## Receiving one new contact's first message, malicious

| Where (worker time) | Before | After |
|---|---|---|
| Loading circuits | 12.4 s | 2.7 s |
| Boolean circuits | 11.7 s (15.1M AND) | 3.4 s (14.5M AND) |
| Field triples being generated, or waited for | 7.5 s | 1.1 s of waiting |
| Field rounds | 0.9 s | 1.0 s |
| *of the above:* opening the 2.7 KB record that carries the envelope | 5.7 s | 1.1 s |
| *of the above:* unseal, certificate, prekey part | 10.3 s | 2.5 s |
| *of the above:* agreements, session, text | 8.8 s | 2.3 s |
| **Session** | **36.2 s** | **11.7 s** |

The record that carries the envelope was 4.12M AND gates for 2.7 KB: 1,500 per byte, of which
only about 290 are AES-GCM. The rest was the post-handshake framing, a state machine with a
64-bit counter run over every content byte in case the record is a handshake message. It is now
2.53M (see "The framing circuit").

## What changed

| Change | Where | Before | After |
|---|---|---|---|
| AND triples minted ahead of use by background pools of the same session | `dyn_session.h` (`TripleStock`), `prepare_validation_v3.py` (the engine's `mint` / `stock`), `tls_worker_v3.cpp` | 0.77 s per million AND in a circuit run | 0.20–0.25 s per million; send circuit 1.48 s → 0.45 s |
| Field triples generated ahead of use by further protocol instances of the same engine | `field_engine.cpp` (`FieldTripleStock`), `field_engine.h`, `field_program.h` | 10.3 s per send session, 7.5 s per receive | 0.4 s and about 1 s of waiting |
| Circuit files parsed directly from the hashed bytes | `lean_circuit.h` | 10.6 s per send session | 3.5 s |
| Cached kernels found without starting an interpreter | `kernel.h` (`KernelCache::cached`) | 3.5 s (about 90 ms per kernel) | 2.1 s |
| Post-handshake framing as a smaller circuit, proved equal | `TlsMpc/TlsPostHandshakeFast.lean`, `TlsMpc/Signal/Word64Mux.lean`, `HybridKernels.lean` (`tlsOpenApplicationCtr`), `HybridKernelsProofs.lean` | 2.7 KB record 4.12M AND; 153-byte record 0.20M | 2.53M; 0.125M |
| The receive path's seven independent key agreements in the same field rounds | `x25519_fast.h` (`evaluate_many`), `tls_kernels.h` (`agreement_words`), `service_kernels.h` | 7 × 1,017 rounds | 1,017 rounds |
| Response parser's word operations computed directly, proved equal | `TlsMpc/Signal/Word64Fast.lean`, `PublicServiceController.lean` (`Word64.fast` for `Word64.concrete`) | 1.20 ms per byte | 0.74 ms per byte |

### The two stocks

Neither triple generation depends on what is computed, so both run before and beside the work
that uses them. Nothing about the triples changes: the same generation code, checks, bucket
rule and MAC key or Delta; each triple is used once, in order, by the session that made it.

- **Boolean engine.** Since the v3 hardening the engine's triple generation is function
  independent (`TRIPLE_POOL_AUDIT.md`, steps 1–2); only the authenticated Beaver openings touch a
  circuit's masks. Steps 1–2 are now `TriplePool::mint`, moved out of `compute_inplace` without
  change. A factory is a further `TriplePool` of the same session: the same Delta, its own two
  channels (siblings of the session's), its own COT sessions, and a counter range of its own for
  digest tags and hash-tweak seeds. Factories mint batches of 2^19 (bucket size 8 from the batch
  length, the same rule as before; small circuits used to get buckets of 9 to 40). Default: 2
  factories, 4M triples of reserve. `TLS_WORKER_TRIPLE_STOCK=FACTORIES[,BATCH[,RESERVE]]`, `0` for
  the old behaviour.
- **Field engine.** Each generator line is a second `ProtocolSet` of the same engine on its own
  connection, running the library's own triple generator; the multiplication protocol takes its
  triples from the stock instead of its own generator. Default: 2 lines, reserve of 8 batches
  (24,000). `TLS_WORKER_FIELD_STOCK=RESERVE[,LINES]`, `0` for the old behaviour.
- **Staying in step.** Both parties must make the same batches. Batch k is started when
  k × batch < requested + reserve, where `requested` counts what the computation has asked for:
  the same number on both sides, reached at different moments. Each side announces a batch on
  the stock's own channel when its count allows it; the batch starts when both have, and on
  shutdown a side announces the end instead. The stock settings are part of every agreed request,
  so two workers configured differently refuse to work together.
- **Cost.** Memory: about 0.5 GB per party for the Boolean reserve and 1.4 GB for two field
  generator lines (the harness peaked at 12.3 GB against 8.2 GB). Traffic: a full reserve that a
  short session never uses is wasted (about 0.6 GB Boolean, 1.7 GB field). Lower the reserves
  for short sessions over a slow link.
- **Checked.** Every pinned circuit of `check_lean_runs.py` through the fixture with triples from
  two factories, with right and wrong expectations (`EMP_TEST_TRIPLE_STOCK`), and a clean exit
  of both workers with the stocks filling, full, and idle. (The harness never exercises a clean
  exit: its controllers kill their workers.) Not checked: a party that misbehaves inside a
  factory; the checks there are the engine's own, unchanged.

### The framing circuit

`TlsPostHandshake.scan` computed all six cases of its state machine as whole states for every
byte and picked one with six nested selects, each selecting the 64-bit counter with two AND
gates per bit. `TlsPostHandshake.Fast.gatedStep` computes the same next state field by field
(three selects for the counter, one for the message kind), and `Word64.symbolicMux` selects with
one AND per bit. `Fast.core_eq` proves the function on values is `TlsPostHandshake.core`
unchanged, `Fast.core_refines` that the compiled circuit refines it, and
`HybridKernelsProofs.tlsOpenApplicationCtr_parser` states it for the kernel. No theorem was
dropped; `TlsPostHandshake` itself is untouched.

Since then the scan runs only on handshake records (`TlsMpc/TypedOpenKernels.lean`,
`TLS_WORKER_TYPED_OPEN`; what it reveals and what is proved: `NEEDS_REVIEW.md` section 2).
`tls-open-typed` decrypts and parses the record and opens one bit, "authenticated handshake
record"; `tls-frame` scans only when it is set. AND gates, `tls-open-application-class` →
`tls-open-typed`: 2.7 KB record (class 3072) 2.87M → 1.14M; 150-byte record (class 160)
132K → 53K. A handshake record costs both kernels (2.91M; 135K).

## Tried, and not kept or not done

- **The response parser's remaining cost.** With `Word64.fast` it is 0.74 ms per byte; the rest
  is in the byte-mask folds and the 100-entry stack it rewrites per byte. Not pursued.
- **Fewer AND gates in the send circuit.** 2.18M AND is about 60 SHA-256 compressions (23–25
  thousand each, already the one-AND-per-bit adder) and about 60 AES blocks. Every HMAC key and
  HKDF input in it depends on the message's own chain or ephemeral key, so nothing in it is a
  function of the contact alone. No change.
- **A larger field reserve** (48,000) would remove the last second of waiting on the receive
  path at the price of 3.4 GB of traffic per session that may go unused. Left at 24,000.
- **Caching the engine's per-circuit analysis** (liveness and slot assignment, two of the four
  passes over the gate list): inside the engine's pass structure; not attempted.

## Tor circuits (one TLS connection per circuit)

Measured on this tree, malicious mode, localhost, through `scripts/socks5_test_proxy.py` (no Tor:
real circuits add their own latency, unmeasured), with
`check_signal_service_local.py --circuits 1,3` and `scripts/session_profile.py` (its "connections
opened after the first" and "send to send" lines). 4 contacts, 2 broadcasts (8 sends), contacts on
the database nodes.

| | Worker time | AND gates |
|---|---|---|
| Each connection after the first: handshake, upgrade, reading its 101 | 1.2–1.6 s | 3.9–4.5M |
| The first send on each further connection, extra (GHASH key powers under its keys) | about 0.1–0.3 s | 0.4–0.5M |
| One message, steady state, N = 1 | 1.0–1.15 s send to send | 2.72M |
| One message, steady state, N = 3 | 0.96–1.07 s send to send | 2.72M |
| Whole session, N = 1 | 19.0 s | 28.9M |
| Whole session, N = 3 | 20.9 s | 37.7M |

Semi-honest, N = 3 (store, same contacts): 0.44–0.55 s per further connection (3.9–4.2M AND),
0.34 s and 2.63M AND per steady message, 7.3 s of worker time for the session.

Direct (N = 0, 2 contacts × 2 messages in the same run) costs the same per message: the TLS
records and the send circuits are identical, and going through the proxy changes nothing in the
engines. Switching connections is one agreed request (a hash exchange) and no circuit. So N
circuits cost about (N − 1) × (1.5 s, 4.5M AND) more per session, paid before the first send,
and nothing per message. Over real Tor, each connection also waits for its circuit to be built
and every server round trip (the handshake's two, the 101, each response) takes the circuit's
latency instead of localhost's; neither is in these numbers.


## Rounds (measured at a 2 ms round trip)

The two computation nodes will be about 2 ms apart (Helsinki and Tallinn). Everything above was
measured on localhost, where a round costs nothing. This section is measured with latency.

**How.** `scripts/delay_relay.cpp` is a local TCP relay that delays every byte by a fixed time
in each direction (no root). With `TLS_WORKER_TEST_LINK_SHIFT` the connecting worker dials the
relay for every link to the other worker: the Boolean engine's channel and its siblings (the
triple factories), the challenge channel, the field engine's connections and its stock lines.
`check_signal_service_local.py --link-delay-ms 1` runs any stage that way (1 ms each way; a
ping-pong through the relay measures 2.2 ms). The field side alone, without a server or a
Boolean circuit: `rounds_fixture.cpp` through `build_hybrid_v3.py rounds`, which counts
multiplication rounds, openings and input exchanges and runs the earlier and the new programs
on the same shared inputs, comparing the opened results.

**What one exchange costs** (`rounds_fixture calibrate`, 1 ms each way, no other traffic):

| Exchange | Time | In round trips |
|---|---|---|
| One multiplication level of a field program | 2.2 ms | 1 (party 1 sends its shares, party 0 answers with the sums) |
| One opening with its checks (`checked_open`) | 7.6 ms | 3.5 (a MAC check before, the opening, a MAC check after) |
| One input exchange | 2.2 ms | 1 |
| One request agreement or commitment (`Challenge::transfer`) | 2.05 ms | 1 (now one message delay: short transfers cross on the wire) |
| One Boolean circuit run | 4 ms + 2 ms per 30,000 AND gates | 2 + one per 30,000 gates |

While the triple stocks are filling through the same relay, these were 3.1, 10.2 and 3.3 ms.
The check that the relay is honest: the earlier preparation of two contacts is 2,578
multiplication rounds and 970 openings, 1.6 s on localhost and 19.2 s through the relay: 17.6 s
more, where the table predicts 5.7 s for the rounds and 7.4 to 9.9 s for the openings (the
stocks were refilling throughout).

### The field programs: constant depth instead of chains

The curve work was long chains (a square root by a power chain, a table by 256 successive
doublings, a 255-step ladder per agreement, a 509-step signature check, a 253-step
multiplication by the group order). `TlsMpc/EdwardsHinted.lean` computes the same results in a
few dozen levels (how: its header; what it opens and where it differs on malformed keys:
`NEEDS_REVIEW.md` section 3b). It is behind `TLS_WORKER_HINTED=1` (harness: `--hinted`), **off by
default until reviewed**. Field side alone (`rounds_fixture`), malicious mode:

| | Multiplication rounds + openings | Field products | Localhost | 2 ms round trip |
|---|---|---|---|---|
| A contact's table, earlier (`edwards-prepare`), per contact | 1,289 + 485 | 11,150 | 0.82 s | 9.6 s |
| A contact's long-term agreement, earlier (ladder), per contact | 1,017 + 1 | 2,796 | 0.12 s | 2.35 s |
| Tables, new (`lift-open`, `lift-point`, `edwards-prepare-hinted`), per BATCH of any size | 45 + 13 | 11,120 per contact | | 0.6 s + the triples |
| Long-term agreements, new (`edwards-affine-bit-sum`, from the tables), per batch | 20 + 1 | 2,637 per contact | | 0.1 s + the triples |
| — a batch of 4 contacts | 65 + 14 | 55,000 | 4.6 s, of which 4.3 s waiting for triples | 5.5 s, of which 4.5 s waiting for triples |
| — a batch of 100 contacts | 65 + 14 | 1,376,000 | | 175 s, of which 165 s waiting for triples |
| A message's agreement, earlier (`edwards-offset-sum`) | 23 + 8 | 638 | 0.02 s | 0.27 s |
| A message's agreement, new (`edwards-offset-sum-fast`) | 17 + 1 | 608 | 0.04 s | 0.08 s |
| First message received, earlier: server key lift (once per process) | 2,537 + 1 | 2,547 | 0.17 s | 6.1 s |
| — unseal agreements and certificate signature | 4,080 + 2 | 16,790 | 1.3 s | 9.9 s |
| — base key lift, torsion, seven agreements | 4,819 + 2 | 26,418 | 2.0 s | 11.7 s |
| First message received, new: server key lift | 0 (each party evaluates the same Lean program in the clear) | 0 | | |
| — unseal agreements and certificate signature | 111 + 21 | 18,309 | 1.5 s | 1.3 s |
| — base key lift, torsion, seven agreements | 56 + 12 | 27,055 | 1.8 s | 1.6 to 3.1 s (waiting for triples) |
| A stored table loaded (proposal, see below) | 0 | 0 | 0 | 0 |

Semi-honest mode, the same fixture at 2 ms: the field side of a first message received is
25.6 s with the earlier programs and 0.6 s with the new ones (its triples are cheap and its
openings carry no MAC check).

So over the link the field side of a contact's first send goes from 12 s to a share of one
batch, and of a first message received from 22 s (28 s with the server key) to about 3 s. The
new programs use as many triples as the old ones (the certificate signature and the torsion
check far fewer, the agreements about twice as many: a table of `2^i·P` per private point,
2,922 products, and a sum over it, 3,011, against a 2,794-product ladder). What they cost is
therefore triples, and **a batch of 100 unprepared contacts is bound by triple production**:
1.4 million field triples at 8,000 to 13,000 per second on this machine, and 66 KB each way
per triple on the wire: 0.75 GB each way per contact, so 6 s of a 1 Gbit/s link per contact
however short the rounds are. The target of 10 s for 100 contacts is not met and cannot be
with this many products per contact; without the triples a batch of 100 is still about 10 s
of local work (each party's hints, 252 point doublings per contact, are computed on one
thread, and the evaluator handles five million shares).

**Stored tables** would remove that cost for every contact after its first session. Design
and options: `SEALED_SENDER_AGREEMENT.md`, "Keeping the table across sessions". Not built: the
form with no cost at load needs a field-engine MAC key that persists across sessions, which
is the owner's decision. `rounds_fixture store` / `load` shows it in the two engines: a table
prepared in one pair of processes, each keeping its own shares and MAC shares, is imported by
a later pair with no exchange and sends correct messages; with one share changed by one party
the first message stops at the MAC check.

### Whole sessions through the relay

`check_signal_service_local.py malicious --runs 1 --broadcasts 4 --link-delay-ms 1` (2 contacts,
8 sends, the contacts reloaded after the second send, so 4 first sends), party 0's worker:

| | Localhost | 2 ms, as before | 2 ms, `--hinted` |
|---|---|---|---|
| A contact's first send (the seal operation) | 0.6 to 1.0 s | 12.7 to 16.0 s | 0.9 to 1.8 s |
| Preparing a batch of 2 contacts (operation 66) | — | — | 0.2 s |
| A later send (the seal operation) | 0.5 to 0.7 s | 0.9 to 1.6 s | 0.8 to 1.6 s |
| Send to send, steady state | 0.8 to 1.1 s | 1.3 to 2.2 s | 1.25 to 2.0 s |
| Field engine time in the session | 2 s | 51 s | 2.9 s |
| Worker time of the session | 18 s | 75 s | 26 s |

**The Rust worker (S8, 2026-11-12).** The same run (`--runs 1 --broadcasts 4 --link-delay-ms 1`,
party 0's worker, malicious) with `node_worker` and with the C++ worker (`--worker legacy`),
back to back on the same tree and circuits:

| | C++ `tls-worker-fixture-v3` | `node_worker` |
|---|---|---|
| A contact's first send (operation 41, busy) | 16.87, 13.92, 14.30, 14.21 s | 16.83, 13.94, 14.41, 14.13 s |
| A later send (operation 41, busy) | 1.30, 1.11, 1.23, 0.89 s | 1.34, 1.18, 1.23, 0.94 s |
| Send to send, steady state (median of the last four) | 1.31 to 1.93 s (1.70) | 1.43 to 2.17 s (1.77) |
| Worker time of the session | 72.7 s | 73.4 s |

The same within noise; a later send is about 0.04 s slower with `node_worker`, as expected from
its double agreement (each forwarded operation is agreed on the control link and again inside
the legacy library, one extra message delay; lib.rs, "Design note"), which goes when the legacy
dispatch loses its own agreement.

A steady-state message is 0.3 to 0.9 s slower at 2 ms than on localhost, before and after:
its field rounds were never the larger part (0.27 s, now 0.08 s). What remains is listed below.
The target "not slower than localhost by more than the server's latency" is not met.

`... --runs 0 --signup --link-delay-ms 1` (a new contact's first message received in one
session, then a send session to it and the two others):

| | Localhost | 2 ms, as before | 2 ms, `--hinted` |
|---|---|---|---|
| The record that carries the envelope (2.7 KB) | 1.1 s | 3.2 s | 2.7 s |
| Unseal, certificate, prekey part | 2.5 s | 20.9 s | 3.7 s |
| Agreements, session, text | 2.3 s | 13.7 s | 3.1 s |
| **A first message received** | **5.9 s** | **37.9 s** | **9.4 s** |
| Worker time of the receiving session | 11.7 s | 49.5 s | 16.6 s |
| Worker time of the send session after it (6 sends, 5 of them a contact's first) | | 81.3 s | 23.1 s |

The target of 8 s for a first message received is missed by 1.4 s. Of the 9.4 s the field
programs are about 1.8 s (0.6 s of it waiting for triples); the rest is Boolean circuits and
their exchanges, the conversions, and 87 `gcm-multiply` runs for the large record's GHASH key
powers (two round trips each, one after the other: 0.4 s that one batched run would save).

**Device refresh.** Under `--hinted` the refresh uses the same programs (the bundle's identity
key lifted once with its table; both prekey signatures as sums over it in the same rounds;
the agreements from tables of the device's keys): per device about 100 field rounds and 25
openings where there were 2,537 (lift) + 2,046 (signatures) + 1,016 (agreements).
`--multi-device --hinted` passes on localhost with the database nodes (a second device linked,
the contact refreshed, both devices decrypt, the list read back in a later session). It was
not timed through the relay; by the counts a refresh of two devices loses about 11,000 field
rounds, some 25 s at 2 ms.

### What a 2 ms link still costs

Measured in the runs above; none of it is in the field programs any more.

- **Bandwidth before latency.** Malicious mode sends about 287 bytes each way per AND gate and
  66 KB each way per field triple: 0.8 GB each way per message, 0.75 GB per contact prepared,
  about 3 GB per first message received. A 1 Gbit/s link carries a message in 6 to 7 s; the
  2 ms of latency matter only above about 5 Gbit/s. WireGuard's throughput on the chosen
  machines is unmeasured; the engines use about 20 TCP connections, so it can use several cores.
- **The Boolean engine exchanges once per about 30,000 AND gates** (and twice per circuit run):
  `gcm-multiply` (16K gates) +4 ms, `signal-request-ctr` (330K) +22 ms, `signal-seal-built`
  (2.2M) +165 ms. A message's 2.9M gates are about 100 sequential round trips, 0.2 s. Sending
  the chunks without waiting for the other party's is a change inside the validated engine;
  not attempted.
- **Every reveal call is two round trips** (a request agreement and an opening), +4 ms; a
  response is 26 calls, 0.1 s per message. Revealing a response's public part in fewer calls is
  controller work; the agreement half is now one message delay (short `Challenge::transfer`s
  cross on the wire).
- **Every field opening carries two MAC checks** (3.5 round trips). The check after an opening
  could be left to the check before the next one for openings that only continue a field
  computation; that is a change to the order of checks, not made.
- **The field engine's rounds are two message delays each.** `TLS_WORKER_FIELD_DIRECT=1` (the
  library's direct opening: both parties send at once) makes them one; built and run in the
  fixture, off by default, `NEEDS_REVIEW.md` 3b.
- **Conversions between the engines** are one opening, one transfer and one circuit run each
  (about 15 ms), one after the other: 10 per first message received, 1 per contact prepared, 1
  per message. Batching them is not done.
- **TCP.** Every engine link has Nagle's algorithm off (emp's `NetIO`, the field library's
  sockets) and buffers left to the operating system; at 10 Gbit/s and 2 ms the bandwidth-delay
  product is 2.5 MB, inside what the system grows to (emp has `SocketOptions::
  for_bandwidth_and_rtt` if a path ever needs more). No link sets keepalive; inside WireGuard
  between two public addresses none is needed. The field library's sockets have a 5-minute
  receive timeout, which only a peer stalled in the middle of an exchange would meet.
- **Memory.** The field engine never frees a share: a batch of 100 contacts creates about five
  million (0.3 GB), and a session that prepares thousands grows without bound.
- **The database client** was not in these runs. Per stored state it is two `exchange`
  operations between the workers (two round trips each) beside its own traffic to the
  database nodes.

## The long-lived send session (2026-11-11)

The node daemons now keep one send session per node pair alive across notifies
(`node_daemon/README.md`, "The long-lived send session"). Measured on this machine (12 cores;
both computation nodes, the five in-memory database test nodes, the local Signal-Server, and each
daemon's receive session running beside the send session) with
`check_signal_service_local.py MODE --runs 0 --sustained 160 --restart-after 80`: eight contacts,
twenty notifies of all eight (160 messages, a 59-byte text), issued one after another by
`notify-app` as an application would; the daemons end the session after 80 messages and start a
new one. Both modes passed: every notify completed with all eight delivered and both nodes
agreeing, and every recipient decrypted every text exactly once (the planned restart lost and
repeated nothing).

| | Semi-honest | Malicious |
|---|---|---|
| Session start to ready (process, circuits from the cache, handshake, upgrade) | 1–2 s | 3–6 s |
| A notify of 8 contacts, steady state, inside the session | 6.2 s (0.78 s per message) | 11.2–11.5 s (1.41 s per message) |
| The first notify of a session, extra (its 8 contacts prepared) | +2.2 s (0.28 s per contact) | +6.5 s (0.8 s per contact) |
| A planned restart, as the application sees it (next notify) | +8 s | +11.7 s |
| **Sustained, inside the session** | **1.25 messages/s** | **0.67 messages/s** |
| Sustained, as the application sees it (signing, both daemons, hand-over) | 1.14 messages/s | 0.63 messages/s |
| Resident memory of one node's send session (controller and worker), idle | 1.0 GB | 2.8–2.9 GB |
| — with 8 contacts loaded, over 80 messages | 1.6–1.8 GB, no trend | 3.8–4.4 GB, no trend (±0.3 GB between samples) |
| Traffic between the workers per message, one direction (whole sessions, so with handshakes and unused stock) | 117 MB | 0.96 GB |
| AND gates per message (same) | 2.84M | 2.89M |

**One session, no restart, with the worker's buffer release** (`--sustained 400`, semi-honest):
400 messages (50 notifies of 8) in one session, 1.26 messages/s inside it and 1.21 as the
application saw it; the session's resident memory sampled every 10 s stayed between 1.50 and
1.76 GB from the 8th message to the 400th, with no trend (1.57 GB at 200, 1.57 GB at 392);
99 MB of traffic per message one way over the whole session; every recipient decrypted all 50
texts exactly once. Malicious, `--sustained 200`: 200 messages in one session, 0.69 messages/s
inside it and 0.64 as the application saw it; resident memory between 3.26 and 3.83 GB per node
from the 16th message to the 200th, no trend; 0.84 GB of traffic per message one way over the
session. (The daemons' first session of that run failed while starting, both sides with
"write_some: No buffer space available" in the field engine's library, as the receive and send
sessions opened their links at the same moment on this machine; the daemons started the next
one 9 s later and nothing else was affected.)

For comparison, the same notify of 8 contacts as its own session (the previous daemon) paid the
fixed 6.8 s (malicious) and the 6.5 s of preparation every time: about 25 s instead of 11.3 s.

**Where a steady message's time goes** (`.deps/lowering-scratch/serve_profile.py` over party 0's
worker log, 56 messages in the middle of a session):

| Malicious, per message | |
|---|---|
| Send circuit (operation 41) | 0.53 s |
| Sealing the request record (13), storing the contact's state (38), opening the response (12), reveals (43) | 0.18 s |
| **Database client: two `write-blob` runs (a debug build, one process each) and the exchanges between them** | **0.41 s** |
| Controllers (reveal steps, parsing, building the request), the server | about 0.3 s |
| **Per message** | **1.43 s** |

In semi-honest mode the workers are busy 0.12 s per message and the same 0.4 s of database
client calls is half of the 0.78 s. **What limits throughput on one machine is therefore the
database write before every send** (state stored before the message leaves: an owner's
decision), then the send circuit. The triple pools (about 2.5M AND triples per second on this
machine for 2.9M per message) keep up because they refill while the controllers wait for the
database client. Per notify there is also the read of its ids (five client runs) and the
agreement on results: about 0.2 s.

**On real nodes the limit moves to the link.** Malicious mode moves 0.96 GB each way per message:
a 1 Gbit/s link carries one message every 7.7 s (0.13 messages/s), 10 Gbit/s one every 0.77 s,
about the local rate. Semi-honest mode moves 117 MB: 0.94 s per message at 1 Gbit/s.

**The owner's volume** (about 1,000,000 messages a month, US daytime, spiky): 1,000,000 / 30 days
/ 12 hours is 0.77 messages/s on average, so a peak of five to ten times that is 4–8 messages/s.
One pair as measured here (0.67/s malicious, 1.25/s semi-honest on one machine) covers about the
average, not the peaks; in malicious mode only with 10 Gbit/s between the nodes, and the traffic
is about 1 PB each way per month (1,000,000 × 0.96 GB), which at cloud egress prices is the
dominant cost. Several pairs in parallel scale the rate (what they need: PRODUCT_TODO.md section
7); the database nodes then take two writes per message from every pair. Cheapest levers, in
order: a long-lived release-build database client (−0.4 s per message), fewer AND gates per
message (the send circuit), and for traffic, semi-honest mode (8× less) if the owner accepts it.

**What bounds a session's life** (and what the daemons do about it):

| Bound | Size | Handled by |
|---|---|---|
| Memory, per distinct contact loaded and prepared (the field engine never frees a share; the contact's Boolean state) | about 0.1 GB per contact here (8 contacts: +0.8 GB semi-honest, +1.2–1.5 GB malicious, including circuits loaded by the first notify); the earlier estimate for a batch was 3 MB per contact of field shares alone | `send_session.max_megabytes` (the daemon samples the tree's resident memory every 10 s) and `max_messages`; a large notify must be split (PRODUCT_TODO section 4) |
| Memory per message | no trend over 400 messages (semi-honest) or 200 (malicious) in one session, within the ±0.3 GB the samples scatter: below about 1 MB per message. Each sealed request and each received record kept about 50 bytes of engine state per bit; the worker now drops a buffer once sealed and keeps only the newest 64 received records (`tls_worker_v3.cpp`, operations 12 and 13) | the fix; `max_messages` (default 5,000) as a backstop |
| TLS on one connection | AES-128-GCM allows 2^24.5 records per key (RFC 8446 5.5); a message is 2–3 records, so about 8M messages; no client KeyUpdate under the libsignal profile | `max_messages`, and a replaced connection starts new keys |
| Request ids | 2^63 + n per connection, ten varint bytes until 2^64 | none needed |
| The server dropping an idle socket (90 s) or closing one | | polled every tick, replaced at once; pinged after 25 s idle |
| The notify request's lifetime | read at the job's start (fresh: 120 s); write-backs allowed for 6 hours after it was issued, if its read was served (`notify_write_back_secs`; the nodes remember 4,096 served reads) | a job longer than 6 hours would get "retry later" for the rest; a session that dies after 120 s cannot resume the notify (the application signs a new one) |
| Logs | an idle session ticks four times a second (once a second after a minute idle), two worker log lines a tick | log rotation (deployment) |

## Lean script flows on the real engines (2026-11-13)

First runs of the script stack (`SIGNAL_SCRIPTS`, STACK_NOTES.md section 9) on the real engines,
this machine, local harness.

Sustained stage (`--runs 0 --sustained 16 --restart-after 8`, eight contacts, two notifies of
eight, 16 messages), all-legacy against `--scripts random` (joint randomness as op 93 batches; the
only group that can be selected in a real session today):

| mode | selection | wall s | in-session s | messages/s in session | s per message in session |
|---|---|---|---|---|---|
| malicious | legacy | 51.6 | 36.1 | 0.443 | 2.26 |
| malicious | `random` | 51.4 | 35.2 | 0.455 | 2.20 |
| semi-honest | legacy | 24.6 | 16.2 | 0.988 | 1.01 |
| semi-honest | `random` | 24.8 | 16.1 | 0.994 | 1.01 |

The difference is within run-to-run scatter: joint randomness is two exchanges (commit, open) per
call instead of one worker operation, and costs no engine work.

The TLS handshake through the scripts (`--scripts random,masks,tls,upgrade --strict-produced`,
malicious; the run stops after the upgrade, PROOF_GAPS J22): from `connect` to the first request
sealed after the upgrade the workers report about 2.36 s against about 1.89 s for the legacy
handshake and upgrade in the same stage (the worker's own clock; one run each). It includes the
deployed S10 mask generation (N = 16, B = 22: 704 candidates), about 0.33 s of it, sent as one
batch of about 6 MB (the pipe bound was raised to 16 MiB for it).

V3 field-program re-export: 68 s, 0.97 GB (alone). Real-engine fixtures (malicious): `e2e_s10.py`
425 s (seven flows, each on fresh workers), `e2e_s11.py` 565 s (nine flows), `e2e_s12.py` 61 s,
`e2e_s13.py` 127 s (3.65 GB peak), `e2e_s15.py` 61 s; each under 1 GB except S13.

### The closed selection: every session flow as Lean scripts (2026-11-13, after J21-J26)

`SIGNAL_SCRIPTS=contacts,account,curve,send,receive,refresh,tls,masks,random,upgrade` (all ten
groups; the smallest selection with `tls` the selection accepts, STACK_NOTES section 10),
`--strict-produced`, this machine, one run each. Every stage below passes, and where there is a
golden its records equal it (compare_records: same modulo masks).

Sustained stage (`--runs 0 --sustained 16 --restart-after 8`), both sides strict, run back to back:

| mode | selection | wall s | in-session s | messages/s in session | s per message in session | AND gates per message |
|---|---|---|---|---|---|---|
| malicious | legacy | 55.5 | 39.1 | 0.409 | 2.44 | 3,807,674 |
| malicious | closed (scripts) | 65.7 | 46.3 | 0.346 | 2.89 | 4,063,534 |
| semi-honest | legacy | 24.5 | 16.6 | 0.964 | 1.04 | 3,614,944 |
| semi-honest | closed (scripts) | 37.4 | 26.9 | 0.595 | 1.68 | 3,967,144 |

Per message the scripts cost about 18 % more time in the malicious mode and 62 % more in the
semi-honest one, with 7-10 % more AND gates (the scripts' kernels are the same; the extra gates
are the script path's word circuits and conversions that the C++ folded into its kernels). The
semi-honest mode, where engine work is cheap, shows the per-batch cost: every script operation is
one or more op 93 batches, each agreed on the control link (one more message delay than the legacy
operation, plan R1) and checked by the Rust interpreter.

Whole stages (seconds, the harness's `elapsed`; legacy column: the same stage all-legacy, this day):

| stage | legacy | closed (scripts) |
|---|---|---|
| malicious `--runs 2 --signup` | 168.4 (non-strict golden run; legacy strict fails on the local set's missing 2224 signup kernels, PROOF_GAPS J27) | 178.8 |
| malicious `--runs 0 --db` | 215.5 (non-strict) | 226.7 |
| malicious `--runs 1 --db` | 239.5 (strict) | 274.2 |
| compact signup `--devices 3` (libsignal) | 72.7 (receive 10.1, send 42.4) | 87.3 (receive 13.8, send 52.8) |
| malicious `--runs 0 --recovery devices` | — | 233.3 |
| semi-honest `--runs 2 --signup` | — | 146.0 |
| malicious `--runs 0 --ceremony` (with `ceremony`: all eleven groups) | 83.8 (the ceremony non-strict, as the harness runs it) | 93.8 (strict) |

("—": not run all-legacy this day.)

### The script path's cost (2026-11-13, later: measured, then mostly removed)

**How it was measured.** The sustained stage (`--runs 0 --sustained 16 --restart-after 8`, closed
selection, `--strict-produced`; with eight contacts and a restart after eight messages EVERY message
is a session's first send to its contact, so every message includes the contact's preparation, op
66 / the C++'s `prepare`). Per worker operation the worker log gives the time inside the worker
(`busy`), the AND gates, and the time outside it before the operation (the controller computing the
next request, the pipe, the other party). New in node_worker (counts and durations only, never a
value): one line per op 93 batch with `TLS_WORKER_BATCH_LOG=1` (bytes, instructions by kind, the
circuits and programs it names, decode/agreement/check/execute times) and a per-session total line.
The controller was sampled with macOS `sample` during the stage (`.deps/lowering-scratch/pf_sample*.py`).
Per-message figures below are over the seven steady messages of a session (from one send circuit
to the next; `pf_period.py`, `pf_ops.py`).

**Finding.** The engines' work was NOT the difference: per message the workers were busy 371 ms
(scripts) against 332 ms (legacy) in the semi-honest mode, and equally busy in the malicious mode;
AND gates per steady message 2.95M against 2.83M (+4.6 %); the agreement waits were small. The
time was the Lean controller between batches: 799 ms outside the worker per message against 228 ms,
almost all of it in five places, each a plain algorithmic defect of IO-glue or codec code:

| where (controller, per steady message, semi-honest) | before | after | fix |
|---|---|---|---|
| decoding a program's reply (`Dec.take` measured the whole rest of the input for every 32-byte element: quadratic) | ~150 ms | <1 ms | `Dec.takeList`; the runner decodes with `decodeRepliesFast` (= `decodeReplies`, `decodeRepliesFast_eq`) |
| cutting 130 KB of randomness into 2,031 mask contributions (`(b.drop (64*i)).take 64`: quadratic) | ~140 ms | ~8 ms | `Engine.byteBlocks` (one pass, `byteBlocks_eq`), `fromLEFast` |
| this party's GHASH half of a sealed record (each GF(2¹²⁸) product built 256 masks with `BitVec.replicate`) | ~115 ms | ~7 ms | `Local.Ghash.mulFast` (`mul_eq_mulFast`); the glue computes `halfFastOf` / `leftsFastOf` / `extendFastOf` (each proved equal to the original) |
| the seal's envelope length (`sealEnvBytes` ran the whole sealed-sender encryption on zero inputs to measure it) | ~28 ms | ~10 ms | `sealEnvBytes` defined from lengths (`sealV1_length`); its old definition is the theorem `sealEnvBytes_value` |
| encoding/decoding numbers byte by byte with big-number arithmetic | ~80 ms | small | `leFast` / `fromLEFast` (seven bytes per step); the runner encodes with `encodeBatchFast` (= `encodeBatch`) |

In the worker, two costs grew with the session: `Interp::admit` CLONED the whole handle context for
every batch (every id the session ever used: 0.16 ms per batch at the start of a session, 0.46 ms
after eight messages, and growing), and `execute` scanned every live engine value after every batch.
Now the batch is checked in place with an undo journal (a refused batch still leaves the context
unchanged, tested) and only the batch's own handles are examined: 0.02 ms per batch, flat.

Batches: a finished script whose last batch only frees handles no longer sends it alone; the frees
open the next batch (`Runner.pending`): 74.6 → 47.9 pipe operations per message (legacy: 34.4), each
one agreement (one control-link round trip) fewer. No opening was added, removed or reordered: the
instructions and their order are unchanged, only the batch boundary of trailing frees moves (frees
release nothing; the D8 rule, a release ends its batch, still holds: the frees come first).

**Per operation, per steady message** (semi-honest; "out" = controller and pipe time before the
operations; "opens" = openings and exchanges in the batches, each a party↔party round besides the
batch's agreement; legacy operations have their rounds inside the C++):

| operation | legacy ops / busy / out / AND | scripts BEFORE batches / busy / out / AND / opens | scripts AFTER batches / busy / out / AND / opens |
|---|---|---|---|
| 41 seal (preparation, ephemeral key, seal) | 1 / 294 ms / 0 / 2,187k | 10 / 285 / 363 / 2,187k / 8 | 10 / 292 / 48 / 2,187k / 8 |
| 13 record seal (request) and its GHASH key powers | 1 / 20 / 0 / 446k | 3.4 / 30 / 182 / 574k / 3.4 | 3.4 / 21 / 16 / 574k / 3.4 |
| 33 joint randomness, commitments | 2 / 0.2 / 0.1 / 0 | 10 / 8.6 / 4.5 / 0 / 10 | 8 / 0.8 / 2.6 / 0 / 8 |
| 42 request, frees | 1 / 0.2 / 12 / 0 | 28 / 18 / 17 / 0 / 0 | 1.1 / 0.1 / 16 / 0 / 0 |
| 43 reveals of the response | 19 / 3.5 / 125 / 2k | 20 / 15 / 124 / 2k / 20 | 20 / 4 / 127 / 2k / 20 |
| 12 record open, 38 contact seal, 39 database, server I/O | 10 / 9 / 87 / 151k | 10 / 11 / 108 / 151k / 2 | 10 / 11 / 89 / 151k / 2 |
| **total** | **34.4 / 332 / 228 / 2,825k** | **82.7 / 371 / 799 / 2,954k / 45** | **56.0 / 334 / 300 / 2,954k / 45** |

Malicious, after: busy 1,415 ms per message (legacy 1,442), outside 361 ms (legacy 283).

**AND gates (+7–10 % per message in the harness's figure).** Two parts, both design choices of the
script path, neither a check the C++ skipped: (1) a session's start: +1.28M AND per session, of which
1.03M is the S10 mask pool's cut-and-choose (`modadd-open` over the 672 opened candidates, P-CUT;
the C++'s pool is generated differently, `dyn_word_mask.h`), the rest the GHASH key powers; with a
restart every eight messages that is +0.16M per message; (2) steady state +0.13M per message: the
GHASH key powers come from the doubling schedule (`Local/Ghash.lean`: every odd power of a round in
ONE `gcm-multiply` run, ⌈log₂ n⌉ + 1 rounds instead of about n/2) which computes up to twice the
powers a record needs. Both trade gates for rounds; under link delay rounds dominate.

**Sustained stage after** (seconds per message in session; one run each, this machine; the legacy
runs the same day):

| mode | legacy | scripts before | scripts after |
|---|---|---|---|
| semi-honest | 0.99–1.04 (15.9, 16.6 s) | 1.68 (26.9 s) | 1.07–1.09 (17.1–17.4 s) |
| malicious | 2.23–2.44 (35.6, 39.1 s) | 2.89 (46.3 s) | 2.29 (36.6 s, twice) |

**Repeat sends to a prepared contact, and rounds (found later the same evening, J30).** The
sustained stage above makes every message a first send. With repeat sends the scripts prepared the
contact AGAIN on every message (the send's glue wrote back a stale table entry, dropping the
prepared static word): invisible locally next to the other costs, but with `--link-delay-ms 1`
(2 ms round trip; `--runs 1 --broadcasts 4`, malicious) a message took 15.0 s against legacy 7.7 s,
the workers busy 14.7 s against 7.5 s — the preparation's ~5,000 field-multiplication rounds per
message. Fixed (the entry re-read after the script). After the fix:

| stage | legacy | scripts |
|---|---|---|
| `--runs 1 --broadcasts 4 --link-delay-ms 1`, malicious (harness elapsed) | 142.2 s | 140.9 s |
| `--runs 0 --sustained 16` (one session; the second notify to prepared contacts), malicious, in session | 28.9 s (1.81 s per message) | 30.3 s (1.89 s) |
| the same, semi-honest | 13.9 s (0.87 s) | 15.4 s (0.96 s) |

So with a 2 ms round trip the script path is at parity (its fewer GHASH rounds offset its extra
batch agreements); on one machine it is 5 % (malicious) to 11 % (semi-honest) slower per message.

**What still separates scripts from legacy** (about 70 ms per message, both modes, all of it Lean
controller time; the engines and rounds are at parity): the contact preparation's glue (cutting and
encoding 2,031 mask contributions, ~25 ms), the ephemeral key's and the static agreement's glue
(~10 ms), the Signal message the envelope length still builds (~10 ms, the length of
`SpqrSend.canonical`'s wire could be proved like `sealV1_length`), the GHASH half on BitVec
(~7 ms; a 64-bit-limb multiplication proved equal would make it negligible), and ~22 more pipe
operations per message than legacy (agreement, encoding, a pipe round trip each; ~10 ms here, about
2 ms each over a 2 ms round trip). The preparation share appears only on a session's first send to
a contact, which in this stage is every message; in a long session to the same contacts it does not
recur. Not done: the `csimp` attribute would have let the compiled code use the fast versions in
place of the definitions, but the plan forbids it in `TlsMpc/Node` (lint `escape-hatches`), so the
runner and the IO glue call the proved-equal fast functions by name.

## What remains, with estimates

| What | Gain |
|---|---|
| Send without waiting for each response (controller) | up to 0.26 s per message here; more over a real link |
| Reveal steps and parsing in the controllers | 0.1–0.3 s per message; about 1.5 s per first message received |
| The database client as a long-lived process (and a release build) | measured in the long-lived session: 0.4 s per message today (two `write-blob` runs of a debug build), the largest single item outside the workers |
| More AND-triple factories on real nodes | removes the pools as the limit in long broadcasts (about 1.2 s → the circuits' own 0.5 s per message) |
| Open "is a handshake record" first and skip the framing scan for application records | Done (see "The framing circuit"): 2.7 KB record 2.87M → 1.14M AND in its size class |
| Prepare contacts in batches | Done behind `TLS_WORKER_HINTED=1` (see "Rounds"): the rounds are per batch, not per contact |
| Keep a contact's table with its stored state | 14,000 field triples (0.9 GB each way) per contact per session; designed, needs a decision (see "Rounds", stored tables) |
| The Boolean engine's chunks sent without waiting; fewer reveal calls per response | about 0.2 s and 0.1 s per message at a 2 ms round trip |
| Preload circuits at start-up beside the handshake | about 2 s per process |
| The engine's per-circuit analysis cached | perhaps a quarter of the remaining 0.2 s per million AND |

## Earlier controller fixes (before this work)

Revealing server bytes in multi-byte steps (261 calls → 118 per send session) and byte
operations that no longer go through arbitrary-precision arithmetic (`PublicReceive.fast_eq`)
took the time outside the workers from 24.5 s to about 6–8 s per send session.
