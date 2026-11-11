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
A sustained broadcast of hundreds of messages was not measured.

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


## Rounds (counted, not measured)

Sequential field rounds per program (multiplication levels, plus one opening per level that
has a division): `x25519-fast` 1,016, `edwards-prepare` 1,289 + 484, `edwards-offset-sum`
23 + 8, `xeddsa-recover` 2,537, `xeddsa-check` 2,046, `receive-torsion` 1,265.

| | Field rounds | Boolean circuit runs | Openings and exchanges |
|---|---|---|---|
| Per message | about 33 | about 8 (each a small constant number of flights) | 30 to 45 |
| Per contact, first send | about 2,800 | 2 | about 10 |
| Per first message received | about 11,500 (was about 17,600) | about 20 | about 40 |

The circuit-run and opening counts are estimates from the sequencing code, not counted from a
trace. At 10 ms per round a contact's first send is about half a minute of latency alone, far
more than its computation. What would reduce it, in order of gain:
- Prepare several contacts in the same rounds (the programs take several instances; the
  worker needs an operation that takes a list of contacts, and the controller must call it):
  2,800 rounds per batch of contacts instead of per contact.
- Keep the contact's curve table and long-term agreement with its stored state: no rounds at
  all on later sessions (needs a larger record and a kernel change).
- The sealed-sender server key is public, yet `xeddsa-recover` on it runs in the field engine
  (2,537 rounds, once per key per process); a clear evaluation of the same Lean program would
  remove them.
- On the receive path the lift of the base key (2,537) and the agreements (1,016) do not depend
  on each other and could share rounds if two different programs were evaluated together.
- The three openings after the send circuit (status, timestamp, envelope) and the four width
  openings could each be one.

## What remains, with estimates

| What | Gain |
|---|---|
| Send without waiting for each response (controller) | up to 0.26 s per message here; more over a real link |
| Reveal steps and parsing in the controllers | 0.1–0.3 s per message; about 1.5 s per first message received |
| The database client as a long-lived process | about 0.05–0.2 s per message |
| More AND-triple factories on real nodes | removes the pools as the limit in long broadcasts (about 1.2 s → the circuits' own 0.5 s per message) |
| Open "is a handshake record" first and skip the framing scan for application records | 640 of 935 AND per received byte (2.7 KB record 2.53M → about 0.8M). Changes what the nodes learn for a rejected record and for a `user_canceled` alert: the owner's decision |
| Prepare contacts in batches; keep their table with the stored state | rounds, see above; with stored tables also 14,000 field triples per contact per session |
| Preload circuits at start-up beside the handshake | about 2 s per process |
| The engine's per-circuit analysis cached | perhaps a quarter of the remaining 0.2 s per million AND |

## Earlier controller fixes (before this work)

Revealing server bytes in multi-byte steps (261 calls → 118 per send session) and byte
operations that no longer go through arbitrary-precision arithmetic (`PublicReceive.fast_eq`)
took the time outside the workers from 24.5 s to about 6–8 s per send session.
