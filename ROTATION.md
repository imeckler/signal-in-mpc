# Connection rotation over Tor with a pool (X2)

PRODUCT_TODO.md section 8 (the rotation item, owner decision 2026-11-11), REORGANIZATION_PLAN.md
section 9 (X2) and section 8 (T15). Status: **the pure part is done**
(`TlsMpc/Node/Policy/Rotation.lean`, `TlsMpc/Node/Policy/RotationTest.lean`, both new; nothing
imports them yet). The integration into the session and the worker is the to-do in section 6.

## 1. The problem

The Signal server sees which TCP/TLS connection each sealed-sender message arrives on. Today
(`Policy/Circuits.lean`, `Circuits.assign`) a send session has N fixed connections
(`SIGNAL_TOR_CIRCUITS`, 1..16) and contact of rank r (ascending ids) always goes on connection
r mod N, in id order. One broadcast of n messages therefore links groups of n/N recipients
(3,500 each for n = 14,000 and N = 4), and the same groups in every session.

Rotation: each connection carries a *random* number of messages around a mean (default 10) and is
then closed; the next one on that pool slot is a fresh connection on a fresh Tor circuit (new SOCKS
credentials). A pool of slots (default 4) is used at random, in a random send order, so which
recipients share a connection is decided by joint randomness alone, not by ids.

## 2. The design (`Policy/Rotation.lean`)

**Configuration** (`Rotation.Config`, to become `Node.Config.rotation`; agreed by both nodes):
`mean` (default 10), `poolSize` (default 4), `hold` (ms, default 0), `length` (the law of a
connection's message count, default `uniform`). `Config.valid`: mean 1..1000, pool 1..16, hold at
most 10 min, a geometric cap of mean..65536. A batch has fewer than 2³² messages.

**Input of the planner**: the hash `H` (SHA-256, `sha256 = TlsWire.hash`), a 32-byte seed of joint
randomness (a fresh `Random.joint` per batch), the message count `n`, the configuration, and
`base` (the session's next connection generation). Nothing else: no contact id, text, per-contact
state or result is an argument (`plan`, `skeleton`).

**Output** (`Plan`): `order` (a permutation of 0..n−1: the i-th message sent is input `order[i]`)
and `actions`, a list of
* `open slot gen`: a new connection on that slot (connect through Tor with the credentials of
  generation `gen`, handshake, unauthenticated WebSocket upgrade);
* `send position slot`: the message at that position, on the slot's connection;
* `close slot`: close the slot's connection (op 92).

**How the actions are made** (`stepMsg`, `schedule`, `runPool`): for each message in send order,
draw its slot uniformly from `0..poolSize−1`. If the slot has no connection, `open` one with the
next generation and draw its budget L (`drawLength`). Send. If that was the connection's L-th
message, `close` it. At the end of the batch, close every slot still open (`closeFrom`). Opens are
lazy (a slot's next connection is opened when the slot is next drawn), so no connection is ever
opened without carrying a message.

**The executor interface**: `PlanState` (what remains), `next : PlanState α → Option (Action α ×
PlanState α)` (the next action, in order), `drive` (`drive_all`: driving `next` yields exactly the
plan's actions), `nextOpen` (the next `open` still to come: the executor may build its circuit
ahead, see section 7). The session drives the plan without knowing the policy.

**Credentials** (`labels session gen reconnect`): username `tls-mpc-<session id, 16 chars>` (as
today), password `rot-<gen>-<reconnect>`; `reconnect` counts replacements of that generation after
a loss (0 for the planned connection). Tor isolates streams by SOCKS username/password
(`IsolateSOCKSAuth`, on by default for a SocksPort), so every connection gets a circuit of its own.
Today's `Circuits.labels` (`send-i-of-N`) reuses the same credentials for a reconnect on the same
index, and Tor may then put it on the same circuit (circuits stay usable for 10 minutes,
`MaxCircuitDirtiness`). The generation counter is session-wide (`base`), so credentials are never
reused across batches either. The receive socket keeps `receive`.

**The hold window** (`plannedAt`): an arrival at t joins the open batch if that batch's deadline d
has t ≤ d ≤ t + hold, otherwise it opens a batch with deadline t + hold; a batch is planned (all
its messages shuffled together, one plan) at its deadline. This is how concurrent broadcasts are
interleaved: every notify arriving within the window goes into one batch. With hold = 0 a batch is
planned when its first notify arrives; notifies arriving while a batch is being sent form the next
batch (they are not merged into a running plan).

**The law of a connection's message count** (`Length`):
* `uniform` (default): L uniform on [1, 2·mean − 1] (1..19 for mean 10). Its mean is exactly
  `mean` (`uniform_mean`); it has a hard maximum, so no connection ever links more than 19
  recipients; one draw per connection. The quantity that matters to a recipient is the size of the
  connection *it* is on, the size-biased mean E[L²]/E[L] = (4·mean − 1)/3 (`uniform_second_moment`):
  13 for mean 10, i.e. 12 other recipients on average, at most 18.
* `geometric cap` (a parameter): after each message the connection ends with probability 1/mean
  (memoryless: how long a connection has run says nothing about when it ends), at most `cap`
  messages. Mean mean·(1 − (1 − 1/mean)^cap) (9.85 for mean 10, cap 40); size-biased mean about
  2·mean − 1 = 19, so a recipient shares its connection with 18 others on average: worse. It is
  there if memorylessness is wanted.

**Sampling** (exact and deterministic: both nodes compute the same plan from the same seed):
* words: the four 64-bit big-endian lanes of `H(domain ‖ tag ‖ seed ‖ uint64 k)`, k = 0, 1, …
  (`blockInput`, `lanes`, `Stream`), with domain `"tls-mpc rotation v1"`. Two streams: tag 0 for
  the shuffle, tag 1 for slots and lengths; their hash inputs never coincide
  (`blockInput_tags_differ`);
* a number below r: rejection sampling (`below`): accept w when w < r·⌊2⁶⁴/r⌋ and return w mod r.
  Accepted words are in bijection with [0, r) × [0, ⌊2⁶⁴/r⌋) (`accepted_split`, `accepted_join`),
  so an accepted draw is exactly uniform. Termination without `partial def`: at most 4 words per
  draw; after 3 rejections the 4th word gives w mod r whatever it is (the fallback). Fewer than r
  of the 2⁶⁴ words are rejected (`rejected_few`), so with r ≤ 2³² the fallback is reached with
  probability < (r/2⁶⁴)⁴ ≤ 2⁻¹²⁸ per draw, < 3n·2⁻¹²⁸ per batch with the uniform law (n shuffle
  draws, n slot draws, at most n length draws);
* the shuffle: Fisher–Yates in selection form (`encode`): draws d₀ < n, d₁ < n − 1, …, each
  takes the dᵢ-th remaining position. `encode` is a bijection between valid draw vectors and the
  permutations (`encode_perm`, `decode_encode`, `encode_decode`), so uniform draws give a uniform
  permutation. It is O(n²) on lists: n = 14,000 plans in well under a minute even interpreted.

**What is assumed about the hash (H-PRF)**: for a uniformly random 32-byte seed the observer does
not know, (tag, k) ↦ H(domain ‖ tag ‖ seed ‖ uint64 k) is indistinguishable from a random function
(SHA-256 as a PRF keyed by the seed; true in the random-oracle model). Under H-PRF the words are
independent and uniform, hence: the shuffle is uniform up to statistical distance n·2⁻¹²⁸ plus the
PRF advantage, and it is independent of the slot/length schedule (the two streams are disjoint
inputs). The seed comes from `Random.joint` (P-RAND: uniform when one node is honest) and is never
sent to the server. **No proof in the file uses H-PRF**: every theorem holds for every `H`.

## 3. The theorems (all proved; no `sorry`, axioms only `propext`, `Quot.sound`, `Classical.choice`)

**T15: the plan reveals nothing about ids.**
* By construction: `plan H seed n cfg base` and `skeleton H seed n cfg base` take nothing else.
* `plan_actions`: the actions are the skeleton (sends carrying send indices 0..n−1) relabelled by
  the order. `skeleton_def` / `plan_order` (definitional): the skeleton reads only the pool stream,
  the order only the shuffle stream.
* `t15_erase`: for any two input lists of the same length (contacts, texts, states, anything), the
  composed sender (`compose`) performs the same actions once payloads are erased: same opens (slot,
  generation), same closes, same sends on the same slots, in the same order.
* `t15_carriers`: the (slot, generation) carrying the i-th sent message is the skeleton's, whatever
  the inputs. `t15_sends`: the i-th message sent is input `order[i]`. Together: *given the
  shuffle*, the sequence of connections carrying the messages is independent of which contact is in
  which position; and the shuffle is a uniform permutation independent of that sequence (H-PRF).
* The shuffle: `shuffle_perm` (a permutation), `encode_perm`, `decode_encode`, `encode_decode` (a
  bijection with the draw vectors), `draws_valid`, `below_lt`, `accepted_split`, `accepted_join`,
  `rejected_few`, `blockInput_tags_differ`.

**Well-formedness**, against `Mon`, the executor's model of the pool (per slot: the open
connection's generation and count). Its rules: `open s g` only on an existing closed slot and with
the next generation; `send _ s` only on an open slot whose connection carried fewer than `maxLen`;
`close s` only on an open slot whose connection carried at least one message.
* `plan_accepted` / `plan_accepts`: the monitor accepts every plan and ends with every slot closed:
  a slot is never used after its close and before its next open.
* `plan_sends_perm`: every position is sent exactly once.
* `plan_generations`: the generations opened are base, base + 1, … in order: none is reused.
* `plan_pool_bound`: after every prefix of the actions, at most `poolSize` connections are open.
* `plan_counts`: every connection carried between 1 and `maxLen` messages; the counts sum to n;
  one per generation.
* `plan_connection_bounds`: with k connections, k ≤ n ≤ k·maxLen (so ⌈n/maxLen⌉ ≤ k ≤ n).
* `plannedAt_bounds`: a message waits at most `hold` before its batch is planned;
  `plannedAt_zero`: with hold = 0 no message waits.
* `drawLength_bounds`, `uniform_mean`, `uniform_second_moment`, `drive_all`.

**Unlinkability in plain terms.** Two messages share a connection exactly when the skeleton put
their send indices on the same generation, which the pool stream alone decided; the shuffle,
independent of it, decides which inputs those indices are. So for any two inputs a ≠ b the
probability they share a connection is Σ_g k_g(k_g − 1) / (n(n − 1)) over the connection sizes
k_g: a function of the sizes only, the same for every pair, whoever they are. The expected size of
a connection is the mean (10); a given recipient is on a connection of 13 on average (12 others),
at most 19. Over a batch of n messages there are between ⌈n/(2·mean − 1)⌉ and n connections
(proved); in expectation n/mean plus about 0.6 per slot (the partly used last connection of each
slot; renewal argument, confirmed by the statistics below).

## 4. Property tests (`Policy/RotationTest.lean`)

`RotationTest.failures ()` evaluated in a scratch file (`.deps/lowering-scratch/x2_eval.lean`):
**`[]`**. It checks, with SHA-256, 8 configurations (default; mean 1 pool 1; mean 2 pool 3; mean 3
pool 16; mean 10 pool 1; geometric 40; geometric 5 with mean 5 pool 2; geometric 1) × counts
0, 1, 2, 3, 4, 7, 10, 19, 20, 48, 100 × 3 seeds and bases: acceptance by the executor model and the
pool bound after every action; the order is a permutation and the sends follow it; generations
base, base+1, …; counts in [1, maxLen] summing to n; k ≤ n ≤ k·maxLen; `decode` gives valid draws
and `encode` gives the order back; plan = skeleton relabelled; T15 (two different input lists: same
erased actions, same carriers as the skeleton, sends are the inputs in shuffled order); `drive`;
the hold window on generated arrival times (hold 0, 1, 250, 1000, 5000 ms); config validity. Also
the 6 permutations of 3 over 600 seeds: 91, 110, 106, 98, 102, 93. And `checkPlan` at n = 14,000
(default config): no failure.

Connections per batch (default config, SHA-256):

| n | seeds | mean connections | min | max | n/mean + 0.6·pool |
|---|---|---|---|---|---|
| 14 | 200 | 4.5 | 3 | 7 | 3.8 |
| 48 | 1000 | 7.12 | 4 | 13 | 7.2 |
| 1000 | 100 | 102.6 | 89 | 116 | 102.4 |
| 14,000 | 3 | 1,390 | 1,380 | 1,398 | 1,402 |

(Geometric, cap 40, n = 48: 8.4 on average.)

## 5. How it replaces `Circuits.assign`

`Circuits.assign recipients count contact` (Policy/Circuits.lean 27-29) gives a contact's
connection from its rank among the ids; the sends go in input (id) order on N connections opened
once per session. The plan replaces both the order and the assignment, and adds rotation.
`Circuits.labels` (34-38) stays for the receive socket only; send connections use
`Rotation.labels`.

## 6. Integration to-do (do not edit until the session refactor lands; line numbers as of today)

**Configuration**
1. `TlsMpc/Node/Config.lean`: add `rotation : Rotation.Config` to the agreed settings (read
   `SIGNAL_ROTATION_MEAN`, `SIGNAL_ROTATION_POOL`, `SIGNAL_ROTATION_HOLD_MS`; refuse unless
   `Config.valid`); include it in the agreement digest/summary next to `circuits` (54, 170-180,
   215, 228, 245). Rotation needs a proxy (as `SIGNAL_TOR_CIRCUITS` does today, 179-180); decide
   whether `circuits` becomes `rotation.poolSize` or stays the switch (rotation off: today's path).
2. `Session/State.lean` 171-173 `proxyFor`: take the generation and reconnect count and use
   `Rotation.labels` for send connections. `sendCircuits` (167) becomes the pool size.

**Pool (`Session/Pool.lean`)**
3. `openConnection` (48-63, connect at 51): take `(slot, gen, reconnect)`; credentials from
   `Rotation.labels`; on a reused slot, first `Flow.Server.reset` (the slot was closed).
4. New `closeSlot slot`: select the slot, send a WebSocket close frame and a TLS close_notify (what
   an official client does; check against CLIENT_FINGERPRINT.md), then op 92
   (`Flow.Server.close`, item 10), then drop the slot's parser state and request counter.
5. Per-slot request ids restart at 2⁶³ for every new connection: `counters` (`toCircuit` 114-115,
   `deliverJob` 471-473) must be reset at each `open`, not only per index.
6. `openCircuits` (67-100) and `openAll` (138-145, the loop at 142-144) open N − 1 connections up
   front: replace with nothing (opens come from the plan). Connection 0 opened by `Start`
   (Start.lean 56, credentials `some 0`) is the receive/first connection: either make it slot 0's
   first generation or close it before the first batch.
7. `toCircuit` (106-119; `Circuits.assign` at 109): replace by the executor below; `reconnect`
   (127-134): keep the slot and generation, password `rot-<gen>-<reconnect + 1>` (a fresh circuit;
   today it reuses the same credentials, comment at 125).

**Send loops (`Session/Send.lean`)**
8. The executor, shared by both loops: per batch, `let seed ← Flow.Random.joint c.w` (a fresh
   32-byte value), `let p := Rotation.plan Rotation.sha256 seed inputs.length cfg.rotation gen`,
   then drive `PlanState.ofPlan p` with `next`: `open s g` → item 3; `send q s` → the existing
   per-message code for `inputs[q]` on slot s; `close s` → item 4. Advance the session generation
   by `(opensOf p.actions).length`. Executor rule for skipped sends: open a slot's connection only
   when its first send actually goes out, and if every send of a connection is skipped, skip its
   open and close too (so a connection never carries 0 messages).
   - `loop` (210-265): the sends go in `inputs` order (`input::tail`, 251-262) with
     `toCircuit` at 260: replace by the executor; `ensurePrepared` (258) should look ahead in plan
     order (`tail` = the remaining sends of the plan).
   - `deliverJob` (394-559): `count` (398), the queue in input order (423), `Circuits.assign` and
     the counters (468-474): replace by the executor. Settled and stopped contacts (451-456) become
     skipped sends (rule above). Retries with back-off (`queue ++ …`, 541) are not in the plan:
     collect them and send them as a new batch with a fresh seed when due. Reconnects (487, 511):
     item 7. The once-per-session KeyUpdate (528-531, legacy profile only) applies per connection
     or not at all; decide.
   - `deliver` (562-565) / `sendAll` (569-574, `openCircuits` at 572): no up-front opens.
   - `notify` / `inputsOf` (37-71): unchanged; the batch is the concatenation of the notifies the
     hold window gathered (`plannedAt` with `cfg.rotation.hold`).
9. T15 for the composed sender then holds if the executor is the only thing deciding order and
   connections. ORD-1 (state stored before a send) is unaffected: it is per message.

**Worker op 92 on the Lean side** (the Rust side exists: `node_worker/src/server.rs` 36-37, 47,
74 parse `ServerOp::Close`; `shell.rs` 201-205 serves it; `lib.rs` 50 notes no controller sends it)
10. `TlsMpc/TlsWorker.lean`: add `closeConnection` to `Operation` (next to `resetConnection`,
    55). `TlsMpc/TlsWorkerPipe.lean` `code` (11-33): `| .closeConnection => 92`.
    `Flows/TlsLegacy.lean` namespace `Server` next to `reset` (57):
    `def close (w : Worker) : M Unit := Legacy.empty w .closeConnection []`, and the same in
    `Flow.lean`'s API. (The lint allows `TlsWorkerPipe.code` only in the legacy flow files.)
11. Check with the engines: after 92 the slot counts as closed and 91 (`Reset`) is then accepted
    (`shell.rs` 194-199 requires `!connected` and `engines.reset()`, which checks the TLS session
    was retired). Slot indices stay below 64 (`connections.rs` 44-46): slots are reused, so this
    holds for any pool of at most 16.

**Rust: fresh SOCKS credentials per generation**: nothing to change in Rust (the credentials are
part of the agreed `Connect`, `socks.rs`); the Lean side supplies `rot-<gen>-<reconnect>`. Verify
that the deployed Tor's SocksPort does not disable `IsolateSOCKSAuth`.

**Security.lean** should restate (as `t15_*` / `rotation_*`): `Rotation.t15_erase`,
`t15_carriers`, `t15_sends`, `plan_actions`, `plan_order`, `skeleton_def`, `shuffle_perm`,
`encode_perm`, `decode_encode`, `encode_decode`, `accepted_split`, `accepted_join`,
`rejected_few`, `blockInput_tags_differ`, `plan_accepted`, `plan_sends_perm`, `plan_generations`,
`plan_pool_bound`, `plan_counts`, `plan_connection_bounds`, `plannedAt_bounds`, `plannedAt_zero`,
`uniform_mean`, `uniform_second_moment`, `drive_all`; and H-PRF in its list of assumptions.

## 7. Cost

One in-MPC TLS handshake (plus Tor circuit, TCP, WebSocket upgrade) per connection. The handshake
is about 4 s per connection in MPC (PRODUCT_TODO measures 1.5–2.6 s; both shown).

| n (mean 10, pool 4) | connections | handshake time at 4 s | at 2 s | per message (4 s / 2 s) |
|---|---|---|---|---|
| 48 | 7.1 on average (4..13; bounds 3..48) | 28 s | 14 s | 0.59 s / 0.30 s |
| 14,000 | ≈ 1,400 (1,380..1,398 measured; bounds 737..14,000) | ≈ 5,600 s ≈ 93 min | ≈ 47 min | 0.40 s / 0.20 s |

Today a send session opens N connections once (N handshakes for the whole session); with rotation
it is about n/10 + 2.4 per batch, so roughly 1/mean of a handshake per message, plus up to one
partly used connection per slot per batch (why small batches pay more per message: 48 messages pay
2.4 extra handshakes, 50% over n/mean).

What the pool does and does not amortise: the worker runs one operation at a time, so the
in-MPC handshake is paid in the send stream (once per ~10 messages) and is not hidden. Hiding it
needs the worker to run a handshake on one slot while sends go out on the others; the plan is ready
for that (`nextOpen`: a slot's next open may start as soon as its previous connection is closed;
uniform slot choice leaves on average poolSize − 1 = 3 sends on other slots before the slot is
used again). What can be done ahead today, without the engines: Tor circuits (Tor also keeps
clean preemptive circuits for recently used ports, which a stream with new credentials can take).
The planner itself: n = 14,000 plans in well under a minute interpreted (the selection shuffle is
O(n²) on lists; compiled it is faster).

## 8. What an observing server can still link (the limits)

* **Messages on one connection** are linked, by design: on average 13 recipients share a
  connection (at most 19 with mean 10). Which ones is random and independent of who they are.
* **Timing.** The sends of a batch are serialized: one request in flight at a time, a request on
  one connection starting right after the response on another, a new connection opening right
  after another closed. A server that sees the arrival times of unauthenticated sealed-sender
  requests from Tor exits can chain all connections of a batch into one sender, and so link all of
  a broadcast's recipients, unless enough other such traffic arrives at the same time. Rotation
  removes the *connection* as a linking signal, not timing. Mitigations not built: random delays
  between sends and between connections, true parallel sends, cover traffic, a larger hold window.
* **One sender, recognisable.** Bulk sealed-sender sends from Tor exits with our client fingerprint
  (CLIENT_FINGERPRINT.md) are probably recognisable as one sender whatever the circuits
  (PRODUCT_TODO 8): rotation hides which messages go together, not that they share a sender.
  Short-lived connections that each carry ~10 sealed sends are themselves unusual for an official
  client.
* **Across broadcasts.** Each batch draws new groups. Connection sharing alone does not chain
  groups across broadcasts (a recipient receives from many senders, so "a and b shared a
  connection" and "b and c shared a connection" are not the same sender unless something else says
  so); with timing or the fingerprint, it does, and repeated broadcasts to the same set then expose
  ever more pairs, where the old fixed assignment re-formed the same groups (Circuits.lean header).
* **Exits.** A fresh circuit is not a fresh exit: Tor picks exits by bandwidth weight and two
  connections can leave from the same exit IP (shared with other Tor users, so a weak link).
* **The account.** The receive socket is authenticated and names the account; it runs on its own
  circuit, but if it is active at the same time its timing can be correlated with the sends.
* **Batch size and size class.** The number of messages in a burst is about the broadcast's size;
  every message of a broadcast has the same size class (80-byte blocks of the text). Timestamps in
  the requests are the agreed clock, strictly increasing within the session: a timing signal like
  the arrival times.
* **Server-caused retries** (409/410 refresh, 429/503 back-off, a lost connection) send extra
  requests for that contact on the same or a later connection; they reveal what the server caused,
  not ids.
* **Rate limits.** Many connections from Tor exits may meet rate limits per IP (429), shared with
  other Tor users.
