# Where the time goes

Measured 2026-11-11 on one machine (both computation nodes, the five database test nodes and the
local Signal-Server on localhost), malicious mode (statistical 128), with
`local_signal_server/check_signal_service_local.py malicious --runs 0 --db --broadcasts 6` and
`scripts/session_profile.py`. A real deployment adds network latency between the two nodes, which
these numbers do not contain (see "Rounds" at the end).

The workers report time by category, each second counted once; the controllers' share is the time
between worker operations.

## One broadcast session: 2 contacts, 6 messages each (12 sends), 73 s

| Where | Time | Share | Notes |
|---|---|---|---|
| Boolean circuits | 28.5 s | 39% | 38.3M AND gates, 10.3 GB sent |
| Controllers, database client, server | 24.5 s | 33% | see below; most of it was avoidable and is fixed |
| Field triples being generated | 10.2 s | 14% | 67,003 products, 4.8 GB sent |
| Loading circuits | 6.8 s | 9% | once per worker process |
| Conversion masks | 1.0 s | 1% | 1.07M AND gates |
| Everything else in the workers | 2.2 s | 3% | field rounds with triples in stock 0.5 s, local field work 1.0 s, openings, request agreement |

Boolean circuits by kernel: the sealed-sender send 17.7 s (12 runs, 2.18M AND each), the request
frame 3.0 s (0.31M AND each), opening TLS records 2.2 s, GHASH key powers 1.7 s, the TLS handshake
2.2 s in all.

### What each thing costs, by how often it is paid

**Once per worker process (about 8 s):**
- Start-up of both engines and the first conversion masks: 0.6 s.
- Loading circuits: 6.8 s. Each circuit is read, hashed and compared between the parties the
  first time it is used; the 2.2M-gate send circuit alone is over 100 MB of text.
- Field triples and masks start from empty stock.

**Once per connection (about 6 s):**
- TLS handshake: about 5 s, 3.1M AND gates.
- WebSocket upgrade: revealing the response took 8 s at one byte per round trip; in multi-byte
  steps it is about 1.5 s.

**Once per contact per session (about 3 s):**
- Loading its key and state from the database nodes: 0.15 s in the workers plus the database
  client.
- Preparing its curve table and the long-term agreement before the first send: 2.7 s more than a
  later send. Almost all of that is generating about 14,000 field triples; with triples in stock
  it is well under 0.5 s.

**Per message (steady state, about 3.8 s before the fixes below, about 2.5 s after):**

| Step | Time | Notes |
|---|---|---|
| Sealed-sender send circuit | 1.48 s | 2.18M AND |
| Request frame circuit | 0.25 s | 0.31M AND |
| Sealing and opening the TLS records | 0.43 s | 0.25 s + 0.18 s |
| Field work for the ephemeral key | about 0.45 s | about 3,000 triples generated on demand; near zero from stock |
| Revealing the response | 0.2 s | 8 round trips; was 20 or more |
| Controller parsing the response | 1.2–1.6 s | fixed: now about 0.25 s |
| Storing the contact's state before the send | not in this run | one small circuit (0.1 s) plus two database-client runs |

### What can be produced ahead of time

- **Field triples** are independent of what is computed. Every one of the 67,003 products here
  could come from stock: that removes 10.2 s (14%) from this session, 2.1 s per contact and about
  0.45 s per message. Stock costs 72 KB of traffic and 0.15 ms per triple to make.
- **Conversion masks** likewise (1.0 s here; 16 masks per batch).
- **Boolean engine.** The 28.5 s is not split into its preparation and its online part: the engine
  does both inside each circuit run. In authenticated garbling most of the cost is the
  preparation of AND triples, which does not depend on the circuit and could be made while idle.
  That needs engine work and is the largest single opportunity; the size of the gain is not
  measured.
- **Circuits** can be loaded before a session starts, and their hashes compared once per
  deployment rather than per process.
- **A contact's curve table and long-term agreement** could be kept with its stored state
  instead of being recomputed each session (they are secrets derived from that state).

### What is amortized by a long-lived session

Process start, circuit loading, the handshake and the upgrade are about 14 s of the 73 s here and
are paid once however many messages follow. A session that stays up and keeps stock therefore
approaches the per-message cost: about 2.2 s of Boolean circuits and under 0.5 s of the rest.

## The time outside the workers

24.5 s of the 73 s was between worker operations:

| Before | Time | What it was |
|---|---|---|
| each send (12) | 14.0 s | the controller parsing the previous response, byte by byte |
| reveal calls (118) | 2.4 s | the same parsing, between steps |
| joint randomness (18) | 3.2 s | the database client being run (a process per call) |
| request frames (12) | 1.5 s | assembling the request and its base64 in the clear |
| polling (13) | 1.1 s | waiting for the server; 10 ms polls |
| the rest | 2.3 s | connecting, the first key update |

The parsing cost was a defect, not inherent: the controllers run the same Lean parsers that the
circuits are compiled from, on clear values, and three of the byte operations went through
arbitrary-precision arithmetic at run time (a `2 ^ 8` computed as a big-number power for every
constant and complement, and a generic bit replication for every mask). Measured per byte:

| Parser | Before | After |
|---|---|---|
| WebSocket frame | 2.58 ms | 0.19 ms |
| Control queue | 1.87 ms | 0.36 ms |
| Service response | 7.90 ms | 1.36 ms |
| Upgrade response | 1.90 ms | 0.19 ms |

The controllers now use operations proved equal to the originals (`PublicReceive.fast_eq`). The
response parser is still slow because request ids are above 2^63 and its 64-bit arithmetic falls
back to big numbers; that is the next thing to fix there.

## Receiving one new contact's first message: 48 s

| Where | Time | Notes |
|---|---|---|
| Controllers | 14.9 s | parsing 2.2 KB of envelope byte by byte at the old cost; about 2 s at the new one |
| Loading circuits | 12.3 s | the receive circuits, once per process |
| Boolean circuits | 12.0 s | 15.7M AND: the 2.7 KB TLS record 4.5M, unseal 2.5M, session 2.4M, certificate 0.6M, handshake 3.1M |
| Field triples being generated | 7.6 s | 48,808 products: nine key agreements, the certificate signature, the torsion check |
| Everything else | 1.5 s | |

Per first message, with circuits loaded and triples in stock: about 7 s of Boolean circuits
(4.5M AND of it just to decrypt the TLS record that carries the envelope) and about 1 s of field
rounds.

## Reveal steps (done)

Revealing server bytes went from one byte per round trip to as many bytes as are certain to be
revealable: a send session's 261 calls (8.3 s) became 118 (2.7 s). Each call is about 23 ms on
localhost and is a real round trip between the nodes, so over a network this matters more.

## Rounds (not measured here)

Everything above is on localhost. Over a real link the round count matters: a key agreement is
about 255 sequential field rounds, the certificate check about 500, each reveal step one, and
each circuit a constant number. At 20 ms per round a key agreement alone is 5 s. Reducing rounds
(batching independent agreements into the same rounds, which the field programs already allow)
has not been done and is not visible in these numbers.

## Semi-honest mode

Sessions take roughly half as long (2 contacts × 2 messages: about 20 s against 41 s). A
category profile for semi-honest mode has not been taken yet.
