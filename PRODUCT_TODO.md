# What is left before this is a working product

Written 2026-11-11 on branch `two-party-hybrid-worker`. The product: an application server calls
`notify(ids, message)`; two computation nodes, neither of which can read the contact list or act
alone, send that message over Signal to each contact; new users sign up by sending the account a
Signal message containing a signup token. Contact keys and state live on five database nodes
(`secret-shared-db`).

Measured costs and what can be precomputed or amortized are in `PERFORMANCE.md`.

Order: sections are roughly in the order the work has to happen. Within a section, items marked
**(blocker)** stop a first real run; the rest can follow.

## 0. What already works (for orientation)

Checked against the real Signal-Server code running locally, in malicious and semi-honest mode
(`local_signal_server/check_signal_service_local.py --signup --db`):

- TLS 1.3 handshake and records, WebSocket upgrade (authenticated socket with an XOR-shared
  password; unauthenticated socket for sends), keepalive, server requests answered.
- Sealed-sender sends to contacts by id; contact state sealed, stored and reloaded.
- Receiving a stranger's first message (sealed sender, PQXDH responder), creating the contact
  under the id its signup token names, acknowledging only after the state is stored.
- Contact keys and state on five database nodes: deal, read with the parity check, versioned
  blobs under the application's signed request or signup token.
- Every circuit defined in Lean; gate lists produced by a Lean lowering with a soundness proof.

## 1. Decisions

Still open:

- [ ] **Go-ahead for the first run against Signal's real service** (ban risk for malformed
      traffic; everything so far is local).

Decided by the owner on 2026-11-11 (each is now work, listed in its section):

- **Database write authority:** a read's signed request also authorises the matching write-back.
- **Signups are always sealed sender.** The account accepts sealed messages from anyone;
  unsealed first messages are not supported.
- **Signup token is fixed width:** the user pastes a base64 string.
- **Later messages from contacts are ignored for now, and no read or delivery receipts are ever
  sent** (they de-anonymise through timing).
- **Message text: at least 200 bytes** (was 48).
- **Delete:** the application server sends a signed "delete" request with a list of ids.

## 2. The account itself (blocker for a real run)

Today the account is created by a conventional client and its identity key is entered into the
session by one party (test admission). For the product no one may ever hold the identity key.

- [ ] **(blocker)** Generate the identity key as a shared scalar (both parties contribute; the
      public key comes from the existing ladder) and register the account from inside the
      two-party session, or accept a one-time trusted setup and document it.
- [ ] **(blocker)** Store the account record (identity key shares, password shares, sender
      certificate, registration ids) on the database nodes under a reserved id, so the
      computation nodes persist nothing usable alone. Today it comes from a JSON export file.
- [ ] **(blocker)** Refresh the sender certificate before it expires (`GET /v1/certificate/delivery`
      on the authenticated socket).
- [ ] Sign prekeys with the shared identity key (XEdDSA signing in the engines, or a ceremony):
      needed to rotate the signed prekey and the Kyber last-resort key. Not needed day one.
- [ ] Replenish one-time prekeys (unsigned upload on the authenticated socket). Signups work
      without them, with slightly weaker forward secrecy for the first message.
- [ ] Persist our prekey private keys (held in the clear by both nodes, by decision) somewhere
      durable and access-controlled; today they are in the export file.
- [ ] Kyber decapsulation outside the engines uses the test tool `lss-provision kem-decapsulate`;
      replace with a small audited binary or the Lean ML-KEM definition run natively.

## 3. Signal protocol coverage

- [ ] **(blocker) Contacts with more than one device.** Sends go to device 1 only. A real user
      with linked devices makes the server answer 409 (missing devices). Needed: handle 409/410,
      fetch prekey bundles, and establish outbound sessions per device (the establish kernels
      exist but are not connected, and the ML-KEM encapsulation circuit is about 190M AND gates:
      decide whether encapsulation may happen outside the engines).
- [ ] **(blocker) Crash safety of contact state.** State is written back once, at the end of a
      session. If a session dies after sending, the stored state is stale and the next session
      reuses message keys and counters. Needed: write the advanced state (or reserve a range of
      counters) before messages go out, and a recovery path that reloads from the nodes.
- [ ] Messages from existing contacts: delivery receipts, replies, repeated first messages
      until we reply, session resets. Today anything that is not a new contact's first message
      is refused and acknowledged. The `receiver` record the receive circuits produce is dropped.
- [ ] A contact whose identity key changed (re-registered): detect and re-establish.
- [ ] Several messages waiting at connect time; more than one envelope in a TLS record (handled
      in the parser, not yet tested).
- [ ] Non-text first messages, or a first message without a profile key: refused today.
- [ ] Certificate validation of the sealed-sender *server* certificate against the trust root is
      done by the test export tool; do it in the controllers (public values, the Lean XEdDSA
      definition run natively).
- [ ] Unsealed (type 3) first messages, only if section 1 decides to accept them.

## 4. Connection lifecycle and failure handling

- [ ] **(blocker)** One long-lived session that both receives and sends. Today a session either
      sends (unauthenticated socket) or receives (authenticated socket) and then exits.
- [ ] **(blocker)** Recovery instead of abort: any rejected operation is terminal for the worker.
      Needed: tear down, restart, reload state from the database nodes, resume the broadcast
      where it stopped, never resend under old keys.
- [ ] Keepalives while a long engine operation is running; reconnect when the server drops the
      socket; handle server-initiated closes and HTTP error statuses (401, 404, 409, 410, 413,
      428, 429 with back-off).
- [ ] Do not wait for each response before the next send (pipelining), and allow several
      connections.
- [ ] Agreed time is the later of the two clocks if within two minutes; decide the production
      rule (NTP assumptions, what happens on disagreement).

## 5. Circuits ahead of time (blocker for a real run)

- [ ] **(blocker)** Generate every circuit a deployment can need before it starts, with a pinned
      manifest both parties check. A first message of a new size currently makes the worker
      produce new circuits while the server waits (over a minute), and the socket drops.
- [ ] Remove the Python wrapper from the runtime (`circuit_cache.py`: it now only names, hashes
      and caches what the Lean executable writes). The older non-kernel modes still use the
      unverified Python lowering; no worker uses them: delete or port.
- [ ] Bound the set of shapes: fixed-width signup token, padding classes for envelopes, the
      certificate lengths the server issues.

## 6. Database nodes (`secret-shared-db`, branch `two-party-handoff`)

Done: the controllers run `handoff_client` for read / parity / combine / deal / write-blob, checked
with five in-memory test nodes.

- [ ] **(blocker)** Run against the real node binary with Postgres. The compute path's Postgres
      code has never been run against a database; the checked-in configs lack the compute
      fields; docker-compose ports and `init.sql` do not match the generated configs.
- [ ] **(blocker)** A new contact becomes readable only after the next epoch (120 s). The flow
      must tolerate "not readable yet" for contacts created moments ago.
- [ ] Notify request lifetime (section 1).
- [ ] Signup tokens carry no nonce or expiry (replayable); a late or replayed second deal can
      leave nodes with different polynomials (detected at read, not repairable).
- [ ] Delete; repair of lagging nodes; the cap of 64 unauthenticated connections (denial of
      service).
- [ ] Check the node-signed reports for blobs between the parties (the parity file carries
      them; the worker already requires both parties to present the same blob).
- [ ] Merge the helper branch `two-party-handoff-signup-tool` (adds `handoff_client sign-signup`),
      and give the application server a real tool for signup tokens and notify requests.
- [ ] Migrate the relay node to the 2^255-19 share field (existing databases are incompatible).
- [ ] Optional: store state natively as field shares instead of an encrypted blob.

## 7. The application-facing service

- [ ] **(blocker)** A daemon on each computation node that accepts the application's signed
      `notify(ids, message)` request (today: environment variables and a test harness), checks
      the signature, and drives a session.
- [ ] Batching and scheduling for thousands of ids; progress and per-id results back to the
      application (delivered / unknown contact / failed), without revealing more than agreed.
- [ ] Signup results back to the application (which id signed up), and the reply to the user
      that the existing relay design sends.

## 8. Privacy: the proxy

- [ ] Send through a proxy (or several exit addresses) so the Signal server cannot link a
      broadcast's recipients by source address and timing. Decide: who runs it, one connection
      per recipient or per batch, added delay and shuffling. Not started, by instruction.
- [ ] Review what timing reveals even with a proxy (burst of sends after each notify).

## 9. Deployment

- [ ] **(blocker)** The two computation nodes on separate machines with an authenticated,
      encrypted channel between them. The Boolean engine's link is plain TCP to 127.0.0.1 today.
- [ ] Production security parameters: the field engine is built with a statistical parameter of
      40 unless overridden (`EMP_HYBRID_NATIVE_SECURITY`); the product profile is 128. Confirm
      every build flag for the malicious/128 profile.
- [ ] Erasure on retire and abort (the worker drops handles; it does not prove erasure).
- [ ] Secrets at rest on each node (database client key, prekey private keys), file permissions,
      and logs that never contain shares (test tooling prints them).
- [ ] Process supervision, configuration, monitoring, memory limits (the guard script is a
      test aid), behaviour over a real network (round counts: a key agreement is about 255
      sequential rounds).

## 10. Security review and proof debt

- [ ] `secure_hybrid_backend` stays false until the engine combination is reviewed: the
      Boolean engine, the field engine, and the conversions between them (cut-and-choose
      parameters for word masks and the new bit pairs).
- [ ] Tests with a cheating party for what was added recently: bit pairs on the runtime-sized
      layer, the receive path, the database flow (tampered share, differing blobs).
- [ ] The controllers' reveal policy (`PublicReceive.budget`, `mayReveal`): state and prove that
      no byte of a request body or of an unknown message is ever revealed.
- [ ] C++ that is logic rather than plumbing: GHASH share helpers, swap-bit derivation, the
      receive sequencing's shape parsing. Move to Lean or review.
- [ ] Not proved: the kernels as wholes (parts carry theorems), the gate-list printer and layout
      text, that the Edwards formulas are the group law, agreement with libsignal beyond tests.
- [ ] Leakage through aborts and timing: a refused message, a failed parity check, the time an
      operation takes.

## 11. Performance work (see `PERFORMANCE.md` for the numbers)

- [x] Reveal server bytes in multi-byte steps (was one round trip per byte).
- [ ] Produce field triples and conversion masks ahead of time (idle time, or a pool), so sends
      use stock.
- [ ] Keep a contact's per-session setup across sessions (it is recomputed at each load).
- [ ] One long-lived connection: the handshake and upgrade are paid once, not per broadcast.
- [ ] Send without waiting for each response; several contacts in parallel.
- [ ] Fewer AND gates in the send and record circuits (AES, SHA-256, large-record opens).
- [ ] Measure over a real network between two machines.

## 12. Testing still owed

- [ ] Rerun the older fixture checks (`check_tls_worker_v3.py`, `check_tls_application_v3.py`,
      `check_signal_service_v3.py`) after the recent worker changes.
- [ ] An official Signal client as the recipient and as the new user.
- [ ] Thousands of contacts; hours-long sessions; reconnects; database node faults.
- [ ] Then the real service, with one test account, at low volume.

## 13. Housekeeping

- [ ] Nothing is pushed (`tls-mpc`: `two-party-hybrid-worker`; `secret-shared-db`:
      `two-party-handoff`, `two-party-handoff-signup-tool`).
- [ ] `REMAINING_WORK.md` predates most of this and is out of date.
- [ ] The database client is built from a checkout at `.deps/secret-shared-db-handoff`.
