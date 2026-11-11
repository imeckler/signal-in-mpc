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
      with linked devices makes the server answer 409 (missing devices). Designed, with circuits
      written, proved and checked offline (`handshake_backend/EmpHybridWork/MULTI_DEVICE.md`,
      `TlsMpc/BundleKernels.lean`): fetch the contact's whole prekey bundle, parse it privately,
      establish a session per device, send one message per device. Still to do:
  - [ ] Bind it into the worker and controller (the list is in MULTI_DEVICE.md, section 7), and
        confirm the bundle response's exact JSON against the local server.
  - [ ] **Post-quantum encapsulation inside the engines.** It cannot be done in the clear (the
        contact's Kyber key is the same for every caller, so a node could test who is a
        contact). The existing circuit is about 190M AND gates per new device; a version with
        arithmetic for the Kyber modulus is estimated at 15-20M (not measured). Needs building.
  - [ ] **Sessions we start stay unacknowledged** until that device replies, and we ignore
        replies: every message to a linked device is then a first-message-style message (about
        3.5M AND, 1,935 bytes of stored state). Working assumption: accept that cost. Processing
        a reply would need to find the sender's state, and state is keyed by the application's
        u128 id while a sealed message names its sender only by Signal identity, inside the
        encryption. That lookup needs either an index that tells both nodes which id replied and
        when, or an oblivious search over every contact; neither is worth it for this.
  - [ ] Stored state becomes one record per device; the store format and the send request
        (one message per device) change accordingly.
- [ ] **What the missing Signal-identity → id mapping rules out.** Each contact's state holds
      its Signal id (so id → identity works and device or identity changes are found when a send
      to that id is rejected), but an incoming message cannot be matched to an id. Consequences
      to handle or document for the application:
  - [ ] A contact who rotates their profile key (Signal clients do on blocking): sealed sends
        fail with 401 and cannot be repaired; report the id as needing to sign up again. Never
        fall back to unsealed sends (the server would learn who the account messages).
  - [ ] Nothing a user sends after signup can be acted on ("stop", replies): unsubscribing goes
        through the application, which sends the delete request.
  - [ ] Report per id to the application: delivered, device list refreshed, unreachable (404),
        needs re-signup (401).
- [ ] **A Signal-identity → id index, if incoming messages from existing contacts are ever to be
      acted on** (not started; needs the owner's go-ahead on the visibility it adds). Design:
  - [ ] Tag = one AES block of the sender's 16-byte Signal id under a key that exists only in
        the shared account record (generated jointly, stored sealed on the database nodes).
        Computed inside the Boolean engine, about 6,000 AND gates, from the id that comes out of
        the verified sender certificate; only the tag is opened. Neither node can compute a tag
        itself, so neither can test whether a given person is a contact, and neither can make
        the engines tag an id of its choosing.
  - [ ] The table lives on the database nodes, not the computation nodes: a tag column on the
        contact's row. Written at signup together with the deal and first blob (accepted only
        when both parties submit the same tag); looked up on an incoming message by each party
        from all five nodes, taking the id enough of them agree on; needs no application
        request, like the account row; removed by delete.
  - [ ] What it adds to what is visible: the computation nodes and the database nodes learn
        which id an incoming message came from and when. Nothing about who the person is.
  - [ ] The same person signing up twice gives the same tag, so the nodes see that two ids are
        one person. Proposed: the new id supersedes the old (re-signup is the recovery path for
        a rotated profile key).
  - [ ] It only finds the state. Acting on a message also needs circuits for receiving on an
        existing session (the `receiver` record the first-message circuits already produce).
  - [ ] What it would unlock: "stop" by Signal message, repairing a rotated profile key from
        the contact's next message, and marking a linked device's session acknowledged (about
        1.3M AND gates saved per message to that device).
- [x] **Crash safety of contact state.** With the database, a contact's advanced state is stored
      and acknowledged before its message leaves.
  - [ ] The recovery path itself (restart, reload, resume the broadcast) is section 4.
- [x] Message text up to 256 bytes, in four padded size classes.
  - [ ] Signal's own clients may pad content to 160-byte blocks, not 80: check against the
        client source and match it ("send what a normal client sends").
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
with five in-memory test nodes. Also done and checked the same way (node changes are on branch
`two-party-handoff-signup-tool` of `secret-shared-db`): a read's request authorises the later
write-back; the application's signed delete request, submitted by both parties; the fixed-width
signup token (108 characters of base64) naming the contact's id; "dealt but not yet readable"
reported separately from "missing"; and the account's own row (identity key, password,
certificate) under a reserved id that the two parties may read and write without an application
request, loaded by send and receive sessions. A first Postgres test of the compute path passes
(one node). Decided there, for the owner to confirm: a deleted id cannot be dealt again; one
party can block a delete by not forwarding it.

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
- [ ] **Tor as the proxy** (concrete option, not started): the node that opens the TCP socket
      connects through a local Tor client by SOCKS5 with the hostname passed through; the TLS
      session inside stays end to end, so the exit sees only ciphertext and nothing else in the
      design changes. To unlink recipients, one circuit (so one TLS connection and handshake,
      about 5 s and 3M AND gates today) per recipient or per small group. Does not hide the
      burst timing of a broadcast (needs delays and shuffling) or which account the receive
      socket belongs to. Unknown until tried on the real service: how Signal treats Tor exits
      for this traffic.

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
- [x] Controller parsing of revealed bytes about 6.5x faster (it was a third of a session).
  - [ ] The response parser's 64-bit arithmetic still falls back to big numbers (request ids are
        above 2^63): 1.4 ms per byte.
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
