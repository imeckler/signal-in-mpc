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
      establish a session per device, send one message per device.
      **Live against the local server since 2026-11-11** (`check_signal_service_local.py
      --multi-device`, semi-honest and malicious): a recipient links a second device, the next
      send is answered 409, the client refreshes and resends, both devices decrypt, and again in
      the next session with the device list read from the database nodes. Measured: 15.6M AND
      gates and about 45k field products per new device (2–3 s semi-honest, 8–10 s malicious),
      and per message about 6.3M AND gates per unanswered device (MULTI_DEVICE.md, section 6).
  - [x] Bound into the worker (operations 56–63) and the controller; the bundle response's JSON
        confirmed against the local server (no change needed; devices are not in id order, and
        the response needed the controllers' message limit raised from 4,096 to 16,384 bytes).
  - [x] **Post-quantum encapsulation inside the engines**: twelve kernels, 12.5M AND gates per
        new device (`ML_KEM_ENCAPSULATION.md`), run live.
  - [x] No response body is revealed any more (prekey bundles; the device ids in a 409/410).
  - [x] Failure handling (MULTI_DEVICE.md, section 9): a refresh builds the new sessions in a
        scratch slot and replaces the contact's state, in the engines and on the database nodes,
        only when every device verified and the nodes acknowledged the new blob; otherwise the
        contact is exactly as before, gets a result, and the session carries on. A second 409
        is refreshed again (at most twice more). Run live: three devices, a removed device, 410.
  - [ ] More than about five unanswered devices do not fit the one-record request. Splitting
        the request is not cheap (both request kernels seal one TLS record), so it is not built:
        such a contact is reported "retry later" with that reason. Not run (needs six devices).
        A send to more than about four is silent for over 90 s in malicious mode (no keepalive
        inside it); the server then closes the connection, which is now replaced (section 4).
  - [ ] The device kinds stored next to a contact's ciphertext are not authenticated. Harmless
        while every entry is an unanswered session (same size); must be fixed before established
        and unanswered entries are mixed (MULTI_DEVICE.md, section 4).
  - [ ] Circuits whose shape depends on the response (its record size, the request size, the
        stored state size) are produced during the session: about 85 s in the session with the
        refresh. They need producing ahead (section 5 below) or size classes.
  - [ ] **Sessions we start stay unacknowledged** until that device replies, and we ignore
        replies: every message to a linked device is then a first-message-style message (about
        3.5M AND, 1,935 bytes of stored state). Working assumption: accept that cost. Processing
        a reply would need to find the sender's state, and state is keyed by the application's
        u128 id while a sealed message names its sender only by Signal identity, inside the
        encryption. That lookup needs either an index that tells both nodes which id replied and
        when, or an oblivious search over every contact; neither is worth it for this.
  - [x] Stored state is one entry per device (the kinds in the clear after the ciphertext; a
        one-record contact is stored as before); the send request carries one message per device.
- [ ] **What the missing Signal-identity → id mapping rules out.** Each contact's state holds
      its Signal id (so id → identity works and device or identity changes are found when a send
      to that id is rejected), but an incoming message cannot be matched to an id. Consequences
      to handle or document for the application:
  - [x] A contact who rotates their profile key (Signal clients do on blocking): sealed sends
        fail with 401 and cannot be repaired; the id is reported "needs re-signup" and not sent
        to again in the session. Never falls back to unsealed sends (the server would learn who
        the account messages). **A deleted account looks the same**: the Signal server answers a
        sealed send to an account that does not exist with 401, not 404 (deliberately, so that
        it gives no existence check), so the application cannot tell "gone" from "rotated".
  - [ ] Nothing a user sends after signup can be acted on ("stop", replies): unsubscribing goes
        through the application, which sends the delete request.
  - [x] Per-id results in each controller's output, agreed between the two nodes (a digest
        compared through the workers) before they are reported: delivered, delivered after
        device refresh, delivered after identity change, retry later, needs re-signup, gone,
        fault, each with a reason (MULTI_DEVICE.md, section 9).
  - [ ] Getting those results to the application is the daemon's job (section 7).
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
  - [x] The recovery path itself (restart, reload, resume the broadcast) is section 4.
- [x] Message text up to 256 bytes, in four padded size classes.
  - [x] Checked against the client source: 80-byte blocks, but padded to `80k − 1` bytes, not
        `80k` (ours made every envelope 16 bytes longer than any official client's). Matched under
        `SIGNAL_CLIENT_PROFILE=libsignal` (section 8; CLIENT_FINGERPRINT.md (e)).
- [ ] Messages from existing contacts: delivery receipts, replies, repeated first messages
      until we reply, session resets. Today anything that is not a new contact's first message
      is refused and acknowledged. The `receiver` record the receive circuits produce is dropped.
- [x] A contact whose identity key changed (re-registered): accepted automatically (owner's
      decision): found when the next send is refused (410), sessions replaced under the new key
      (`bundle-rebind`, which opens one byte: the key changed), reported "delivered after
      identity change". What this trusts is in `NEEDS_REVIEW.md` section 3: a server that serves
      a bundle under a key of its own is accepted too. If the contact's profile key changed with
      the registration (a reinstall without a backup), the send gets 401 instead: "needs
      re-signup".
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
- [x] **Recovery instead of abort** (2026-11-11; `MULTI_DEVICE.md` section 9, `NEEDS_REVIEW.md`
      section 3). In a send session with the database nodes, what goes wrong for one contact is
      that contact's result and the others continue:
  - [x] Operations scoped to a contact reply with a status instead of making the worker
        terminal (a send that cannot be sealed, stored state that does not open, a device that
        does not verify). Engine and MAC failures, disagreement between the parties and TLS
        records that do not authenticate stay fatal.
  - [x] Statuses: 409/410 refresh and resend (the refresh repeated at most twice); 429 and 5xx
        back off (`Retry-After` when the response has it, else 1, 3, 9 s), the contact moves to
        the end of the queue, three retries; 401 "needs re-signup"; 404 "gone"; anything else
        (413, 428, ...) "fault" with the status.
  - [x] A connection the server or the proxy closed is replaced (new handshake and upgrade on
        that connection, the others kept) and what was in flight is sent again, under new keys:
        a possible duplicate, by the owner's decision.
  - [x] Per-id results agreed by both nodes (section 3 above).
  - [x] After a session that did die: a new session for the same notify reloads every contact
        from the database nodes and sends what was not confirmed. "Confirmed" is a journal line
        on each computation node, counted only when both nodes have it. Guarantee: at least
        once, duplicates possible, never a message key used twice.
  - [ ] A handshake or proxy connect that fails while a connection is being replaced still ends
        the session (the next session resumes). So does a server that sends nothing for 30 s.
  - [ ] The journal is a file per node named by the test harness; the daemon (section 7) must
        own it, bound its size, and take the notify's id from the application's signed request.
  - [ ] A contact that is not on the database nodes, or not readable until their next epoch,
        still ends the session at load; it should be that id's result.
  - [ ] No test with a cheating party.
- [ ] Keepalives while a long engine operation is running (sent between the steps of a
      refresh; not inside one send to many devices, and not on connections that wait while
      another is in use: such a connection is closed by the server after 90 s and is now
      replaced when next used, at the cost of a handshake).
- [ ] Do not wait for each response before the next send (pipelining), and allow several
      connections. (Several connections: done, one per Tor circuit, section 8; sends still wait
      for each response, one connection at a time.)
- [ ] Agreed time is the later of the two clocks if within two minutes; decide the production
      rule (NTP assumptions, what happens on disagreement).

## 5. Circuits ahead of time (blocker for a real run)

Inventory of every kernel family, what fixes each parameter, the tools and the numbers:
`handshake_backend/EmpHybridWork/CIRCUIT_SHAPES.md`.

- [x] Generate every circuit a deployment can need before it starts, with a pinned manifest both
      parties check: `scripts/produce_circuits.py DEPLOYMENT.json OUT` (names from the Lean
      executable `circuit_inventory`, one kernel at a time under a memory cap, resumable), and
      strict mode in the worker (`CIRCUIT_MANIFEST`: only the manifest's kernels, never produces,
      manifest hash compared before the first kernel, a name outside it is refused). Checked by
      `check_signal_service_local.py --strict`.
- [x] TLS application records, sealed public-size contents and prekey response bodies are in size
      classes (four per doubling; the true length is a value the circuit enforces), proved equal
      to the exact-size kernels. `bundle-device` no longer depends on the response's size or the
      item's offset (`bundle-item`).
- [ ] **(blocker)** Measure the real server's handshake record sizes (`tls-open-handshake` is per
      size; if they vary between connections it needs classes too).
- [ ] **(blocker)** Signup shapes are enumerated, not classed: sender certificate lengths, prekey
      id widths, client version (addresses field, post-quantum field size). A signup outside the
      listed shapes is refused. Either measure and list what real clients send, or give the
      receive kernels capacities (a rewrite of `ReceiveFirst` and its proofs).
- [ ] Multi-device: digit counts of a bundle's numbers (`bundle-item`) and the per-combination
      request frame (`bundle-request-ctr`) still multiply; fixes are described in
      CIRCUIT_SHAPES.md ("Not done" 3 and 4).
- [ ] A manifest belongs to one emitter binary; decide how a deployment ships it (the gate lists
      are several GB) and add a binary gate-list form to cut loading time.
- [ ] Remove the Python wrapper from the runtime (`circuit_cache.py`: it now only names, hashes
      and caches what the Lean executable writes). The older non-kernel modes still use the
      unverified Python lowering; no worker uses them: delete or port.
- [ ] Our own sender certificate's length is a deployment constant (`certificate`); if the server
      issues another length on refresh, every kernel that takes it must exist for that length too
      (a second deployment description, produced ahead).

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
- [ ] **Being recognisable is separate from being located.** Whatever the exit. Comparison,
      reference and ranking: `handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md` (model client
      Signal-Android; reference derived from libsignal v0.106.1 and BoringSSL source, because
      libsignal-net cannot be built here: BoringSSL is not vendored). Everything marked done is
      behind `SIGNAL_CLIENT_PROFILE=libsignal` (the default stays `legacy` until the harness's
      `--fingerprint` stage passes; then flip `officialProfile`).
  - [ ] **Regression check:** `check_signal_service_local.py --fingerprint` captures our
        ClientHello, upgrades and frames (`scripts/fingerprint_terminator.py`) and compares them
        with `local_signal_server/fingerprint/reference/` (fails on any difference outside its
        allow-list). Replace the synthetic reference with a real libsignal capture once BoringSSL
        is vendored (CLIENT_FINGERPRINT.md, first section).
  - [x] ClientHello: BoringSSL's extension order, 32-byte session id, TLS 1.0 first-record
        version, libsignal's signature algorithms, `psk_dhe_ke`.
    - [ ] **Needs new capability:** TLS_AES_256_GCM_SHA384 (SHA-384 key schedule; medium),
          TLS_CHACHA20_POLY1305_SHA256 (Poly1305 mod 2^130−5; large), P-256/P-384 groups
          (large). Without them the cipher count and JA3/JA4 still differ.
  - [ ] **Needs new capability: HTTP/2.** Since libsignal v0.97.1 (2026-07) official clients
        connect to `grpc.chat.signal.org` with ALPN h2 and run the WebSocket over HTTP/2
        extended CONNECT; HTTP/1.1 to `chat.signal.org` is now only an out-of-date client's (or
        a proxied one's) route. Specified in CLIENT_FINGERPRINT.md (c).
  - [ ] Client Finished seconds after the server's flight (two-party key schedule): visible to
        the server and any observer; only faster handshake circuits help.
  - [ ] **Payloads too: the server terminates TLS and sees every request in full.**
    - [ ] Request ids count up from 2^63 (libsignal: 0 per connection). Not fixed: each id
          varint width is another request-kernel shape (size classes); specified in
          CLIENT_FINGERPRINT.md (d).
    - [ ] The send request's JSON pads the device id and registration id with spaces. Replacement
          specified, not built (CLIENT_FINGERPRINT.md (d)): canonical digits at a private length
          inside a fixed-size, TLS-padded record; reveals nothing new to the nodes (revealing the
          digit counts would leak 1.28 bits of each contact device's registration id).
    - [x] Field order of the request JSON (libsignal's), no `?story=false`; request protobuf field
          order and headers already matched.
    - [x] Upgrade requests: libsignal's header order and case, `uuid.1` username, Signal-Android
          user agent (`RelayUpgrade.userAgent`, a deployment constant to keep current), no
          `accept-language`, stories header only on the authenticated socket.
      - [ ] Owner's decision: `x-signal-receive-stories: false` (most Android users send `true`;
            `true` makes the server deliver stories, which we would refuse).
    - [x] Content padding `80k − 1` (it was `80k`: every envelope 16 bytes off). Size classes:
          `signal-seal-official`, `bundle-seal … 80k−1`; `CircuitInventory` does not list them yet.
    - [ ] Data-message fields (Android adds expireTimer 0, isViewOnce false, expireTimerVersion,
          profileKey): not added; the server sees only lengths, and `expireTimer` could reset a
          recipient's disappearing timer. Owner's decision.
    - [x] Timestamps: each message stamped from the agreed clock when first sent, increasing,
          kept on a resend (was base + recipient index, built ahead).
    - [x] No client-initiated TLS KeyUpdate.
    - [x] Keepalive on the receive socket: WebSocket ping after 31 s idle, as libsignal.
      - [ ] The send session's keepalive during a device refresh and the last keepalive of a
            receive session are still `GET /v1/keepalive` requests; no WebSocket Close at the end.
    - [ ] Behaviour over time: never fetching profiles or syncing, never sending receipts
          (deliberate, still a pattern); one session per broadcast. Cheap and allowed: refresh
          the sender certificate and check prekeys on the authenticated socket periodically.
  - [ ] Few Signal clients arrive from Tor exits, so sealed messages arriving over Tor in one
        window are easy to attribute to one sender even on separate circuits. Exits that
        ordinary users also arrive from would be less conspicuous; the SOCKS mechanism is the
        same.
  - [ ] Spread a broadcast in time (random delay and order per recipient). The owner decides
        how much delivery latency is acceptable.
- [ ] **Tor as the proxy** (concrete option, in progress): the node that opens the TCP socket
      connects through a local Tor client by SOCKS5 with the hostname passed through; the TLS
      session inside stays end to end, so the exit sees only ciphertext and nothing else in the
      design changes. To unlink recipients, one circuit (so one TLS connection and handshake,
      about 5 s and 3M AND gates today) per recipient or per small group. Does not hide the
      burst timing of a broadcast (needs delays and shuffling) or which account the receive
      socket belongs to. Unknown until tried on the real service: how Signal treats Tor exits
      for this traffic.
  - [x] SOCKS5 in the leader (`tls_worker_v3.cpp`, `socks_connect`): username/password only,
        the server asked for by hostname (address type 3), so no node resolves it; the proxy's
        own address must be numeric. The credentials choose the circuit (Tor's default
        `IsolateSOCKSAuth`): username `tls-mpc-<first 16 hex of the session id>` (fresh per
        session), password `send-<i>-of-<N>` or `receive`. The other node opens nothing. The
        proxy, credentials and count are in the agreed connect request, so a node configured
        without the proxy or with another count aborts the session.
  - [x] Configuration: `SIGNAL_TOR_SOCKS=IP:PORT` and `SIGNAL_TOR_CIRCUITS=N`, the same on both
        nodes (top of `PublicServiceController.lean`). N = 0 (default): one direct connection,
        as before. N ≥ 1 (at most 16): N send connections, each its own TLS session and
        unauthenticated WebSocket on its own circuit, opened up front; the receive socket is one
        connection on a circuit of its own.
  - [x] Several connections in one worker: a connection table selected by a public index
        (operation 90, `TlsWorker.onConnection`; 0 when never selected, so existing callers are
        unchanged). Per connection in the worker: socket, handshake phase, TLS secrets, record
        parser, GHASH key-power shares, WebSocket state; in the controller: the TLS session
        (record sequence numbers), the response parser and the request-id counter. Shared:
        engines, circuits, conversion masks, private buffers, contacts, the account.
  - [x] Assignment (`Circuits.assign`): the session's distinct ids in ascending order, rank r on
        connection r mod N. A contact stays on one connection for the session; the same set of
        ids is split the same way in every session. The state is still stored before each send.
  - [x] A dropped circuit is reported to both parties at the same request (the leader tells
        the other node, so neither waits). With the database nodes the connection is then
        replaced and the session goes on (below); without them, or with `SIGNAL_RECOVERY=0`, the
        session ends cleanly and the next one carries on from the stored state.
  - [x] Tested locally only, never with Tor: `local_signal_server/scripts/socks5_test_proxy.py`
        and `check_signal_service_local.py --circuits 1,3` (with and without `--db`; the drop
        test needs `--db`). Costs: `PERFORMANCE.md`, "Tor circuits".
  - [ ] What the server can still link: recipients on one connection; the whole broadcast by
        timing (N handshakes together, then sends alternating one response at a time, no delay
        or shuffling); the request-id scheme (each connection counts from 2^63, so nothing
        interleaves, but every connection starts the same way; a device refresh's own requests
        use one session-wide counter); and the receive socket names the account.
  - [ ] Idle connections: each connection waits while the others handshake and send, and the
        server drops a socket silent for 90 s. Fine for a few circuits; one circuit per recipient
        of a large broadcast needs keepalives on idle connections, pipelining (section 4), or
        opening connections in batches.
  - [x] Recovery instead of ending the session on a dropped circuit (section 4): that connection
        is replaced (a new handshake, the same SOCKS credentials, so Tor decides whether it is
        the same circuit or a new one) and what was not answered is sent again; the other
        connections are kept. `check_signal_service_local.py --recovery drop`.
  - [ ] A Tor client on the leader node (deployment, section 9): its SOCKS port only on
        localhost, no DNS for the Signal host on the node.
  - [ ] Only a run against the real service can show (needs the owner's explicit go-ahead):
        whether Signal blocks or rate-limits (429, challenges) Tor exits for these requests,
        circuit build times and failures, and the real latency per circuit.

## 9. Deployment

- [ ] **(blocker) Deployment design** (decided by the owner on 2026-11-11: WireGuard between
      nodes; each computation node with a different cloud provider; the database nodes split
      across several providers):
  - [ ] **WireGuard between the two computation nodes**, and from each computation node to the
        database nodes. The engines' links (plain TCP to 127.0.0.1 today, on several ports per
        worker) then run inside the tunnel; the workers need to take the peer's address from
        configuration instead of assuming localhost. Decide whether WireGuard alone is the
        authentication between the nodes or the engines also authenticate each other.
  - [ ] **Choosing the two providers for the computation nodes.** What matters, from the
        measurements in `PERFORMANCE.md`:
    - [ ] *Round-trip time.* A contact's first send is about 2,800 sequential rounds and a
          first message received about 11,500; each round is one round trip between the nodes.
          At 1 ms that is 3 s and 12 s; at 10 ms it is 28 s and 2 minutes, past the Signal
          server's 90 s idle limit. The two providers need data centres in the same metro area
          with a short path between them (ideally 1-2 ms). Measure before committing.
    - [ ] *Traffic price.* Malicious mode sends on the order of 1 GB between the nodes per
          message (about 270 bytes per AND gate and 72 KB per field triple; a 12-send session
          was about 15 GB). At typical cloud egress prices that is cents per message, so
          providers with free or very cheap egress, or a private interconnect between the two,
          are worth more than cheap compute. Semi-honest mode sends far less.
    - [ ] *Bandwidth.* At 1 GB per message, a 1 Gbit/s link caps throughput near one message
          per 8 s per pair of nodes regardless of CPU; 10 Gbit/s links matter.
    - [ ] *Jurisdiction* (owner's criterion): the two providers ideally in separate legal
          jurisdictions, or at least ones that do not comply with extra-legal requests from
          intelligence services; likewise for how the database nodes are spread. Both the
          company's place of incorporation and the data centre's location count. This pulls
          against "same metro": look for providers incorporated in different countries sharing
          a metro, or cross-border metro pairs a millisecond or two apart, and know what
          latency full separation costs. Research in progress: `deployment/PROVIDERS.md`.
    - [x] Shortlist candidate pairs: `deployment/PROVIDERS.md`. **Decided: Helsinki + Tallinn**
          (jurisdiction first; about 2.0-2.2 ms round trip measured one way from public probes).
    - [ ] Still to verify for that pair by renting and measuring inside WireGuard, both
          directions, at several times of day: median and 99th-percentile round trip, sustained
          throughput, and for Tallinn the available hardware, 10 Gbit/s ports and traffic price.
    - [ ] At 2 ms the sequential round counts dominate (2,800 rounds for a contact's first send,
          11,500 for a first message received): batching and stored per-contact tables are in
          progress; see `PERFORMANCE.md`, "Rounds".
  - [ ] **Splitting the five database nodes across providers.** Three shares reconstruct a
        contact's key, so no single provider (and no realistic pair) should host three nodes;
        and since each computation node already holds one additive share of what it reads,
        decide whether a computation node's provider may also host database nodes, and how
        many. Their traffic is small; latency between them matters only for their own epochs.
  - [ ] Where the application server sits, and how it reaches both computation nodes and the
        database nodes.
- [ ] **(blocker) Automated deployment.**
  - [ ] Infrastructure as code for all seven machines across the providers: instances,
        firewalls (only WireGuard and the outbound Signal/proxy connections), WireGuard keys
        and peers, time synchronisation.
  - [ ] Reproducible builds of the workers, controllers and database nodes, with the pinned
        circuit manifest (section 5) and its hash compared between the nodes at start.
  - [ ] A key ceremony that generates each machine's keys on that machine (WireGuard, database
        client and node signing keys, the application's notify and signup keys) and assembles
        the shared network configuration, with no party ever holding another's private key.
  - [ ] Account creation as part of deployment (section 2), then the account row on the
        database nodes.
  - [ ] Rolling upgrades: both computation nodes must run the same build and manifest;
        database protocol version changes need all nodes together.
  - [ ] Monitoring and alerts that never log shares or revealed tags beyond what is public;
        backups of the database nodes; a runbook for losing one node of each kind.
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
  - [x] The response parser's 64-bit operations computed directly (`Word64.fast`, proved equal):
        1.2 ms → 0.74 ms per byte. The rest is in its byte-mask folds and stack rewrites.
- [x] AND triples and field triples produced ahead of use by background pools of the session
      (`TLS_WORKER_TRIPLE_STOCK`, `TLS_WORKER_FIELD_STOCK`): 2.4 s → 1.0 s per message.
  - [ ] Conversion masks are still made when a batch runs out (0.6 s per session).
  - [ ] More factories on real nodes; a sustained broadcast of hundreds of messages is unmeasured.
- [x] Circuit loading 10.6 s → 2.1 s per process; record opening 1,500 → 935 AND per byte.
- [ ] Prepare several contacts in the same field rounds (2,800 sequential rounds per contact now).
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

## 12a. Less C++, more Lean (queued: starts only after the application works end to end)

Order set by the owner on 2026-11-11: first finish the orchestration blockers (sections 4, 6
and 7: recovery, the node daemons and the application's requests, the real database nodes) so
there is a functioning application end to end including the database nodes; then this.

The C++ is dense and hard to audit. Decided by the owner on 2026-11-11: move what can move
into Lean and prove what is useful about it.

- [ ] **A generic engine server.** The worker keeps only a small instruction set: run a named
      circuit on named handles, open an output Lean marks public, convert between engines,
      evaluate a field program, take a private input, draw joint randomness, exchange bytes,
      checked field openings. One agreed batch of instructions per operation (not one round
      trip per instruction).
- [ ] **All sequencing as Lean scripts** (`service_kernels.h`, `tls_kernels.h`: send, receive,
      device refresh, account and contact state, TLS handshake and records). Theorems for the
      main flows:
  - [ ] composition: the script's result equals the flow's specification (closes "the kernels
        as wholes carry no theorem");
  - [ ] disclosure: a script opens only outputs marked public, and no private handle reaches an
        opening any other way;
  - [ ] ordering: for example, a contact's state is stored before its message leaves.
- [ ] **The conversion and helper protocols as Lean scripts too** (`dyn_word_mask.h`,
      `x25519_fast.h`, `edwards_points.h`, `gcm_shares.h`, `split_ecdh.h`): the cut-and-choose
      for word masks and bit pairs, word/field conversion, masked inversion, the offset key
      agreement, GHASH key-power shares. Their arithmetic is already Lean circuits and field
      programs; what moves is the orchestration (which candidates are opened, compared,
      bucketed; which values are opened; when to abort). To prove, relative to an ideal model
      of the two engines:
  - [ ] correctness of an honest run (a mask is the same value in both engines; a conversion
        returns the value it was given; the masked quotient is x/z; the tag shares sum to the
        GHASH tag);
  - [ ] hiding: each opened value is a bijective function of a fresh uniform mask, so it is
        independent of the secret (and a mask is consumed exactly once, enforced by the script's
        types rather than a runtime flag);
  - [ ] detection: every way a single deviating input is caught, as lemmas; and, as the
        stretch goal, the cut-and-choose counting bound for the parameters in use (statistical
        128) proved rather than computed by a script.
  - Not covered by any of this: that the engines themselves implement their ideal behaviour
    (see `NEEDS_REVIEW.md`).
- [ ] Public-data pieces still in C++ (commit-and-open, the WebSocket accept value, public
      curve arithmetic through a C library) into Lean.
- [ ] **The remaining shell in Rust**: pipe protocol, sockets and SOCKS, connection table,
      loaders. Engines stay C++ behind a narrow interface.
- [ ] Reformat whatever C++ is left.

## 13. Housekeeping

- [ ] Nothing is pushed (`tls-mpc`: `two-party-hybrid-worker`; `secret-shared-db`:
      `two-party-handoff`, `two-party-handoff-signup-tool`).
- [ ] `REMAINING_WORK.md` predates most of this and is out of date.
- [ ] The database client is built from a checkout at `.deps/secret-shared-db-handoff`.
