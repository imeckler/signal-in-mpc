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

**The registration ceremony** (2026-11-11; design, value table and threat discussion in
`CEREMONY.md`; review items in `NEEDS_REVIEW.md` 3c). Scope set by the owner the same day: only
the password must be secret-shared; the account's keys may be in the clear on the nodes.

- [x] The account password is made inside the engines from both nodes' randomness, enters
      `POST /v1/registration` only there, and each node keeps an XOR share in the form sessions
      already take (kernels `ceremony-secrets`, `ceremony-register-ctr`; worker operations 80, 81).
      The recovery password likewise (its shares are two files; nothing reads them yet).
- [x] `public_service_controller ceremony NODE_CONFIG NAME register|certificate|store`, run on
      both nodes: verification session, captcha (from a file), SMS code, registration; then the
      authenticated socket from the shares, the sender certificate, one-time prekeys; then the
      account's row on the database nodes. A record of every request and response on each node.
- [x] `check_signal_service_local.py --runs 0 --ceremony`: the ceremony against the local server,
      then a signup received and a broadcast sent with the result; semi-honest and malicious pass.
- [ ] **(blocker for a real run) Owner's decisions**, `CEREMONY.md` section 8: the verified
      session id is public to both nodes, so either can register the number alone while it
      lives (fix designed: keep the id in the engines); the identity private key in the clear
      lets a node colluding with the Signal server read who signs up; who holds the SIM;
      registration lock; password length 22 vs the official 24.
- [ ] Username (reserve and confirm on the authenticated socket). Not started.
- [ ] Replace the export file as the carrier of the keys and public account between the
      ceremony and the sessions; a key tool that is not the test tool.
- [ ] The ceremony through the node daemons (today started by hand on both nodes); strict mode
      (the registration request's circuit ahead of time: its shape is fixed by the number's
      length, the session id's length and the tool's fixed-width ids); failure paths; the wait
      for the SMS code; libsignal's JSON field order for the registration body.

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

- [x] **One long-lived send session** (2026-11-11; `node_daemon/README.md`, "The long-lived send
      session"; `PublicServiceController.lean`, `serve`). The daemons keep one send session alive
      across notifies: connections opened once and kept alive between notifies (polled, replaced
      when closed, pinged after 25 s idle), contacts kept loaded with their preparation, triple
      stocks refilling in idle time, one notify after another from the daemon's queue, per-id
      results per notify. Ended cleanly between notifies after `max_messages` (5,000),
      `max_seconds` (6 h) or `max_megabytes`; restarted and the notify handed over again when it
      fails. Receiving stays its own long-lived session on the authenticated socket (a sealed
      send must not go on it; the two run side by side).
  - [ ] What bounds a session (PERFORMANCE.md, "The long-lived send session"): memory, which
        grows with every distinct contact prepared (the field engine never frees a share; per
        message no growth was measurable over 400 messages, after the worker began dropping
        sealed and old received buffers); the request lifetime for a notify that must be
        resumed (its ids are read again under the same request, 120 s); a Tor circuit kept for
        hours (NEEDS_REVIEW 3d, the owner's decision on rotating connections).
  - [ ] A notify of thousands of ids is one job: its contacts' field state (several MB each in
        malicious mode) stays until the session ends, and a session that dies after the
        request's lifetime cannot resume it. Until the field engine frees per-contact state,
        the application (or the daemon) should split large notifies into requests of a few
        hundred ids.
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
        With the daemons the next session is started and handed the notify at once (at most
        `send_session.attempts` sessions, 3, while the request is fresh).
  - [x] The journal belongs to the daemon (section 7): one file per notify, named by the signed
        request's digest, removed when the notify completes (leftovers after a day).
  - [x] Through the daemon, a requested id that is not on the database nodes, or not readable
        until their next epoch, is that id's result ("unknown contact" / "retry later"), agreed
        by both parties. (The harness's own sessions, which take their contacts from the export,
        still end there. The "not readable yet" case is not exercised by a test.)
  - [x] **A party that stops without closing its link is detected** (2026-11-11). The workers
        wait for each other at the start of every request for at most `TLS_WORKER_PEER_WAIT`
        seconds (default 180; `tls_worker_v3.cpp`, `await_peer`), then fail the session with the
        reason in the log ("the other party did not reach operation N within S s"). The daemons
        also tell each other when a send session ends (`peer-ended`), so the other side ends at
        once, and stop a session whose log has not grown for 15 minutes. Then the next session
        resumes from the journals. Checked: `--recovery hang` (a controller stopped, the other
        party ends within the wait) and `--app` (a controller killed in a notify, its worker
        left alive; the daemons restart and the notify completes).
  - [ ] Not covered: a party hung INSIDE a request (both workers in one engine operation, one of
        them stopped): the engines' own reads have no deadline. The daemon's stall check (no log
        growth for `stall_seconds`) ends it; nothing faster.
  - [ ] Local-server limits of the tests: account deletion cannot be run (the local server
        answers 500 to it), and 429, 5xx, 404 and bad prekey responses are injected by a test
        proxy between the TLS terminator and the server (`scripts/fault_proxy.py`), not produced
        by the server.
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
- [x] Measure the real server's handshake record sizes: chat.signal.org (2026-11-12) sends the
      whole encrypted flight in ONE record of 1122 bytes (Ed25519 certificate and signature, one
      certificate, 16 bytes of record padding): `deployment-production.json` `handshake: [1122]`.
      Ed25519 signatures have a fixed size, so the size changes only with a new server
      certificate (re-measure then; `measure_handshake.py`). The local compact instance
      (`start_compact_server.sh`, `coalesced_terminator.py`) reproduces that shape (621 bytes).
- [x] `profile` setting in the inventory (`libsignal`: `signal-seal-official`, `bundle-seal 80c−1`,
      request frames named with the same profile), so strict mode works with
      `SIGNAL_CLIENT_PROFILE=libsignal`.
- [ ] **(blocker)** Signup shapes are enumerated, not classed: sender certificate lengths, prekey
      id widths, client version (addresses field, post-quantum field size). A signup outside the
      listed shapes is refused. Either measure and list what real clients send, or give the
      receive kernels capacities (a rewrite of `ReceiveFirst` and its proofs).
- [x] Multi-device digit counts (2026-11-12, after the first real run's contact turned out to have
      three devices and the refresh was refused at `bundle-shape 8192`): `bundle-slot FIRST LAST
      ONETIME`, 8 kernels for every digit count (the item spliced into fixed-width number slots;
      CIRCUIT_SHAPES.md). Enumerating `bundle-item` instead would have been about 11,500 kernels.
- [x] Production deployment covers contacts with up to four devices (`devices 4`, `record_max
      12288` with `scan_record_max 10240`, `device_lists pending`, produced with `--max-gb 26`).
- [ ] **Five or six devices**: the prekey response is a record of class 14336 or 16384, whose
      opening kernel does not lower within this machine's memory (12288 already peaks at 23.6 GB).
      Needs an opening kernel that takes a long record in pieces, or a leaner lowering. Such a
      contact's refresh is refused (strict) and the session ends.
- [ ] The per-combination request frame (`bundle-request-ctr`) still multiplies: 2^n per message
      class for n unanswered devices (30 for four devices; two classes: 60). Fix: CIRCUIT_SHAPES.md
      "Not done" 4. A sixth device does not fit one request record ("retry later"); a request
      split over records is not built.
- [x] The controller's pass-over of an unrevealed body was slow in the clear (measured 2026-11-12
      with `parse-bench`): 1.24 ms/byte for a response body (`PublicReceive.stepPassed`: frame
      parser 0.18, control queue 0.35, response parser 0.73) and 0.56 ms/byte for a server-request
      body (`stepSkipped`); a 7,727-byte prekey response took 10 s. **Fixed 2026-11-12:** the record
      loop now passes over a body in one step (`passBulk k`, `k ≤ passRoom s`) and only the bytes
      `passRoom` excludes (the body's last byte, or all of them when its conditions fail) one at a
      time (`passOne`, the old loop body). Proved equal to the byte-by-byte loop, no new axioms:
      `PublicReceive.passRun_bulk` (controller), from the parser lemmas of
      `TlsMpc/Node/PassOver.lean` (`frame_step_room`, `control_idle`, `response_step_room`); no
      parser module changed, no emitter imports it. `parse-bench` (whole frame, revealed header
      bytes included; bulk and byte by byte checked to end in the same state): response body
      2,265 / 7,727 / 13,000 bytes 2.8 s / 9.7 s / 16.6 s → 27 / 28 / 28 ms; request body
      1.2 s / 4.1 s / 6.9 s → 16 / 17 / 17 ms (70× to 580×; what is left is the revealed bytes).
      Local harness with it (2026-11-12, all passed): `check_signal_service_local_signup.py --compact
      --manifest …circuits-compact/manifest.txt --devices 2/3/4`, malicious and semi-honest (409,
      device refresh with 5,090 / 7,643 / 10,193-byte keys responses, delivered after device refresh,
      every device decrypts; whole send session 32 / 44 / 53 s malicious, 11 / 12 / 13 s semi-honest,
      where the 7.7 KB pass-over alone took about 10 s before), `android again:android`, the
      `--resume` test, `check_signal_service_local.py semi-honest --runs 2 --signup` and `--runs 0 --db`.
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
  - [x] On one machine (2026-11-11): `check_signal_service_local.py MODE --runs 0 --app --real-db`
        (five `server` processes on a private Postgres, consensus and 20 s epochs,
        `scripts/start_db_nodes.py`) passes in semi-honest and malicious mode with the
        long-lived send session: the account's row, a sealed signup with the fixed-width token,
        three notifies (one interrupted by a killed controller and resumed by the next session),
        a delete with the nodes' signatures checked, and a notify reporting the deleted id
        unknown. 410 s and 444 s per run, most of it waiting for epochs. Nothing needed fixing on
        the database side; the binaries of `.deps/ssdb-agent-target` were current, those of the
        in-memory test node were rebuilt.
  - [ ] Not run: nodes on separate machines, a node down or restarted during a session, a
        database larger than a few rows.
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

- [x] A daemon on each computation node (2026-11-11; `node_daemon/`, protocol and formats in its
      README). It accepts the application's signed `notify(ids, message)` and `delete(ids)`,
      checks the signature, freshness and message hash itself (the bytes the database nodes
      verify), confirms with the other daemon that both hold the same request, runs the session
      (one send or delete at a time, queued; a receive session always running beside it),
      supervises it, and returns per-id results (the controller's, plus "unknown contact" and
      "not readable yet") or, for a delete, the database nodes' signatures. Signups come back as
      events (the id), from both nodes. `notify-app` stands in for the application server.
      Checked end to end in both modes: `check_signal_service_local.py --runs 0 --app` (signup,
      notify, notify again, delete, notify with the deleted id reported unknown).
- Still test scaffolding in that flow, to be replaced for a deployment:
  - [ ] **(blocker)** The export file: every session still reads our prekey private keys, our
        address and the sealed-sender server certificate from it, and the two pre-provisioned
        test contacts are created on the database nodes from it (section 2).
  - [ ] **(blocker)** Account creation: a conventional client registers the account, and a
        harness-run session given the credentials in two shares stores its row. The daemons
        cannot create an account (section 2).
  - [ ] **(blocker)** Links: the application's connection to a daemon is plaintext and replies
        are unsigned; the daemons' link is HMAC over plaintext under a shared key; the workers'
        TLS material comes from one `setup-ssl.sh` run for both parties; everything is on
        127.0.0.1. Needs mutually authenticated TLS and per-node keys.
  - [ ] The application stand-in (keys in files, signatures by `handoff_client`, no persistence
        or retry policy) is a reference, not a server.
- [ ] Batching and scheduling for thousands of ids: one request is one job of the long-lived
      session (section 4) and must start within the request's lifetime (120 s); its write-backs
      are accepted for 6 hours after it was issued, and the database nodes remember at most
      4,096 served reads (`notify_write_back_secs`, `DEFAULT_MAX_SERVED_REQUESTS` in
      `secret-shared-db`), so very many small notifies within 6 hours would lose the older
      ones' write authority. No progress reports during a job; a failed notify reports no
      per-id results (the daemons hand it to the next session, which resumes from the journals,
      while the request is fresh).
- [ ] **Several node pairs in parallel** (not built; the owner is considering it for peaks of
      several messages a second, PERFORMANCE.md "The long-lived send session"). Against the
      same database nodes and the same Signal account they would need:
  - [ ] **One contact advanced by one pair at a time.** The database's versioned write already
        refuses a second writer of the same version (that pair's contact gets "retry later" and
        nothing is sent, so no key is reused), but two pairs racing on one contact can leave the
        nodes with different blobs for one version (a write the nodes took only partly), which
        the next read detects and cannot repair. So partition: every id belongs to exactly one
        pair (e.g. a hash of the id, fixed for the deployment, changed only with the pairs
        drained), and the application splits each notify by that rule. A pair's long-lived
        session reloads a contact whenever the nodes' version is not the one it stored, so
        moving an id between pairs is safe once the old pair is idle.
  - [ ] **One receiving pair.** A second authenticated WebSocket for the same account and device
        displaces the first: the server closes the old one with 4409 "Connected elsewhere" and
        delivers queued and new messages to the new one (Signal-Server
        `RedisMessageAvailabilityManager.handleClientConnected`, `WebSocketConnection` line 164;
        best effort through Redis pub/sub; on one server instance the displacement can also drop
        the new socket's presence, which its next keepalive turns into a close with 1000). Two
        pairs receiving would knock each other off in turn. Exactly one pair holds the receive
        session (signups, account row writes, certificate refresh, one-time prekey upload); the
        others only send. Failover needs a lease (e.g. a row on the database nodes) so that two
        never receive at once.
  - [ ] **Sealed-sender rate limits do not depend on the sending connection or address.** The
        only limit on `PUT /v1/messages/{destination}` with an access key is `inboundMessageBytes`,
        keyed on the DESTINATION (128 MiB bucket refilling at about 2 KB/s, fail-open); the
        identified-sender `messages` limiter does not apply; nothing is keyed per connection,
        source address or access key, and no concurrent-connection limit exists in the source
        (`MessageController.sendSealedSenderMessage`, `RateLimiters`). The prekey fetch with an
        access key has no limiter at all. So more pairs (more connections, more addresses) do not
        hit a server limit by themselves; what production adds in its private spam filter
        (`SpamChecker`, not in the public source) or load balancer is unknown and only a real run
        can show.
  - [ ] Per pair: its own journals and daemons; the two organisations' database client keys
        shared by their nodes of every pair (or more compute parties registered with the
        database network); its own worker ports and links. The database nodes take two writes
        and one read per message from every pair (their 64-connection cap, section 6).
  - [ ] What the server sees: N unauthenticated connections from N addresses sending sealed
        messages in bursts after each notify; linkable by timing unless the proxy work (section
        8) spreads them.
- [ ] The daemon keeps requests and results in memory only (signup events are on disk); decide
      what must survive a restart.
- [ ] One node holding "completed" and the other "failed" for the same notify cannot be resumed
      under the same request.
- [ ] The receive session ends after its step budget (hours) and is restarted; there is no
      scheduled restart and no check that an idle one is still alive beyond its keepalives.
- [ ] The reply to the user who signed up that the existing relay design sends.

## 8. Privacy: the proxy

- [ ] Send through a proxy (or several exit addresses) so the Signal server cannot link a
      broadcast's recipients by source address and timing. Decide: who runs it, one connection
      per recipient or per batch, added delay and shuffling. Not started, by instruction.
- [ ] Review what timing reveals even with a proxy (burst of sends after each notify).
- [ ] **Connection rotation over Tor (owner decision 2026-11-11; queued behind the C++ move and
      reorganisation of section 12a).** The long-lived send session reuses connections, and so
      Tor circuits, across notifies. Build: a new connection on a new Tor circuit (distinct
      SOCKS credentials; check that this is what `SIGNAL_TOR_CIRCUITS` does today) after a
      *random* number of messages around a configurable mean (default 10); a pool of
      connections on different circuits (default 4) with each message assigned to a random one
      and sent in random order, not id order; messages of concurrent broadcasts interleaved
      across the pool; an optional hold window (default 0) so small broadcasts can wait to be
      mixed. Circuits built ahead in idle time. No TLS session resumption (the ticket links
      connections). Cost: one in-MPC handshake (1.5–2.6 s) per new connection, about 0.2 s per
      message at a mean of 10. Known limit: bulk sealed sends from Tor exits are probably
      recognisable as one sender whatever the circuits; rotation hides which messages go
      together, not that they share a sender.
- [ ] **Being recognisable is separate from being located.** Whatever the exit. Comparison,
      reference and ranking: `handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md` (model client
      Signal-Android; reference derived from libsignal v0.106.1 and BoringSSL source, because
      libsignal-net cannot be built here: BoringSSL is not vendored). Everything marked done is
      behind `SIGNAL_CLIENT_PROFILE=libsignal` (the default stays `legacy` until the harness's
      `--fingerprint` stage passes; then flip `officialProfile`).
  - [ ] **Regression check:** `check_signal_service_local.py --fingerprint` captures our
        ClientHello, upgrades and frames (`scripts/fingerprint_terminator.py`) and compares them
        with `local_signal_server/fingerprint/reference/` (fails on any difference outside its
        allow-list). Passes (semi-honest and malicious, 2026-11-11). Replace the synthetic reference with a real
        libsignal capture once BoringSSL is vendored (CLIENT_FINGERPRINT.md, first section).
  - [ ] The account password must be base64 of 18 random bytes (24 characters, as Signal-Android
        generates); the local test account's is 22 (section 2).
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
          `signal-seal-official`, `bundle-seal … 80k−1`; listed by `CircuitInventory` with
          `profile=libsignal` (2026-11-12).
    - [ ] Data-message fields (Android adds expireTimer 0, isViewOnce false, expireTimerVersion,
          profileKey): not added; the server sees only lengths, and `expireTimer` could reset a
          recipient's disappearing timer. Owner's decision.
    - [x] Timestamps: each message stamped from the agreed clock when first sent, increasing,
          kept on a resend (was base + recipient index, built ahead). Since 2026-11-12 the stamp
          is taken after the contact's per-session preparation (it was taken before it: a first
          message to a contact was stamped about 40 s before it left).
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
    - [x] At 2 ms the sequential round counts dominated. Measured through a delay relay
          (`PERFORMANCE.md`, "Rounds"): a contact's first send 12 to 16 s, the field side of a
          first message received 22 s (28 s with the server key). With the constant-depth
          programs (`TLS_WORKER_HINTED=1`, to be reviewed: `NEEDS_REVIEW.md` 3b) the field rounds
          are a few dozen per batch of contacts and 167 per first message received.
    - [ ] What then limits the pair is **bandwidth, not latency**: malicious mode moves about
          66 KB each way per field triple and about 0.8 GB each way per message (the Boolean
          triples of its 2.9M AND gates; so 6 to 7 s of a 1 Gbit/s link per message). A contact's
          preparation is 0.75 GB each way (6 s of a 1 Gbit/s link), a first message received
          about 3 GB each way (24 s). Until tables are stored across sessions (section 11), the
          first broadcast of a session to N contacts needs N × 0.75 GB each way. Decide the port
          speed with that in mind, and measure WireGuard's throughput on the chosen machines
          (the engines use about 20 TCP connections, so it can spread over cores).
    - [ ] The engines' own limits over a link, each measured and listed in `PERFORMANCE.md`
          ("What a 2 ms link still costs"): about 100 sequential exchanges of the Boolean engine
          per message, two round trips per reveal call, two MAC checks per field opening.
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
  - [ ] More factories on real nodes. A sustained run of 160 messages is measured (PERFORMANCE.md,
        "The long-lived send session": 0.67 messages/s malicious, 1.25 semi-honest on one
        machine); there the database writes, not the pools, were the limit.
  - [ ] A long-lived, release-build database client: its two `write-blob` runs per message are
        0.4 s of the 1.43 s (malicious) and of the 0.78 s (semi-honest).
- [x] Circuit loading 10.6 s → 2.1 s per process; record opening 1,500 → 935 AND per byte.
- [x] Measuring with latency: `scripts/delay_relay.cpp` and the harness's `--link-delay-ms`
      (every link between the two workers, each direction delayed); the field side alone in
      `rounds_fixture.cpp`. Numbers at a 2 ms round trip: `PERFORMANCE.md`, "Rounds".
- [x] Prepare several contacts in the same field rounds, in constant depth
      (`TLS_WORKER_HINTED=1`, off by default until reviewed: `NEEDS_REVIEW.md` 3b): about 65
      rounds per BATCH instead of 2,300 rounds and 490 openings per contact (12 s each at 2 ms);
      worker operation 66, called by the controller before a contact's first send for it and the
      contacts that follow (`SIGNAL_PREPARE_BATCH`, default 32).
  - [ ] What a batch costs now is its field triples: about 11,000 per contact, 0.75 GB each way
        (100 contacts: 3 minutes on one machine, and 10 minutes of a 1 Gbit/s link). Fewer
        products per contact (the initial point is half of them), or stored tables (next item).
- [x] The first message received and the device refresh in constant depth (same switch): 167
      field rounds instead of 11,400 for a first message.
  - [ ] Twist points and `u = 0` behave differently from libsignal under the switch
        (`NEEDS_REVIEW.md` 3b): decide, or write a twist-capable program.
- [ ] Keep a contact's table across sessions. Designed, not built
      (`SEALED_SENDER_AGREEMENT.md`, "Keeping the table across sessions"): with a field-engine
      MAC key that persists (the owner's decision), a stored table is imported with no rounds and
      no triples; shown in the two engines by `rounds_fixture.cpp` (`store`, `load`, and a tampered
      share stopped by the MAC check). Without a persistent key: about 1,000 products per contact
      and session. Needs the blob format, two worker operations, and the MAC key share before the
      field engine starts.
- [ ] Per-message latency that remains at 2 ms (`PERFORMANCE.md`, "What a 2 ms link still costs"):
      the Boolean engine exchanges once per about 30,000 AND gates (a message is about 100
      sequential exchanges), every reveal call is a request agreement and an opening, and each
      opening in the field engine carries two MAC checks.
- [ ] `TLS_WORKER_FIELD_DIRECT=1` (one message delay per field round instead of two): built,
      off by default, to be reviewed and then switched on.
- [x] One long-lived connection: the handshake and upgrade are paid once per send session (up to
      5,000 messages by default), not per broadcast (section 4).
- [ ] Send without waiting for each response; several contacts in parallel.
- [ ] Fewer AND gates in the send and record circuits (AES, SHA-256, large-record opens).
- [ ] Measure over a real network between two machines.

## 11a. Spikes: a stock of circuits made ahead, encrypted on disk (owner decision 2026-11-11)

**Load (owner).** About 300 broadcasts a day averaging 48 recipients (about 14,400 messages a
day, 430,000 a month, US daytime), and occasionally one broadcast of about 14,000 recipients,
which should finish "within minutes ideally. an hour is too long. 10 minutes would be nice":
about 23 messages a second sustained. Live, semi-honest mode would need about 18 Gbit/s
between the nodes for that. Still open: how often the large broadcasts happen, and whether
they are known in advance (both set the stock size).

**Design chosen.** One dedicated pair with large disks. In quiet hours the nodes produce and
exchange the message-independent part of each send (semi-honest: the garbled circuit, about
85–100 MB per message; one spike is about 1.2–1.4 TB) and keep it on disk; a send then needs
only a small exchange plus local computation. The owner accepted keeping the stock on disk
provided it is encrypted ("encrypting on disk seems reasonable. plan for that"). Many burst
pairs rented by the hour stay the fallback for a spike larger than the stock. Queued with the
move out of C++ (section 12a), because the stock handling belongs in Lean with the sequencing.

Order of work:
- [ ] **Measure first.** With the engine as it is: how much of a semi-honest send is
      message-independent (bytes and time), the evaluator's time per message per core, and
      therefore whether 23 a second is reachable on one 16-core pair. If not, size the pair or
      add burst pairs. Same split for malicious mode (stock about 13 TB a side per spike).
- [ ] **Stock format.** Per circuit shape (size class, client profile), fixed-size items with an
      index; produced by the same lowered circuits as today (manifest hash recorded in the
      stock header, so a stock is never used with other circuits). Both nodes agree a hash of
      every item when it is made and check it before use.
- [ ] **Use exactly once.** A durable "consumed" record written and synced before an item is
      used; both nodes confirm the item index inside the agreement for every message; a node
      that finds its record ahead of or behind its peer's skips forward, never back. State and
      prove in Lean: no index is ever handed to the engine twice, including across crashes and
      restarts (model the journal). Stock is never restored from a snapshot or backup: the
      stock header carries a boot-time random id held only in memory, so a restored disk is
      unusable.
- [ ] **Encryption at rest.** Stock encrypted under a key that exists only in memory (lost on
      reboot: the stock is disposable and is made again). Each item under its own key derived
      from a chain that is advanced and the old value erased on use, so used items cannot be
      recovered from the disk even though SSDs do not reliably delete. The garbling node's side
      (its randomness) is the sensitive one; the evaluator's side is authenticated, and
      encrypted too for uniformity.
- [ ] **Refill policy.** Target level per shape, refill when idle and at night, rate limit so
      the everyday load is not starved; what happens when the stock runs out (fall back to
      live garbling at link speed, reported to the application as slower, never refused).
- [ ] **The other limits on a spike**, needed whatever the stock: contacts prepared in parallel
      or ahead (0.28 s each today, over an hour for 14,000 on one session); a long-lived,
      release-build database client (0.4 s per write today); the field engine freeing shares
      (about 0.1 GB per contact per session today); several sessions per pair with each
      contact id on exactly one.
- [ ] **Malicious mode.** The same stock for authenticated triples; needs each node's
      authentication key to live as long as the stock (the persistent-key question in
      `SEALED_SENDER_AGREEMENT.md`) — decide then.
- [ ] `NEEDS_REVIEW.md`: the stock changes when secrets exist and for how long; record the
      argument (nothing in the stock depends on contacts or messages; reuse is the hazard).
- [ ] Deployment: disks sized for the stock, the machines of `deployment/PROVIDERS.md`
      re-priced for this design (dedicated pair about €330–400 a month plus five database
      nodes), and a test that pulls the plug mid-spike and checks no index is reused.

## 11b. Prepare a contact's devices ahead of the first broadcast (owner idea 2026-11-12)

The second real run showed the cost: the first send to a contact with three devices was answered
409 and took about 30 s of device refresh (key fetch, one session establishment per device
including a KEM encapsulation) before the resend. In a 14,000-recipient broadcast to new
multi-device contacts that would dominate. So do the multi-device work after the signup, not in
the broadcast.

- [ ] **Default plan: prepare silently, delayed and batched.** A background job takes contacts
      that signed up since its last pass, in shuffled order, and for each one fetches the key
      bundle for all devices (`GET /v2/keys/{uuid}/*`) and runs the establishment kernels, storing
      one session record per device. No message is sent; the first broadcast then goes out as
      PreKey messages to every device in one request, with no 409. The 409/410 path stays as the
      fallback for device lists that changed since.
- [ ] **Do not do it immediately after the signup.** A key fetch (or a welcome message) for user
      U seconds after the account received a sealed-sender message tells the server that U was
      the sender: the same timing correlation as a read receipt (owner: "never send read
      receipts … de-anonymizing through timing correlation"). Run the job on its own schedule
      (for example a pass every few hours, or a random delay of hours per contact), over
      connections that are not the receive connection, and with the rotation of section 8.
- [ ] **Optional: a welcome message** ("you are signed up") sent by the same delayed job. It does
      the same preparation as a side effect and confirms the signup to the user. Owner's choice;
      not built by default because it is user-visible and adds a send per signup.
- [ ] Needs: a fetch-without-send flow (today the fetch only runs after a 409), storing
      established-but-unsent device sessions (the PreKey state must survive until the first
      send), a "prepared" mark in the contact record, and a harness stage: signup, prepare job,
      link another device, broadcast (expect: no 409 for prepared devices, 409 only for the new
      one). One-time prekeys are consumed by the fetch; that is what they are for.
- [ ] Measure: prepare cost per device in both modes, and the broadcast rate to prepared
      three-device contacts (three envelopes per send; not measured yet).

## 11c. Generate the identity key jointly (queued by the owner 2026-11-13: do not start yet)

Today the ACI identity private key is in the clear on both nodes (`CEREMONY.md` sections 4 and 8,
decision 2). A node colluding with the Signal server (or with whoever can read the server's queue)
can open the sealed-sender layer of envelopes addressed to the account and read who signs up. A
node alone cannot (no password, so no authenticated socket; envelopes are never in the clear in a
session).

Queued work ("option 3"):

- Joint key generation in the ceremony: each node picks a share; the public key is the sum of the
  two public shares, computed in the clear; one conversion inside the engines at the `store` stage
  turns the shares into the bit form the sessions load from the account's row. X25519 clamping of
  the shared scalar needs care.
- Joint signing of prekeys with the identity key (ceremony and every prekey rotation): a two-party
  Schnorr-style XEdDSA signature (public hash input, signature linear in the key shares; a
  commit-then-open round for the nonce). Needed in any case if the clear key is erased.
- Both written in Lean with proofs; no clear copy of the identity private key ever exists.

Expected cost: none per message (sessions already use the identity key as a secret loaded from the
sealed account row — inferred from `CEREMONY.md` and the receive proofs' `ScalarHolds`, to be
confirmed when the work starts); seconds in the ceremony; the cost is the build and proof effort.

Not covered: signed prekeys, one-time prekeys and Kyber keys stay in the clear (Kyber decapsulation
runs outside the engines). The sealed-sender layer needs only the identity key, so this closes the
who-signs-up exposure, not joint holding of first-message session keys.

Cheaper alternative ("option 2"): erase the clear copy after `store`. Protects against a node
compromised later, not one that kept a copy, and breaks prekey rotation unless joint signing exists.

## 11d. Do not enable the hinted curve setting (`TLS_WORKER_HINTED=1`) — recorded 2026-11-14

The check-value audit (`CHECK_VALUES_AUDIT.md`, branch `check-values`, section 3.1) could not show
that the hinted curve programs' link checks (`edwards-bit-table`, `edwards-prepare-hinted`; legacy
C++ `hinted_points.h`) are safe against a cheating node: the hinted points enter as unchecked field
elements, the links are opened per window and per coordinate, masked denominators are opened, and
the soundness theorems (`bitTable_sound`, `prepareTable_sound`) assume every link holds. Whether a
cheating node can make the abort pattern depend on a contact's key is UNDECIDED (PROOF_GAPS F22c).

A default deployment never runs these programs: the setting is off by default, and the script path
never calls them even when it is on. Until decided: keep the setting off; deployment preflight
should refuse it. Ways out: (a) drop the hinted path with the legacy C++ (the non-hinted programs
compute the multiples inside the engine and need no new argument); (b) change and re-lower the two
programs (on-curve check per hinted point from its owner's input only; links opened as one masked
random combination; a link failure fatal and reported) and then prove it.

## 11e. DEFECT: contact preparation (op 66) aborts selectively on a contact's key — found 2026-11-14

Found by the check-value proof work (`CHECK_VALUES_AUDIT.md` §4b–4d and
`TlsMpc/Node/TopLine/Checks/PrepareLeak.lean`, branch `check-values`). Default path, scripts:
op 66 → `ContactsPrepare.prepareOneG` → `Curve.offsetPrepare` → `Curve.prepBlock` runs the field
program `edwards-prepare` on the contact's key and on both parties' 504 scalar coins BEFORE the
coins' bit checks are opened; coins are only checked to be below 2^64. The program's divisions
abort on a zero denominator, and a cheating node can choose non-bit coins (e.g. 2 and 7 at its
first two positions) so that a denominator is zero for some valid contact keys and not for others.
The run then stops at the program for those keys: the cheating node learns a predicate of the
contact's key from whether the run aborts. A concrete pair of keys is checked in Lean by `decide`.
How precisely the test can be aimed at one candidate key is not established. Whether the legacy
C++ op 66 has the same ordering is being checked.

Fix being implemented (branch `prepare-fix`): open a mask-free bit check on the coins before
`edwards-prepare` runs (one more round), then prove op 66 simulatable from its accepted leak.
To check with it: `Curve.torsion` on the hinted path has the same shape (see 11d: hinted stays off).

## 12. Testing still owed

- [ ] Rerun the older fixture checks (`check_tls_worker_v3.py`, `check_tls_application_v3.py`,
      `check_signal_service_v3.py`) after the recent worker changes.
- [ ] An official Signal client as the recipient and as the new user.
- [ ] Thousands of contacts; hours-long sessions; reconnects; database node faults.
- [ ] Then the real service, with one test account, at low volume. **First run 2026-11-12**: the
      signup worked; the reply got 409 (three devices) and the refresh was refused by the manifest
      (REAL_TEST_PLAN.md section 0). Fixed offline the same day.
- [ ] **(before the retry)** The local reproduction of that run with 2, 3 and 4 devices, strict,
      both modes, the repeated-signup case and `run_real_test.py --resume` (commands in
      REAL_TEST_PLAN.md section 4): not run on 2026-11-12, the machine's Docker daemon (OrbStack)
      had stopped answering, which blocks every local Signal-Server.
- [ ] The multi-device harness stages of `check_signal_service_local.py --strict` use
      `local_signal_server/deployment.json`, which now also lists `bundle-slot` (the controllers'
      default since 2026-11-12): produce that manifest again before its next strict run, or run
      with `SIGNAL_BUNDLE_SLOTS=0`.

## 12a. Less C++, more Lean (queued: starts only after the application works end to end)

Order set by the owner on 2026-11-11: first finish the orchestration blockers (sections 4, 6
and 7: recovery, the node daemons and the application's requests, the real database nodes) so
there is a functioning application end to end including the database nodes; then this.

**One plan with the audit reorganisation (owner, 2026-11-11).** The owner wants it to be "easy
to look at all the external communication a node is doing and easily verify its security
properties", and asked that this and the move out of C++ be one coherent plan, queued to start
once the agents now editing the controller have landed. The map of what exists is
`SECURITY_MAP.md`; the staged plan is `REORGANIZATION_PLAN.md` (both being written). Target: all
controller I/O through one small Lean module; public versus secret in the types, with named
reveal functions as the complete list of openings; per-channel theorems; `TlsMpc/Security.lean`
restating the important theorems in one place. The owner waived a review of the plan ("you can
skip my review of the plan, i trust your judgement here"): the work starts as soon as the plan
is written and the other agents have landed.

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
