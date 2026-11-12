# Node daemon and application stand-in

The layer between the application server and the two-party sessions. One `node-daemon` runs on
each computation node; `notify-app` stands in for the application server and is the reference
for how a real one integrates.

```
application ──notify / delete / events──▶ node-daemon 0 ◀──confirm, start──▶ node-daemon 1 ◀── application
                                              │ controller + worker  ═══ two-party session ═══  │
                                              └────────── Signal server, database nodes ───────┘
```

Build (offline, vendored crates, the toolchain of `local_signal_server/scripts/provision.sh`):
`node_daemon/build.sh` → `target/debug/node-daemon`, `target/debug/notify-app`.
Checked end to end by `local_signal_server/check_signal_service_local.py --runs 0 --app`.

## What a daemon does

- Verifies every request of the application itself, before anything else: the id list (not
  empty, sorted, distinct, without the account's reserved id), the Ed25519 signature (strict)
  under the application's notify key over the exact bytes the database nodes verify
  (`secret-shared-db`, `server/src/handoff.rs`: `NotifyRequest::encode`, `DeleteRequest::encode`),
  the freshness rule of the nodes (`issued_at` within `[now − notify_max_age_secs, now + 30 s]`),
  and for a notify that SHA-256 of the message text is the signed `message_hash`. The encoding is
  re-implemented in `src/lib.rs` (the database project's library does not build from the vendored
  crate set); a unit test checks it against a request file written by `handoff_client`, and the
  application stand-in signs with `handoff_client` only.
- Confirms with the other daemon that it holds the SAME request (the request's digest, which
  covers ids, message hash, nonce and time) before a session starts. Neither daemon can be driven
  alone: a daemon answers "yes" only for a request it verified itself.
- Keeps one long-lived send session running and hands it one notify after another (below);
  supervises it: memory and message limits, a stall check, kill of the whole process tree on a
  hang or on shutdown, a new session (resuming the notify) after a failure. A delete runs its own
  short controller (`db-delete`) between notifies.
- Keeps a receive session running at all times and turns each new user it stores into an event.
- Returns only what the two controllers agreed on as public results. It never holds, logs or
  returns a share; it does not read Signal traffic. Its own secrets are the path of this node's
  database client key and the key of the link to the other daemon. The controller's error text
  and log stay on the node (`STATE/logs/`); the application gets a status.

## Protocol between the application and a daemon

TCP, one JSON object per line, one request and one reply per connection. The application sends
every request to BOTH daemons and accepts a result only if both report the same `result_digest`.

| Request | Reply |
|---|---|
| `{"op":"notify","message":TEXT,"request":R}` | `{"ok":true,"job":DIGEST,"state":"received"}` or `{"ok":false,"error":…}` |
| `{"op":"delete","request":D}` | the same |
| `{"op":"wait","job":DIGEST,"timeout":SECONDS}` | `{"ok":true,"state":"received"｜"agreed"｜"running"｜"done","result":…}` (blocks until done or the timeout) |
| `{"op":"events","after":N,"wait":SECONDS}` | `{"ok":true,"events":[{"seq":1,"event":"signup","id":"…","at":UNIX}],"next":N'}` (blocks until there is one) |
| `{"op":"status"}` | counts of requests by state; whether a receive session is running |

`R` is the file `handoff_client sign-request` writes:
`{"ids":["1","2"],"message_hash":hex32,"nonce":hex16,"issued_at":unix seconds,"signature":hex64}`;
`D` is the file of `sign-delete` (the same without `message_hash`, with `"kind":"delete"`).
`TEXT` is 1..256 bytes of UTF-8. `DIGEST` (hex) is SHA-256 of the signed bytes; it names the
request for both daemons, the controllers' journal and the database nodes.

### Results

Notify:

```json
{"job":"…","kind":"notify","status":"completed",
 "results":[{"id":"1","result":"delivered","reason":""},
            {"id":"7","result":"unknown contact","reason":""}],
 "result_digest":"…",
 "node":{"party":0,"detail":"","seconds":41.3}}
```

`results` has one entry per requested id, in the request's order. `result` is one of the
controller's per-id results (`delivered`, `delivered after device refresh`, `delivered after
identity change`, `retry later`, `needs re-signup`, `gone`, `fault`; see
`handshake_backend/EmpHybridWork/MULTI_DEVICE.md` section 9), or `unknown contact` (the database
nodes hold no such id: never signed up, or deleted), or `retry later` with the reason "not
readable until the database nodes' next epoch" (signed up moments ago).

Delete:

```json
{"job":"…","kind":"delete","status":"deleted","ids":["7"],"result_digest":"…",
 "node":{"party":0,"detail":"","seconds":0.6,
         "evidence":{"request_digest":"…","nodes":["committed",…],"commit_signatures":[hex64｜null,…],"acknowledged":true,…}}}
```

`evidence` is the database client's `DELETE` file: each database node's signature over the
request's digest. The application checks it itself
(`handoff_client verify-signatures --network NET --delete-output EVIDENCE --delete-request D`:
at least `n − max_faulty` valid node signatures for this very request); `notify-app delete` does.

`status` is `completed` / `deleted`, or:

- `failed`: the session ended without an agreed result (it died, hit its time limit, or the
  other node did not start it). For a notify, results are not reported; submitting the SAME
  signed request again while it is fresh runs a new session that reloads every contact from the
  database nodes and, from each node's journal, does not resend what both nodes recorded as
  settled (at least once; duplicates possible; see PRODUCT_TODO.md section 4).
- `rejected`: the other node did not confirm that it received this request within
  `agree_seconds` (30). Nothing was run. This is what a request sent to one node only ends as.
- `expired`: its turn did not come while the request was fresh.

`result_digest` is SHA-256 of the JSON of `job`, `kind`, `status` and `results` (notify) or `ids`
(delete), keys sorted, no whitespace. Everything under `node` is that node's own account
(timing, a status text, the delete evidence) and is not compared.

Each id's result of a notify was compared between the two controllers inside the session
(a digest, through the workers' link) before either reported it; ids the database does not hold
are compared the same way at load.

## Between the two daemons

The same line protocol on a listener of its own (`peer_listen`; the application's listener,
`listen`, refuses peer messages and the peer listener takes nothing else). Each request carries
the sender's party (`from`), a fresh 16-byte `nonce`, the sender's clock (`at`, accepted within
60 s) and `mac` = HMAC-SHA256 over the message under a key the two nodes share
(`peer_key_file`). A request is accepted once: a nonce seen within the window is refused as a
replay, and a message whose `from` is the receiver itself (reflected) is refused. Each reply is
sealed the same way with `reply_to` = the request's nonce, and the caller accepts only a reply
to the request it sent (`lib.rs`, `seal_request` / `open_request` / `seal_reply` / `open_reply`).
Both daemons must run the same version of this link. Party 0 leads:

- `peer-agree {job}`: "do you hold this request?" Asked for every request party 0 accepted, until
  yes or `agree_seconds`. Party 1 marks a request rejected if it is not asked within
  `agree_seconds + 5`.
- `peer-start {job, session, port}`: both start their controller for this request, with the
  session name (32 random bytes) and worker port party 0 chose. Party 1 refuses a request it does
  not hold, one that is no longer fresh, and anything while it is busy.
- `peer-receive {session, port}`: both (re)start the receive session.
- `peer-serve {session, port}`: both (re)start the long-lived send session (below); party 1's
  previous one is ended first.
- `peer-ended {session}`: "my send session of this name ended" (it failed, was asked to end, or
  its controller died). The receiver ends its own session of that name at once instead of
  waiting for the workers' bounded wait. Sent by both parties.
- `peer-finish {job}`: party 0 gave a notify up (its attempts are used up); party 1 reports it
  `failed` too.

Only public values cross this link: request digests, session names, ports.

## The long-lived send session (default; `send_session.long_lived: false` for one per notify)

Each node runs one send session (controller and worker) for many notifies, under the session
name party 0 chose (`peer-serve`). It is started when the daemons start and opens its
connections to the Signal server once (handshake, unauthenticated WebSocket, one per Tor circuit
with a proxy); its controller prints `{"event":"ready"}` when they are up. Then:

- **Jobs.** Party 0 hands each agreed notify, in order and one at a time, to the session: it asks
  party 1 (`peer-start {job, session}`, refused unless party 1's session has that name and is
  idle, and the request is fresh), then both daemons write the job into the session's directory
  (`SIGNAL_SERVE_DIR`: `jobs/DIGEST-request.json`, `jobs/DIGEST-message.txt`, then `job.json`
  = `{"job","request","message","journal"}`, renamed into place whole). The two controllers run a
  job when both were handed the same one (they compare its name's hash at each tick) and print one
  line with its agreed per-id results, `{"job","status":"completed","results","unknown",
  "not_yet_readable","recovery","messages","delivered","milliseconds"}`; the daemon turns it into
  the request's result exactly as for a one-notify session and removes the job file and journal.
- **What the session keeps between jobs**: the connections and their request counters, the
  contacts' loaded state and per-session preparation (a contact is reloaded only when the version
  the database nodes hold is not the one the session stored), the account, the circuits. Every job
  still reads its ids from the database nodes under its own signed request (which also authorises
  that job's write-backs), so a deleted id is `unknown contact` and leaves the engines.
- **Between jobs** the controllers tick every quarter second (an exchange through the workers:
  the job each holds, whether its daemon asks the session to end, the clocks), poll each
  connection (one the server or the proxy closed is replaced at once; a ping or pong is answered),
  and keep each connection alive after 25 s without traffic (a WebSocket ping under the
  libsignal profile, as libsignal does; otherwise a `GET /v1/keepalive`, awaited). The triple
  stocks refill in the background as in any session.
- **Ending a session cleanly.** Each daemon asks its session to end, between jobs, by creating
  `stop` in the session's directory when it has sent `send_session.max_messages` messages (default
  5,000), is `max_seconds` old (default 6 hours) or its process tree's resident memory reaches
  `max_megabytes` (default 0: no limit; sampled every 10 s and logged as `send session memory`).
  The two controllers see either daemon's request at the same tick and end together; party 0 then
  starts the next session. Nothing is in flight at that point, so nothing is lost or repeated.
- **A session that fails.** A job's failure is the session's (as for a one-notify session). The
  daemon whose session ended tells the other (`peer-ended`), both sessions end, party 0 starts a
  new one, and the unfinished notify is handed to it again (at most `send_session.attempts`
  sessions, default 3, while the request is fresh). The new session reads the contacts from the
  database nodes and does not resend what both journals show as settled (at least once; the
  contact whose send was in flight may get the message twice). A notify whose request expires
  before another session could take it ends `failed` on both nodes.
- **A party that stops responding.** The workers wait for each other at the start of every
  request for at most `timeouts.peer_wait_seconds` (default 180; `TLS_WORKER_PEER_WAIT`), so a
  node whose controller hangs or died while its worker lives ends the other node's session with a
  reported reason ("the other party did not reach operation N within S s" in the session's log)
  instead of a wait without end. A session whose log has not grown for
  `send_session.stall_seconds` (default 900; an idle session logs several lines a second) is
  stopped by its daemon.

## Sessions and ordering

- One send or delete at a time per node pair, in the order party 0 confirmed them; later
  requests queue (and expire if their turn does not come within the request's lifetime, 120 s
  today).
- The receive session runs CONCURRENTLY with sends. They are separate worker pairs on separate
  ports with separate working directories and database scratch directories, on different
  sockets of the account (authenticated for receiving, unauthenticated for sealed sends), and
  they touch different rows (a receive creates a new contact; a send reads and writes existing
  ones; both only read the account's row). Stopping the receive session for every notify would
  delay signups for as long as a broadcast runs, and a receive session cannot be stopped safely
  in the middle of storing a new contact. Cost: memory for two worker pairs.
- The receive session ends when it fails or after its step budget (4096 records and keepalives:
  hours when idle); the daemons then start a new one (back-off 4 s to 60 s). Messages are
  acknowledged to the server only after the contact is stored, so nothing is lost in between.
- A signup event is emitted by each node's controller when the new contact is stored on the
  database nodes (`{"event":"signup","id":…}` on its standard output), and the application counts
  an id as signed up when both daemons report it.

## Configuration (one JSON file per node)

```json
{ "party": 0, "listen": "127.0.0.1:19700",   // the application's: localhost, or an address only it reaches
  "peer_listen": "10.0.0.1:19710",            // the other daemon's (WireGuard address); must differ from listen
  "peer": "10.0.0.2:19710",                   // the other daemon's peer_listen
  "peer_key_file": "…/peer.key",              // hex, at least 16 bytes, shared by the two nodes
  "state_directory": "…/node-0",              // the daemon's own: logs/, work/, journal/, events.jsonl
  "controller": "…/public_service_controller",
  "worker": { "binary": "…/tls-worker-fixture-v3",   // or the semi-honest worker
              "send_directory": "…", "receive_directory": "…",   // the workers' key material, one per session kind
              "hosts": ["10.0.0.1", "10.0.0.2"], "port_base": 23000 },
  "circuits": { "tool": "…/circuit_cache.py", "manifest": null },   // manifest: CIRCUIT_MANIFEST (strict mode)
  "signal": { "endpoint": "127.0.0.1", "port": 18443, "hostname": "server.example",
              "trust_root": "…/ca.pem", "certificate_checker": "…/public_auth" },
  "proxy": { "socks": "127.0.0.1:9050", "circuits": 3 },             // optional (Tor)
  "database": { "client": "…/handoff_client", "network": "…/network.json", "key": "…/compute-nodes/0/key.json" },
  "application": { "notify_public_key": "base64" },   // optional pin; default and cross-check: the database network config
  "test": { "export": "…/mpc-export.json", "tokens": "…/tokens", "kem_tool": "…/lss-provision" },   // scaffolding, below
  "environment": { "DYLD_LIBRARY_PATH": "…" },        // passed to the controller as is
  "receive": true,
  "timeouts": { "agree_seconds": 30, "start_margin_seconds": 30, "send_seconds": 600, "send_seconds_per_id": 60, "delete_seconds": 120,
                "peer_wait_seconds": 180 },                // TLS_WORKER_PEER_WAIT for the workers
  "send_session": { "long_lived": true, "max_messages": 5000, "max_seconds": 21600, "max_megabytes": 0,
                    "stall_seconds": 900, "attempts": 3 } }   // README, "The long-lived send session"
```

The controller inherits the daemon's working directory (the repository root, for `circuit_cache.py`).

## The application stand-in

```
notify-app token  --db-client C --app-config APP_CONFIG --id ID --work DIR
notify-app notify --daemons A,B --db-client C --key NOTIFY_KEY --ids 1,2 --message-file F --work DIR [--timeout S]
notify-app delete --daemons A,B --db-client C --key NOTIFY_KEY --network NET --ids 1,2 --work DIR [--timeout S]
notify-app events --daemons A,B [--after N] [--wait S] [--until-id ID]
notify-app status --daemons A,B
```

It signs with the database project's `handoff_client` (`sign-signup`, `sign-request`,
`sign-delete`), sends the request to both daemons, waits for both, and prints
`{"job","agreed","result","nodes":[…]}`; exit status 0 only if both nodes report the same
result and it is `completed` / `deleted` (and, for a delete, both nodes' evidence verifies).
`token` prints the 108-character signup token the new user sends to the account as their first
Signal message.

## Controller interface added for the daemon

All additive; without these variables the controller behaves as before.

- `SIGNAL_NOTIFY_MESSAGE_FILE` (send session with the database nodes): the session sends ONE
  message, this file's text, to exactly the ids of the signed request `SIGNAL_DB_REQUEST`; the
  controller checks the text against the request's `message_hash`. A requested id that the
  database nodes do not hold, or do not serve until their next epoch, is left out of the session
  and listed in the new report fields `unknown` / `not_yet_readable` (the two parties compare
  these lists before going on) instead of ending the session.
- `SIGNAL_LOCAL_EVENTS` (receive session): a line `{"event":"signup","id":"…"}` on standard
  output as soon as a new contact is stored. The final report line is unchanged.
- A receive session without end needs no change: `SIGNAL_LOCAL_EXPECT` is set far above what the
  session's step budget allows.
- The daemon names the notify (`SIGNAL_NOTIFY_ID` = the request's digest) and owns the journal
  (`SIGNAL_NOTIFY_JOURNAL` = `STATE/journal/DIGEST.jsonl`, removed when the notify completes;
  leftovers older than a day are removed at start).

## What is still scaffolding

Honest list; PRODUCT_TODO.md section 7 has the same items as work.

- **The export file** (`test.export`, `SIGNAL_LOCAL_EXPORT`). Every session still reads it: our
  prekey private keys (receive), our address and registration id, the server's sealed-sender
  certificate, and the identity key and sender certificate as a fallback when the account's row
  is missing. It also holds the two pre-provisioned test contacts: a requested id that is in the
  export and not yet on the database nodes is created there from the export, under a token from
  `test.tokens`. A deployment has no export: section 2 of PRODUCT_TODO.md.
- **Account creation.** The account is registered by a conventional client, and its row on the
  database nodes is created by a harness-run session that is given the credentials in two shares.
  The daemons never see credentials and cannot create the account.
- **`test.kem_tool`**: Kyber decapsulation by the provisioning tool.
- **Local addresses and keys.** Both daemons, all workers and the database test nodes on
  127.0.0.1; the workers' mutual TLS material comes from MP-SPDZ's `setup-ssl.sh` run once for
  both parties; the link between the daemons is HMAC-authenticated plaintext; the application's
  connection to a daemon is plaintext and the daemon's replies are not signed. A deployment needs
  mutually authenticated TLS on both links (or signed results), and each node its own keys.
- **The application stand-in** keeps the application's private keys in files and shells out to
  `handoff_client`; it has no persistence, no retries and no queue of its own.
- **Epochs.** The harness tells the in-memory database nodes when an epoch passes. With real
  nodes a contact is readable only after the next epoch; until then its notify result is "retry
  later".

## Not done

- Batching and scheduling for thousands of ids: one request is one job, and it must start within
  its lifetime (120 s). No progress reports during a job. A notify of thousands of ids keeps all
  their contacts in the session's memory until it ends (PRODUCT_TODO.md section 4): split it.
- A `failed` notify reports no per-id results (the journal knows what was settled; the next
  session for the same request uses it, and the daemons hand it to that session themselves while
  the request is fresh). After the request has expired the application must sign a new one,
  which the journal does not cover: duplicates are then possible.
- The connections of the long-lived session are kept across notifies: the server can link the
  recipients of different notifies sent on one connection (NEEDS_REVIEW.md 3d; owner's decision).
- The receive session's worker pair runs beside the send session's: two worker pairs per node
  (about 1 GB idle each in semi-honest mode, 3 GB in malicious mode, mostly triple stocks).
- The daemon keeps requests and results in memory (signup events are also on disk). After a
  daemon restart the application must ask again; a result that was not fetched is gone.
- If one node's daemon holds a `completed` result and the other's a `failed` one, resubmitting is
  refused by the first (the application sees the disagreement and must sign a new request).
- No reply to the user who signed up, and a delete does not tell Signal anything.
- No limit on connections or request rate from the application side; no authentication of who
  may ask for events or results (they are public to the nodes, not to the world).
- The receive session is not restarted on a schedule, and a hung one is noticed only by its
  worker link failing.
