# First test against Signal's real service: what differs, what is ready, how to run it

Written 2026-11-11 (branch `two-party-hybrid-worker`). Prepared offline: **nothing here has
contacted any Signal host.** Every step marked *(go-ahead)* below contacts Signal's service and is
run by the owner only. Everything else is offline or against the local server.

The test: a real phone sends the account (registered by `real_signal/register`, state in
`real_signal/state/account.json`) a sealed-sender message whose text is a signup token; the
two-party client receives it, creates the contact, and sends one text back.

Tools (all new except the first):

| | |
|---|---|
| `real_signal/register` | registers the account (done 2026-11-11, `state/account.json`) |
| `lss-provision export-account ACCOUNT_JSON OUT_DIR production\|local` | **no network**: the controllers' export, each party's credential share, deployment hints |
| `real_signal/signal-root-ca.pem` | Signal's pinned TLS root (from libsignal; public) |
| `real_signal/deployment-production.json` | the circuit inventory's settings for this account (handshake sizes still to measure) |
| `real_signal/measure_handshake.py` | one conventional TLS handshake, records the server's handshake record sizes and chain |
| `real_signal/run_real_test.py` | runs the test (receive the signup, send one text), records everything |
| `SIGNAL_RECORD=FILE` (controller) | one JSON line per exchange with the server, with time |
| `SIGNAL_ACK_REFUSED=0` (controller) | refused messages stay on the server (recorded, not acknowledged) |

## 1. Gap list

Status: **handled** (works for production as it is), **change needed** (file, size), **unknown**
(only a connection shows it). Blocking items first.

### Blocking

**B1. A real Signal-Android first message is refused (change needed).** The receive kernels take the
contact's profile key from the field right after the message body
(`TlsMpc/Signal/ReceiveFirst.lean`, `withAccessKey`: "right after the body unless other fields come
between"; the worker passes `offset = start + text length`, `service_kernels.h` line ~396).
Signal-Android's plain-text `DataMessage` puts `expireTimer` (field 5, `28 00` for 0, more bytes
for a set timer) between `body` (1) and `profileKey` (6) (`CLIENT_FINGERPRINT.md` (e), read from
the Android source, not yet seen on the wire). The kernel then sees `28` where it expects `32 20`
and the signup is refused. Fix: `withAccessKey` accepts a short run of other fields (an
`expireTimer` varint of 1 to 5 bytes) before `32 20`, choosing the offset privately (no new
opening), about 30 lines of Lean plus its `_map` theorem; `CircuitInventory` unchanged. Until
then the first real signup will be refused (and, with `SIGNAL_ACK_REFUSED=0`, kept on the server
for a fixed build). Related, **unknown**: the content's padded size (Android pads to `80k − 1`; a
108-character token with Android's fields is likely 240 bytes of ciphertext, not the local 176),
the `ContentHint` (Android may set RESENDABLE: hint 1), the post-quantum field size of libsignal
0.107 (`signup_pq`, 37 for 0.106), and whether addresses are present. `deployment-production.json`
lists 176 and 240 and both hints; anything else is produced on demand (non-strict) or refused
(strict), and recorded.

**B2. Circuits for production shapes have never been produced or run (change needed).** Our
production sender certificate is **134 bytes** (compact: UUID as 16 bytes, signer named by id 3)
against 244 locally (embedded signer, UUID text). Every kernel parameterised by our certificate
length (`signal-conversation-view`, `signal-widths`, `signal-seal-official`, `contact-seal 204`
for the account row, `establish-session 134`, `receive-session 134 …`, `receive-access-key 134 …`)
exists only for 244. `ReceiveFirst.certShape` accepts the compact form and `circuit_inventory`
accepts the production settings (396 kernels, checked), but nothing has run with them. Also:
`CircuitInventory.lean` does not list the libsignal-profile seal kernels (`signal-seal-official`,
`bundle-seal … 80k−1`), so **strict mode cannot be used with `SIGNAL_CLIENT_PROFILE=libsignal`**
(CLIENT_FINGERPRINT.md says the same). Producing a kernel while connected leaves the socket idle
for tens of seconds (the server may close it). Needed before the run:
- `CircuitInventory.lean`: a `profile` setting that lists `signal-seal-official CERT CLASSES` and
  the `80k − 1` `bundle-seal` sizes (about 15 lines), and `produce_circuits.py` running
  `request-shape` with the same profile;
- produce `deployment-production.json` (one kernel at a time, about 25 minutes);
- a local run with a compact certificate: `local_signal_server/scripts/make_config.py` can set
  `embedSigner: false` (the local server then issues 138-byte certificates naming libsignal's test
  certificate id 0x7357C357, width 5) behind an environment switch, 2 lines, plus a harness flag
  and a deployment with `certificate: 138`. Not done here because the local server is shared by
  other runs.

**B3. The server's handshake record sizes (unknown; tool ready).** `tls-open-handshake N` is one
circuit per encrypted handshake record size. Local: 43, 922, 94, 58 (Ed25519 certificate). Production's
chain, key type and record split are unknown; with an ECDSA key the CertificateVerify record varies
by a byte or two between connections. `measure_handshake.py production OUT --i-have-the-go-ahead`
*(go-ahead)* makes one OpenSSL handshake with our cipher, group, ALPN and SNI and prints the
`"handshake": [...]` setting (tested locally: it reproduces 43, 922, 94, 58). Run it two or three
times if the peer signature is ECDSA. Without the sizes, a strict session refuses the handshake;
a non-strict one produces the kernel during the handshake (tens of seconds; the server may time
the handshake out; the next attempt finds it in the cache).

**B4. The sender certificate expires (handled for now; no refresh).** The production certificate is
valid 7 days: the current one expires **2026-11-19 01:14 UTC**. The MPC client cannot refresh it
(PRODUCT_TODO section 2). `export-account` refuses an expired one and warns under 24 hours;
`run_real_test.py` refuses under 2 hours. A new certificate (same length, 134) needs a conventional
`GET /v1/certificate/delivery?includeE164=false` on the authenticated socket *(go-ahead)*, never
while a receive session is connected (the server closes the older socket, code 4409).

**B5. Resending after an ambiguous send needs the database nodes (handled by the plan).** The
recovery path (`deliver`: sent but not answered → reconnect, send again under new keys, at most 2
reconnects) runs only with `SIGNAL_DB_CLIENT`. Without it (`SIGNAL_LOCAL_STORE`) a dropped
connection ends the session and the stored state can be behind what was sent, so a rerun would
reuse a message key. `run_real_test.py` therefore always uses the database nodes (the harness's
in-memory test nodes, local to this machine; they live for the one process).

**B6b. After a signup refused at the token step, no further signup works in that session (bug,
change needed, pre-existing).** Found in the local test of the acknowledgement switch. A first
message that opens but whose text the database nodes refuse (a mistyped token, a used one) is
evicted with `contactEvict`, and `contact_evict` (`service_kernels.h` ~456) clears the contact's
state but keeps its entry in `conversations`; `envelope_session` requires that the id has no
entry (`!conversations.count(id)`, ~340), and the controller always uses the same provisional id
(2^128 − 1). The next first message in the session is rejected by the worker and the session ends
("native worker rejected the operation"). Refusals at the open step (the B1 case, receipts,
unsealed messages) create no entry and are not affected. Fix, small, either: an operation that
erases a contact's entry (worker, ~3 lines; `contact_evict` itself cannot erase, `reloadContacts`
evicts and reloads the same id), called by the controller's `refuse`; or a new provisional id per
received message in the controller (Lean, ~5 lines, needs a reserved id range). Consequence for
the run: with `SIGNAL_ACK_REFUSED=0` such a refused message stays first in the queue and every
later session dies on the signup behind it; run once with `--ack-refused` to clear it.

**B6. Trusted setup of the identity key (accepted for this test).** `account.json` holds the
identity key, password and prekey private keys in the clear; the export admits them into the
session (test admission, PRODUCT_TODO section 2). Fine for a first test; not the product.

### Already handled

| Item | Local test server | Production | Where |
|---|---|---|---|
| Host, port, SNI | 127.0.0.1:18443, `server.example` | `chat.signal.org:443`, SNI `chat.signal.org` | controller argv `ENDPOINT PORT HOSTNAME`; the export's `server`; the worker resolves the name itself (`getaddrinfo`, first address; today's registration went over IPv6) |
| HTTP `Host` header | ignored by the local server | `chat.signal.org` | fixed in `RelayUpgrade.lean` (both upgrades) |
| Route, ALPN, HTTP version | HTTP/1.1 | `chat.signal.org`, TLS ≥ 1.3, ALPN `http/1.1`, WebSocket upgrade: the route of `PROD.chat_domain_config` in the relay node's libsignal (fork rev c1d9fb5, `rust/net/src/env.rs` `DOMAIN_CONFIG_CHAT`), and the one the registration tool used today (trace: "connection through chat.signal.org:443 (direct) succeeded", `GET /v1/websocket/ HTTP/1.1`) | `TlsWire.Config` `alpn := ["http/1.1"]`. Official clients since libsignal 0.97.1 use `grpc.chat.signal.org` with h2: a fingerprint difference (CLIENT_FINGERPRINT.md (c)), not a functional one |
| TLS trust anchor | `local_signal_server/state/tls/ca.pem` | Signal's own root, pinned by libsignal (`SIGNAL_ROOT_CERTIFICATES` = `res/signal.cer`, identical in c1d9fb5 and v0.106.1): "Signal Messenger", RSA-4096, self-signed, 2022-01-26 to 2032-01-24, SHA-256 `DDB0F92B…DC9DF65A` | `real_signal/signal-root-ca.pem`; controller argv `TRUST`; `public_auth` checks chain (depth ≤ 10, up to 12 certificates), SAN host name, server purpose, security level 2 |
| CertificateVerify scheme | Ed25519 | unknown (RSA-PSS or ECDSA) | the libsignal profile offers `0807 0403 0804 0401 0503 0805 0501 0806 0601`; `public_auth` verifies 0804–0806, 0403/0503/0603, 0807 (the PKCS#1 ones are not allowed in TLS 1.3 CertificateVerify and are refused) |
| Sealed-sender trust roots | the upstream test root `BS/lfaNH…` | `BXu6QIKV…HWMF` and `BUkY0I+9…xuk6` (Signal-Android's; secret-shared-db's relay config) | `lss-provision export-account` validates the server certificate against the target's roots offline; for the real account it matched `BUkY…` (libsignal `KNOWN_SERVER_CERTIFICATES` id 3). The controller is given the validated server key, certificate and id (`sealed_sender_server`), never a root |
| Our sender certificate's form | 244 bytes, embedded signer | 134 bytes, signer by reference (id 3), UUID bytes | `ReceiveFirst.certShape` covers all four forms; see B2 for the circuits |
| Socket password | 22 characters | 22 (the registration tool samples 22 base64url characters) | `signal-upgrade 22`. Android's are 24: a fingerprint difference (PRODUCT_TODO section 8) |
| Our prekey ids | small (varint width 1) | random 24-bit: signed and Kyber width 4; no one-time prekeys uploaded | `deployment-production.json`: `signup_signed 4`, `signup_kyber 4`, `signup_one_time 0` (from the export's `deployment-hints.json`) |
| A phone's sender certificate | 244 | 134 without a phone number (Android's default "nobody" sharing), 136 + n with one of n characters | `signup_certificates` `134:0:0`, `148:255:12` (+1 numbers); other lengths are produced on demand or refused, recorded |
| Responses and records | record classes up to 6144 | the same classes; a send's response is ~150 bytes; the upgrade response may carry headers the local server does not send | the upgrade validator accepts any syntactically valid headers; a record above 6144 is refused (`record_max`, CIRCUIT_SHAPES "Not done" 6) |
| Contacts with linked devices | tested (`--multi-device`) | a phone user with Desktop or iPad: first send answered 409 → prekey fetch → one message per device | `bundle_items` covers 3–5-digit registration ids, 7–8-digit key ids and 0/3/4-digit one-time ids; other digit counts are refused (CIRCUIT_SHAPES "Not done" 3) |
| Export without contacts | n/a | a real account has none | `readExport` accepts an empty `contacts` list (changed) |
| Never a receipt | | | no request kind exists for one: the only requests are sealed text sends, prekey fetches, keepalives, pings and 200 replies to server requests; the content is always a `DataMessage` (body, timestamp) |
| Signups sealed sender only | | | a delivered envelope is processed only if its type is 6 (UNIDENTIFIED_SENDER); any other type is refused and recorded; sends are always sealed on the unauthenticated socket, and a 401 is "needs re-signup", never an unsealed retry |

### Unknown until we connect (each is recorded when it happens)

- **Rate limits and challenges.** A sealed send passes Signal's spam checker (closed source in
  production; the open-source one does nothing) and an inbound-bytes limit per recipient. The
  controller treats 429 and 5xx as back-off (`Retry-After`, at most 60 s, 3 retries), 401 as
  "needs re-signup", 404 "gone", 409/410 a device refresh, and anything else (428 challenge, 403,
  413) as "fault" without retrying. The prekey fetch (only after a 409) has its own limit.
- **Idle limits.** We ping after 31 s without a record on the receive socket (libsignal's
  interval); the send socket sends nothing while the engines work. The local server closes after
  90 s; production's limit is unknown. Close codes 4401 (invalidated) and 4409 (connected
  elsewhere) are recorded as a closed connection.
- **The phone's first message** (B1): envelope size, content padding, hint, certificate length.
- **Whether the server accepts our ClientHello** (one cipher, X25519 only, `psk_dhe_ke`): BoringSSL
  servers do; a HelloRetryRequest for another group ends the handshake (recorded).
- **Consistency the server can see**: this machine's address already registered the account with
  user agent `relay-node libsignal/0.8…`; the sessions announce `Signal-Android/8.36.0 …
  libsignal/0.107.0`; the account declared only the `spqr` capability (Android declares many);
  the client Finished leaves about a second after the server's flight. None is a protocol error;
  all are visible (CLIENT_FINGERPRINT.md).
- **Message timestamps older than the send.** In the local run of `run_real_test.py` the text's
  timestamp was taken 40 s before its request left (semi-honest; the contact's first preparation
  and seal run after the stamp, `restamp` in `sendSoft`). The server and the phone see a message
  "sent" 40 s before it arrived; an official client's is milliseconds old. Fix: stamp after the
  preparation (`ensurePrepared` before `restamp`), or accept it.
- **What the phone does after our reply**: delivery and read receipts, which arrive at our account
  as sealed messages that are not first messages (refused; kept on the server with
  `SIGNAL_ACK_REFUSED=0`, so the queue grows until a later run acknowledges them).

## 2. Recording (`SIGNAL_RECORD`)

Each controller appends one JSON line per event to its own file, with `time_ms` from its clock.
`run_real_test.py` sets `real_signal/state/runs/RUN/record-{receive,send}-party-{0,1}.jsonl`.

| Event | Fields | When |
|---|---|---|
| `connect`, `connected` | endpoint, port, host name, socket kind, proxy, circuits, profile | before and after the TCP connection |
| `server-certificate` | host name, trust file, signature scheme, transcript hash, the whole chain (DER, hex), accepted, checker error | each handshake |
| `handshake` | certificate verified, Finished verified | each handshake |
| `sent-public` | connection, the bytes (hex) | every public record we send: unauthenticated upgrade, 200 replies to server requests, keepalives, pings, close frames |
| `sent-private`, `sent-private-prekey-fetch` | connection, contact id, request id, timestamp, frame size, the frame with its private slots zero (hex) | every send and prekey fetch |
| `record` | connection, handle, content size | every record received |
| `revealed` | handle, offset, bytes (hex) | every revealed range: upgrade responses, response status and headers, server request verbs, paths and headers, envelope headers |
| `passed-over` | handle, offset, size, where it went | every unrevealed range: request and response bodies, a delivered envelope's sealed content |
| `envelope`, `envelope-refused` | envelope type, content size; outcome (new contact id) or the reason it was refused | every delivered message |
| `server-request` | delivered message or not, refused, answered | every server request |
| `response` | contact, message, request id, answered, status, Retry-After | every send's response (recovery path) |
| `recovery` | the controller's recovery notes | 409/410 refreshes, back-offs, reconnects, results |
| `closed` | where | the server closed the receive socket |

Also in the run directory: `plan.json` (configuration, binary and manifest hashes, git head and
diff hash, deployment hints; no secrets), `timeline.jsonl` (the launcher's steps with times),
`{receive,send}-party-N.log` (controller and worker stderr, including every worker operation with
its time and cost), `{receive,send}-party-N.json` (each controller's final report: results,
envelopes, refusals, error), `kernels-requested.txt`, `kernels-refused.txt` (strict mode),
`token.txt`, `report.json`.

**Cannot be recorded, because it stays secret-shared or encrypted:** the private slots of our
requests (the recipient's Signal id and access key, device and registration ids), our credentials
in the authenticated upgrade, every TLS key, and a delivered message's sealed content unless it is
accepted (then only its text and the new id are public). Refused messages are therefore recorded
by their envelope header, sizes and reason only; their content stays on the server when
`SIGNAL_ACK_REFUSED=0`. The raw ciphertext on the wire is not written by the controllers; for that,
run a capture on the leader during the test (`sudo tcpdump -i any -w RUN/wire.pcap tcp port 443`).

## 3. Run sequence

Offline (now):

1. `lss-provision export-account real_signal/state/account.json real_signal/state/export production`
   — done 2026-11-11: certificate 134 bytes, signer id 3, matched root `BUkY…`, valid 167 hours.
   Records `real_signal/state/export/{mpc-export.json, credentials-party-{0,1}.hex, deployment-hints.json}`.
2. Fix B1 and B6b; add the profile kernels to the inventory and run the compact-certificate local
   stage (B2).
3. `python3 real_signal/run_real_test.py local --export DIR --local-account NAME` against the local
   server (the same launcher and recording, with `lss-provision export-account … local` from a local
   account; section 4).

With the owner's go-ahead:

4. *(go-ahead)* `python3 real_signal/measure_handshake.py production real_signal/state/handshake.json --i-have-the-go-ahead`
   (twice more if the peer signature is ECDSA). Records the chain, record sizes, ALPN, group,
   signature scheme. Put the sizes in `deployment-production.json` `handshake`.
5. Offline: `python3 scripts/guarded.py 16 3600 python3 scripts/produce_circuits.py real_signal/deployment-production.json real_signal/state/circuits`
   with `SIGNAL_CLIENT_PROFILE=libsignal` (after B2). Records the manifest and its hash.
6. Offline: `python3 real_signal/run_real_test.py production --export real_signal/state/export --dry-run [--manifest real_signal/state/circuits/manifest.txt]`.
   Records `plan.json`; must list no problems (certificate time, binaries, manifest).
7. *(go-ahead)* Optionally start the packet capture; then
   `python3 real_signal/run_real_test.py production --export real_signal/state/export --i-have-the-go-ahead [--manifest …]`,
   type YES. It starts the database nodes, issues the signup token and prints it.
8. On the phone: find the account by its username, send the printed token as one message.
   The receive session (already connected) records the delivery; the contact is stored and the
   message acknowledged, or the message is refused, recorded and left on the server.
9. The launcher then sends one text back on a new unauthenticated socket and records the
   response. Check on the phone that it arrived, and write what the phone showed into the run
   directory (`notes.txt`).
10. Stop at once, and do not retry, on: a 428 or 403 to any of our requests, a close code
    4401/4409, an `x-signal-alert` header in any revealed response, a refused handshake. The run
    directory has the full record.

After the test: the phone's receipts will be waiting for the account as refused messages; a later
receive session with `--ack-refused` clears them (each is still recorded).

## 4. Tested here (2026-11-11/12, offline and local server only)

- `lss-provision export-account` on the real `account.json` (production, offline): writes the
  export; certificate 134 bytes, by reference, key id 3, root `BUkY…`, 167 hours left, signed and
  Kyber id width 4, no one-time prekeys. `production` refuses a file that is not marked production;
  `local` refuses one that is.
- `measure_handshake.py local`: 43, 922, 94, 58 (the local deployment's sizes), verified,
  `http/1.1`, X25519, Ed25519.
- `circuit_inventory` on `deployment-production.json`: accepted, 396 kernels.
- **The whole flow against the local server, from an account file in the registration tool's exact
  format** (a local account, `register NAME NUMBER unrestricted`, rewritten into `account.json`'s 27
  fields): `export-account … local`, then `run_real_test.py local` (semi-honest, libsignal profile,
  in-memory database nodes, `SIGNAL_ACK_REFUSED=0`): the receive session created the account row,
  received the signup (2305-byte sealed content), stored the contact under the token's id and
  acknowledged it (5 s); the send session delivered one text, 200, and the new user's libsignal
  client decrypted it from an envelope without source fields (47 s). Recorded: 164 events per
  party for the receive session, 85 for the send.
- **The acknowledgement switch** (`.deps/lowering-scratch/check_ack_refused.py`): a valid signup
  followed by a first message whose text is not a token. Session 1 stored the first and answered
  it, recorded the second as refused ("the text is not a signup token …") and did not answer it,
  and kept waiting (a refusal does not count). Session 2 received the refused message again,
  refused and did not answer it again.
- `public_service_controller recovery-check`: passes. Other agents' harness runs (`--db
  --multi-device`, `--circuits 2 --circuits-db`, `--ceremony`) built and ran the controller with
  these changes while they were in place.

## 5. Where the target is configured

Nothing in the controller assumes the local server: the target is the session's arguments
`ENDPOINT PORT HOSTNAME … TRUST` (the harness passes `127.0.0.1 18443 server.example
state/tls/ca.pem`; `run_real_test.py` passes the export's `server` block; the node daemon has the
same four values in its configuration, `signal.endpoint`, `port`, `hostname`, `trust_root`). The
sealed-sender trust root enters only through the export (`sealed_sender_server`, validated by
`export-account` against the target's roots). Fixed in Lean, and correct for production: the HTTP
`Host: chat.signal.org` and ALPN `http/1.1`. So no change was needed; the default stays the local
server wherever the harness runs.
