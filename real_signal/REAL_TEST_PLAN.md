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

## 0a. The second real run (2026-11-12, 08:40 local): passed

Run `state/runs/20261112-164009-production` (malicious, strict with the 414-kernel manifest,
libsignal profile, real database nodes kept under the run directory). The owner ran it and
confirmed the text arrived.
- Receive, 56.4 s: one 2,265-byte envelope delivered and accepted (the phone's second signup,
  taken with `SIGNAL_RECEIVE_JUMP=3`), 484 bytes revealed, nothing refused, 2 keepalives.
- Send, 44.8 s: the reply was answered 409, one refresh, 3 sessions established, the reply sent
  again: "delivered after device refresh". 647 bytes revealed, nothing refused, no unknown
  events, certificate verified in both sessions.
- The contact is stored in that run's database, so `--resume` on this run directory sends again
  without a new signup.

## 0. The first real run (2026-11-12) and what changed after it

Run `state/runs/20261112-074913-production` (malicious, strict with the 436-kernel manifest,
libsignal profile, in-memory database nodes). **The signup worked; the reply did not reach the
phone.** From the run's records (`.deps/lowering-scratch/record_events.py`, `unmask.py`,
`time_breakdown.py` print them):

**Receive session, 55.6 s, exit 0.** Connection, handshake (the 1122-byte flight, as measured),
upgrade: 3.7 s. Then idle, waiting for the phone (a ping after 31 s, as designed), 44 s. The
signup arrived at 48.5 s in one record of 2,402 bytes (`tls-open-typed 2560`): envelope type 6,
sealed content 2,265, unsealed content 2,171, PreKey message 2,027, ciphertext 240 (Android's
layout, as B1 predicted), hint RESENDABLE, sender certificate 134 without a phone number, the
phone's registration id two varint bytes, addresses present, post-quantum field 37 bytes:
`receive-session 134 2027 0 2 4 4 1 1 240 1 1 0`, a shape the manifest had. (The `4 4` are OUR
signed and Kyber prekey ids' widths, which the phone's message names; the phone's own key ids
are never visible.) The controller passed the 2,265 bytes over in 1.2 s, the engines opened the
message (2.9 s) and built the session (2.1 s), the contact was stored and the message
**acknowledged at 55.06 s**: the record's `server-request` event with `delivered_message: true,
answered: true`, and the `sent-public` frame after it, which is a WebSocket response with status
200 to the server's request id (decoded: `unmask.py`). So the message is off the server's queue
and will not be delivered again. Worker busy time 8.8 s of the 55.6.

**Send session, 20.8 s, exit 1 on both.** Connect, handshake, upgrade 4.1 s; the contact read
back from the database nodes and prepared, 0.6 s; sealed (`signal-seal-official 134 2`), 1.0 s;
the advanced state stored and acknowledged by the database nodes (`contactSeal`, then the
parties' exchange) **before** the request left at 7.1 s (928-byte frame; the message's timestamp
was then 2.0 s old). **409** at 7.5 s, body 42 bytes: `{"missingDevices":[…],"extraDevices":[]}`
has 39 fixed characters, so the list is three characters, two device ids of one digit each. The
prekey fetch left at once; the 200 came at 10.3 s in ONE record of 7,843 bytes (body 7,727),
opened with `tls-open-typed 8192` (listed). Then the controllers spent **10.2 s** in the clear
passing over the 7,727 unrevealed bytes (finding: superlinear, PRODUCT_TODO section 5), and the
worker asked for `bundle-shape 8192`, which the manifest did not have (`bundle_max` followed
`devices: 2`): refused, "native worker rejected the operation", both controllers exited 1.
Worker busy 7.0 s of the 20.8.

**What the sizes say about the contact.** A 7,727-byte body is exactly three devices
(two: at most 5,200; four: at least 9,986), and only with a one-time EC prekey on each of the
three (with two or fewer the remaining digits would exceed what the numbers can hold); the 15
numbers then have 72 digits, the three device ids 3, so registration ids and key ids average
about six digits. An Android primary's key ids are random 24-bit numbers (7 or 8 digits), so at
least one linked device has shorter ids: outside `bundle_items` (7–8 digits for linked devices)
even if `bundle-shape 8192` had been listed. Which device has which numbers, and what the 409
body names, cannot be known: neither body is ever revealed (only their lengths and the opened
punctuation flags, which never ran here).

**State left by the run.** The contact's state was on the harness's in-memory database nodes,
which `run_real_test.py` stopped at the end: **it is gone**; no resume is possible for this run.
Its stored state had been advanced past the message that got the 409 (stored before every
send), so a resend from it would have sealed under the next key, never the same one; this is
what `--resume` now relies on (section 3). The phone has a session with our account that it
started and that was never answered.

**Changed (2026-11-12), offline and against the local server only:**
- `bundle-slot FIRST LAST ONETIME` (`TlsMpc/BundleSlotKernels.lean`): one circuit per item
  position and one-time flag for EVERY digit count (the item is spliced into fixed-width number
  slots; CIRCUIT_SHAPES.md). Enumerating `bundle-item` for realistic ranges would have been about
  11,500 kernels. Checked against a JSON parse for every digit count (`check_bundle_slots.py`).
- `deployment-production.json`: `devices 4`, `bundle_slots 1`, `device_lists pending`,
  `record_max 12288` with `scan_record_max 10240`, `signup_jump [3]`. Sizes per device count:

  | Devices | Prekey response body | Record (content) | Record class | Request frame, class 2 |
  |---|---|---|---|---|
  | 1 | 2,552–2,637 | ≤ 2,747 | 3072 | about 3.1 KB |
  | 2 | 5,030–5,200 | ≤ 5,304 | 6144 | about 6.2 KB |
  | 3 | 7,508–7,763 (the real one: 7,727) | ≤ 7,861 | 8192 | about 9.3 KB |
  | 4 | 9,986–10,326 | ≤ 10,419 | 10240 or 12288 | about 12.4 KB |
  | 5 (not covered) | 12,464–12,889 | ≤ 12,976 | 14336 | about 15.5 KB |
  | 6 (the server's limit) | about 15,400 | about 15,500 | 16384 | over one record: "retry later" |

  (Bodies from the template with 3–5-digit registration ids and 6–10-digit key ids; the record
  adds 116 bytes of framing and headers.) `record_max 10240`, as before, allows three devices
  always and four only with short numbers. The framing-scan kernels of 12288 and up do not lower
  under the 16 GB cap, but they run only on handshake records, so above 10240 only
  `tls-open-typed` and `tls-reveal-masked` are listed (`scan_record_max`). `tls-open-typed 12288`
  itself is 4.58M AND gates and peaks at **23.6 GB** to produce (59 s): hence `--max-gb 26`.
  `14336` (five devices) would be about 5.3M AND gates and, by the same growth, over 30 GB: not
  attempted on this 48 GB machine (crash history). **Five or more devices are therefore not
  covered**: the response record is refused in strict mode and the session ends (the contact's
  stored state is untouched; nothing is sent). Beyond that: an opening kernel that takes a long
  record in pieces (the decryption is per block; the parser's state would be carried between
  pieces), or a lowering that uses less memory per gate.
- The receive kernels accept a first message that is the sender's number 0 to 3 of its
  unanswered session (`SIGNAL_RECEIVE_JUMP=3`, set by the launchers; `signup_jump [3]`). Needed
  for the next run: the phone's next token goes out as message 1 of the session it started
  for the first one, which we never answered (with jump 0 it would be refused).
- `run_real_test.py`: real database nodes by default (`--db real`: secret-shared-db's node
  binary with a private Postgres under `RUN/db/real`, kept after the run), `--resume RUN` (only
  the send, to the contact RUN stored), `--stop-after receive` (for testing).

## 1. Gap list

Status: **handled** (works for production as it is), **change needed** (file, size), **unknown**
(only a connection shows it). Blocking items first.

### Blocking

**B1 — FIXED 2026-11-12.** `ReceiveFirst.withAccessKey` now accepts, between the body and the
profile key, any of 72 layouts (`ReceiveFirst.gaps`: `flags` 4, `expireTimer` 5 of any value,
`expireTimerVersion` 23, each absent or a varint; Wire's declaration order, which Signal-Android
uses, and tag order), chosen inside the circuit: the opened status still says only "a layout
matched" (NEEDS_REVIEW 3e). Kernel name and inputs unchanged; `withAccessKey_map` kept (no new
axioms). What the phone is now expected to send for the 108-character token:
`0A len (0A 6C token ‖ 28 00 ‖ B8 01 01 ‖ 32 20 profileKey ‖ 38 timestamp(6) ‖ 70 00)`, 161 bytes,
padded to 239, **240 bytes of ciphertext**, sealed with hint RESENDABLE (`20 01`), sender
certificate 134 bytes (no phone number). Tested: kernel level on 11 layouts
(`.deps/lowering-scratch/check_access_key_layouts.py`), and end to end
(`local_signal_server/check_signal_service_local_signup.py`, section 4). Still unknown until the
phone's message: the post-quantum field's size (`signup_pq`, 37 for libsignal 0.106; the phone has
0.107) and whether addresses are present; both are shape parameters of `receive-session`.
Original text:

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

**B2 — DONE 2026-11-12.** `CircuitInventory.lean` has a `profile` setting (`libsignal`:
`signal-seal-official`, `bundle-seal … 80c−1`), `produce_circuits.py` names the request kernels
under the same profile, and `deployment-production.json` sets `profile: libsignal`. The local
compact-certificate stage runs strict with the libsignal profile (a second server instance,
`scripts/start_compact_server.sh`, ports 19080/19081/19443, `embedSigner: false`; the default
instance is untouched): passes semi-honest and malicious (section 4). The production set is
produced into `real_signal/state/circuits/` (see step 5). Original text:

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

**B3 — MEASURED 2026-11-12 (owner's go-ahead), handled.** `state/handshake-production.json`:
chat.signal.org sends EncryptedExtensions (49), Certificate (927: ONE certificate, Ed25519 key,
signed by the pinned RSA root), CertificateVerify (72, Ed25519) and Finished (36) coalesced in ONE
encrypted record of **1122 bytes**, with 16 bytes of record padding; ALPN http/1.1, X25519. Our
path handles that as it is: the worker opens each record with `tls-open-handshake SIZE` (the inner
parser strips padding), and `TlsClient.receiveFlight` splits the decrypted bytes into messages
by their own headers (`TlsWire.messages`, any number per record, split across records too), then
checks the chain (`public_auth`: one certificate, path built to the trust file), the Ed25519
CertificateVerify (0x0807, offered by the libsignal profile) and Finished. Nothing about the
split is taken from fixed offsets. The local default server never showed this shape (OpenSSL: 4
records, two certificates); the second local instance does (`scripts/coalesced_terminator.py`, a
small TLS 1.3 server: one record of 621 bytes, 16 bytes of padding, one Ed25519 certificate) and
the compact strict stage runs through it (section 4). `deployment-production.json`:
`handshake: [1122]`. Ed25519 signatures have a fixed length: the size changes only with a new
server certificate (re-measure then). Original text:

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
reuse a message key. `run_real_test.py` therefore always uses the database nodes. Until
2026-11-12 these were the harness's in-memory test nodes, which live for the one process (the
first real run's contact was lost with them); now by default the real node binary with its own
Postgres under the run directory, kept, so `--resume RUN` can retry the send (section 3).

**B6b — FIXED 2026-11-12** (the controller option: Lean only, `PublicServiceController.lean`
`provisionals`): every opened message gets its own provisional id (2^128 − 1, then 2^128 − 3,
2^128 − 4, …; both controllers count in lockstep), so an evicted entry never blocks the next
signup. Tested: a refused signup (not a token) first, then four good ones, in one receive session:
the first refused, all four stored (section 4). Original text:

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
| Responses and records | record classes up to 6144 | the same classes; a send's response is ~150 bytes; the upgrade response may carry headers the local server does not send | the upgrade validator accepts any syntactically valid headers; `record_max` is now 10240 in `deployment-production.json` (2026-11-12: a frontend packs queued WebSocket frames into one record; locally two queued deliveries made an 8192-class record, which 6144 refused in strict mode). 12288 and up do not lower under the 16 GB per-kernel cap: a record above 10240 (five or more deliveries queued in one record) is refused, the session ends and the messages stay on the server |
| Contacts with linked devices | tested (`--multi-device`) | a phone user with Desktop or iPad: first send answered 409 → prekey fetch → one message per device | since 2026-11-12 `bundle-slot`: any digit counts; up to four devices (section 0). Before: `bundle_items` (3–5-digit registration ids, 7–8-digit key ids); the first real run's contact (three devices, mixed widths) would have been refused there too |
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
- **Message timestamps older than the send (2026-11-12: cause found, partly changed).** The
  libsignal profile's `restamp` now prepares the contact (operation 66) before it stamps. But the
  40 s were not the preparation (0.3 s): they were operation 41 producing the
  `signal-seal-official` circuit on demand (the cache was cold). With the circuits produced ahead
  (step 5) the stamp is taken about a circuit load, a seal and the database write before the
  request leaves; measured in the compact strict stage (section 4). Original text:
  In the local run of `run_real_test.py` the text's
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

### The next run (after 2026-11-12's), in order

All commands from the repository root. Steps A and B are offline; C and D contact Signal's
service and are run by the owner only.

A. Produce the production circuits (again after any change to the Lean kernels; the cache, and
   with it every pin, belongs to the emitter binaries), one heavy job:

       python3 scripts/guarded.py --heavy 28 10800 python3 scripts/produce_circuits.py real_signal/deployment-production.json real_signal/state/circuits --max-gb 26

   `--max-gb 26` because `tls-open-typed 12288` (the four-device prekey response) peaks at
   23.6 GB; everything else stays under 12.3 GB. **Done 2026-11-12** (05:00 local): 414 kernels,
   412.6M AND gates, 31.1 GB of gate lists, 43 min with the earlier production's kernels in the
   cache (from an empty cache: about 1.5 to 2 hours). Against the 436 of the first run: +8
   `bundle-slot`, +4 `bundle-shape` (7168 to 12288), `tls-open-typed 12288` and its
   `tls-reveal-masked`, +18 stored-list sizes (up to four unanswered devices), the four
   `receive-session` shapes at jump 3 instead of 0, 60 `bundle-request-ctr` frames (one to four
   unanswered devices, both message classes; 163M AND gates, 14.2 GB, the bulk of the growth);
   −90 `bundle-item`, −12 request frames with established devices.
B. Dry run (no connection; writes a run directory with `plan.json`, which must list no problems):

       python3 real_signal/run_real_test.py production --export real_signal/state/export --manifest real_signal/state/circuits/manifest.txt --dry-run

C. *(go-ahead)* The run, with the persistent database nodes (the default `--db real`):

       python3 real_signal/run_real_test.py production --export real_signal/state/export --manifest real_signal/state/circuits/manifest.txt --i-have-the-go-ahead

   It prints a NEW token. The first run's contact is gone (in-memory nodes), so the phone signs
   up again: send the new token as one message. Phone side: this is the second message of the
   session the phone started on 2026-11-12, which we never answered, so it goes out as a PreKey
   message with counter 1; the receive kernels now accept counters 0 to 3
   (`SIGNAL_RECEIVE_JUMP=3`). The old token is meaningless (it was signed by the first run's
   in-memory application keys). Expected then: our reply answered 409, a refresh of three
   devices (about 30 s in malicious mode), the reply sent again to all three, 200, "delivered
   after device refresh". Check all three devices.
D. *(go-ahead)* If the receive stored the contact but the send failed (any reason): retry ONLY
   the send, for that contact, without a new signup:

       python3 real_signal/run_real_test.py production --export real_signal/state/export --manifest real_signal/state/circuits/manifest.txt --resume real_signal/state/runs/RUN --i-have-the-go-ahead

   RUN is C's run directory. It restarts that run's database nodes (Postgres and five nodes under
   `RUN/db/real`, same ports and keys), waits one epoch, and sends. The stored state is always
   the one advanced past the last message that may have left (it is written and acknowledged
   before each send), so the resend seals under new keys; a duplicate is possible, a reused
   message key is not.

The earlier sequence, kept for the record:

Offline (now):

1. `lss-provision export-account real_signal/state/account.json real_signal/state/export production`
   — done 2026-11-11: certificate 134 bytes, signer id 3, matched root `BUkY…`, valid 167 hours.
   Records `real_signal/state/export/{mpc-export.json, credentials-party-{0,1}.hex, deployment-hints.json}`.
2. ~~Fix B1 and B6b; add the profile kernels to the inventory and run the compact-certificate local
   stage (B2).~~ Done 2026-11-12 (section 4).
3. `python3 real_signal/run_real_test.py local --export DIR --local-account NAME` against the local
   server (the same launcher and recording, with `lss-provision export-account … local` from a local
   account; section 4).

With the owner's go-ahead:

4. *(go-ahead)* `python3 real_signal/measure_handshake.py production real_signal/state/handshake.json --i-have-the-go-ahead`
   (twice more if the peer signature is ECDSA). Records the chain, record sizes, ALPN, group,
   signature scheme. Put the sizes in `deployment-production.json` `handshake`.
5. Offline: `python3 scripts/guarded.py 20 3600 python3 scripts/produce_circuits.py real_signal/deployment-production.json real_signal/state/circuits`
   (the profile now comes from the deployment's `profile` setting). **Done 2026-11-12**: 436
   kernels, 17 GB, 23.5 min, peak 10.5 GB per kernel; every file present and hashing as pinned;
   the 195 kernels it shares with the compact local manifest are pinned identically (the strict
   local stage ran with exactly those). Redo it after any change to the Lean kernels if the run
   is non-strict (the cache is keyed by the emitter binary); a strict run reads the manifest's
   own directory and is unaffected. Recommended: run step 7 with `--manifest
   real_signal/state/circuits/manifest.txt` (strict) and the default `SIGNAL_ACK_REFUSED=0`: a
   signup of an unlisted shape (e.g. another `signup_pq`) is refused, recorded in
   `kernels-refused.txt` and kept on the server; produce that shape and run again. Non-strict, a
   cold shape is produced while connected (90 s locally), and the local server closed the idle
   socket (1001) meanwhile.
6. Offline: `python3 real_signal/run_real_test.py production --export real_signal/state/export --dry-run [--manifest real_signal/state/circuits/manifest.txt]`.
   Records `plan.json`; must list no problems (certificate time, binaries, manifest). Not run on
   2026-11-12: the agents' permission classifier refused even the dry run; the owner runs it.
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
- **2026-11-12, B1/B6b/B2/B3/timestamps** (`local_signal_server/check_signal_service_local_signup.py`,
  the real run's launcher pieces, libsignal profile, in-memory database nodes): queue = a refused
  signup (Android layout, text not a token), then signups in the `legacy`, `android` (Wire order:
  expireTimer 0, expireTimerVersion 1, isViewOnce, 80k−1 padding, hint RESENDABLE),
  `android-tag` and `android-timer` (one-week timer, version 2) layouts; then one reply to the
  `android` contact, which the server accepts only with the access key the engines derived from
  that layout's profile key (the test senders are not unrestricted).
  - default server, semi-honest, non-strict: refused 1, stored 4, reply delivered and decrypted.
    The receive session then got the server's close 1001 "Connection Idle Timeout": the first
    envelope took 90 s because its circuits were produced on demand (cold cache after the Lean
    change). Another reason to produce the circuits ahead (step 5).
  - **compact-certificate instance, strict** (`--compact --manifest
    local_signal_server/state/circuits-compact/manifest.txt`, `deployment-compact.json`, 283
    kernels): our certificate 138 bytes by reference (signer 0x7357C357), the senders' 138, the
    handshake ONE coalesced 621-byte record with padding and one Ed25519 certificate
    (`coalesced_terminator.py`), every kernel from the manifest, none refused. Semi-honest:
    receive 15.5 s for 5 messages, send 3.7 s, the reply's timestamp 1.4 s old at the server.
    Malicious: receive 37.1 s, send 7.6 s, timestamp 2.3 s old. The first malicious attempt was
    refused `tls-open-typed 8192` (two deliveries packed into one record) with `record_max`
    6144: now 10240 in both deployments.
- `public_service_controller recovery-check`: passes. Other agents' harness runs (`--db
  --multi-device`, `--circuits 2 --circuits-db`, `--ceremony`) built and ran the controller with
  these changes while they were in place.

- **2026-11-12, after the first real run** (offline; this machine):
  - `check_bundle_slots.py` (under `guarded.py 12`): the eight `bundle-slot` kernels against a JSON
    parse of responses of one to five devices with every digit count (device id 1–3, registration
    id 1–5, key ids 1–10, with and without one-time prekeys, including a 72-digit three-device
    account like the real one): 18 items, every field equal; the Lean splice equal to an
    independent one; 251 altered inputs (wrong digit counts, 0, beyond the slot, padding not `0`,
    a leading zero, out of range, template text) all release nothing.
  - Lean: `BundleSlots.slotValid_map`, `deviceSlots_map`, `bundleSlot_spec`, `slot_rejects`,
    `compiled_correct`: standard axioms only (`[propext, Quot.sound]`, the last also
    `Classical.choice`); no `sorry`, `native_decide`, `bv_decide`.
  - `circuit_inventory`: production 351 kernels before the request frames (414 produced in all);
    compact local 350 (413 produced: `local_signal_server/state/circuits-compact/manifest.txt`,
    60 min, peak 23.6 GB for `tls-open-typed 12288`).
  - The persistent database nodes: started, an epoch applied, stopped, started again from their
    Postgres data with `run_real_test.reopen_cluster` (10.3 s), an epoch applied after the restart
    (48.6 s), same tables (`.deps/lowering-scratch/test_db_restart.py`, 141 s).
  - `public_service_controller recovery-check`: passes (29 checks).
  - **Run 2026-11-12 (afternoon), all passed: the local 2/3/4-device reproduction and the local
    `--resume` test** (logs `.deps/lowering-scratch/out/h1…h11-*.log`). They had been blocked in
    the morning by OrbStack's Docker daemon not answering; once it was back, the commands below
    were run in this order:
    - malicious, 3 / 2 / 4 devices (h1–h3; 92 s, 57 s, 89 s, peak 14.1–14.9 GB) and semi-honest,
      3 / 2 / 4 devices (h4–h6; 36 s, 27 s, 43 s, peak 7.6–8.9 GB): in each, the Android-layout
      signup received (both parties passed), the devices linked, the reply answered 409, the
      contact refreshed, the resend `delivered after device refresh`, and the account and every
      linked device (`signup-…-u0`, `.2`, `.3`, `.4`) decrypted the reply; `kernels_refused` empty;
    - `android again:android`, malicious (h7, 28 s): the second signup with the same token was
      refused at the token step (`envelope-refused`: "the new contact could not take the token's id
      …"), no second contact; the first reply `delivered`;
    - the resume test (h8, h9): the first run stopped after receive (`stopped-after-receive`), the
      account got a linked device, and the resumed run (database nodes restarted from their data,
      10.2 s) sent with the send answered 409, `delivered after device refresh`, and `realtest-user`
      decrypted it; passed;
    - and, after them, two `check_signal_service_local.py` runs (h10 `local-signup`, 140 s; h11
      `local-db`, 173 s), both passed.

    The commands (each one heavy job, about 1–2 minutes):

        python3 scripts/guarded.py --heavy 20 600 python3 local_signal_server/check_signal_service_local_signup.py malicious --compact --manifest local_signal_server/state/circuits-compact/manifest.txt --devices 3
        python3 scripts/guarded.py --heavy 20 600 python3 local_signal_server/check_signal_service_local_signup.py malicious --compact --manifest local_signal_server/state/circuits-compact/manifest.txt --devices 2 --one-time 0
        python3 scripts/guarded.py --heavy 20 600 python3 local_signal_server/check_signal_service_local_signup.py malicious --compact --manifest local_signal_server/state/circuits-compact/manifest.txt --devices 4
        (the same three with semi-honest)
        python3 scripts/guarded.py --heavy 20 600 python3 local_signal_server/check_signal_service_local_signup.py malicious --compact --manifest local_signal_server/state/circuits-compact/manifest.txt android again:android

    The first three: an Android-layout signup, then 1, 2 or 3 linked devices (`--one-time`: their
    one-time EC prekeys, default 5, 0, 5), the reply answered 409, refresh, resend, and every
    device must decrypt; `report.json` has the statuses, the prekey response size and the record
    sizes. The last: the same token sent twice (a redelivered or repeated signup): the second must
    be refused at the token step, no second contact. Then the resume test, with the export of
    one of those runs (`real_signal/state/runs/STAMP-local-signup-compact/export`, account
    `signup-NNNNNN` from its `timeline.jsonl`):

        python3 scripts/guarded.py --heavy 20 600 python3 real_signal/run_real_test.py local --export EXPORT --local-account ACCOUNT --manifest local_signal_server/state/circuits-compact/manifest.txt --stop-after receive
        python3 .deps/lowering-scratch/lss_compact.py link realtest-user 5
        python3 scripts/guarded.py --heavy 20 600 python3 real_signal/run_real_test.py local --export EXPORT --local-account ACCOUNT --manifest local_signal_server/state/circuits-compact/manifest.txt --resume real_signal/state/runs/RUN

    (RUN: the first command's run directory.) Expected: the resumed send answered 409, two
    devices refreshed, "delivered after device refresh", `realtest-user` decrypts (and
    `realtest-user.2`: `lss_compact.py receive realtest-user.2`).

## 5. Where the target is configured

Nothing in the controller assumes the local server: the target is the session's arguments
`ENDPOINT PORT HOSTNAME … TRUST` (the harness passes `127.0.0.1 18443 server.example
state/tls/ca.pem`; `run_real_test.py` passes the export's `server` block; the node daemon has the
same four values in its configuration, `signal.endpoint`, `port`, `hostname`, `trust_root`). The
sealed-sender trust root enters only through the export (`sealed_sender_server`, validated by
`export-account` against the target's roots). Fixed in Lean, and correct for production: the HTTP
`Host: chat.signal.org` and ALPN `http/1.1`. So no change was needed; the default stays the local
server wherever the harness runs.
