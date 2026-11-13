# What the Signal server sees of this client, compared with an official client

Written 2026-11-11 (branch `two-party-hybrid-worker`). Goal: the server (and anything that
terminates TLS for it) should not be able to single this client out among official Signal
clients. PRODUCT_TODO.md section 8 ("Being recognisable is separate from being located") tracks
the work; this file is the field-by-field comparison behind it.

## How the reference was obtained, and how far to trust it

1. **libsignal could not be run.** libsignal v0.106.1 is on disk (`.deps/libsignal-v0.106.1`), but
   its `net` crate links `boring-signal`, whose build script compiles BoringSSL from
   `boring-sys/deps/boringssl`, and that submodule is **empty** in `.deps/libsignal-vendor` (and
   in `.deps/boring-b518db8…`). No BoringSSL source or build exists under the repository, so
   libsignal-net cannot be built offline. To unblock: vendor BoringSSL at commit
   `427ec40cc8edc545253289232e885708c409e5ea` (the submodule of `signalapp/boring` at tag
   `signal-v5.3.0`, which libsignal v0.106.1 pins) into
   `.deps/libsignal-vendor/boring-sys/deps/boringssl`. Then a small crate beside
   `local_signal_server/provision` can call `ChatConnection::start_connect_with` (the function
   the app bridge calls) with a static DNS map and our test CA, against
   `scripts/fingerprint_terminator.py`, and replace the synthetic reference below with a capture.
2. **So the reference is derived from source**, in this order of authority:
   - libsignal v0.106.1 on disk: everything from the TLS configuration up (TLS options, ALPN and
     host per route, WebSocket upgrade, request framing, request ids, keepalive, JSON bodies,
     responses to server requests). This is the code the apps run; the derivation is exact up to
     library behaviour I traced by reading (tungstenite 0.29 `generate_request`, http `HeaderMap`
     order, prost field order, serde_json field order).
   - BoringSSL `427ec40` on GitHub: the ClientHello (`ssl/extensions.cc` `kExtensions` order and
     per-extension conditions, `ssl/handshake_client.cc`, `ssl/ssl_cipher.cc`, `ssl/tls_record.cc`,
     `ssl/tls13_client.cc`).
   - The apps on GitHub, at Signal-Android `b8544a8`, Signal-Desktop `5d1bbb7`, Signal-iOS
     `32b101a`, libsignal `0abcfd4` (read 2026-11-11): what libsignal does not decide (user agent,
     languages, stories flag, which send API, content padding, data-message fields, app-level
     keepalives).
   - The local Signal-Server: what is accepted.
3. `local_signal_server/fingerprint/make_reference.py` turns this into a synthetic transcript
   (dummy UUIDs, zero keys, fixed randoms; no account data) and
   `fingerprint/reference/reference.json` is its normalized form. **Still a guess:** BoringSSL's
   exact cipher order depends on the device having AES instructions (with: AES-128, AES-256,
   ChaCha20; without: ChaCha20 first; older Android phones); what Signal's remote configuration
   currently enables (gRPC sends); record coalescing over HTTP/2 (needs a real run).

**Model client: Signal-Android.** All three apps make both chat connections with libsignal-net and
send 1:1 sealed messages through libsignal's typed API (Desktop only when a remote flag is on), so
the TLS and transport layers are libsignal's in every case. Android is chosen because (a) it is
the largest population, (b) it adds nothing of its own on the wire beyond the user agent (no
`accept-language`, no app-level keepalive requests, no extra request headers), so everything can
be matched from libsignal alone, (c) it can be a primary device (`authorization` username
`uuid.1`), which our account is; Desktop is always a linked device, so a Desktop user agent on a
device-1 socket would itself be a contradiction. Its version: Signal-Android 8.36.0 with
libsignal 0.107.0 (same transport code as 0.106.1).

**The biggest structural finding:** since libsignal **v0.97.1** (commit `7a59231`, 2026-07-10) the
direct chat route is `grpc.chat.signal.org` with **ALPN `h2`**, and the WebSocket runs over
**HTTP/2 extended CONNECT** (RFC 8441); HTTP/1.1 to `chat.signal.org` is only used through
proxies / domain fronting (path prefix `/service`). Every current official app pins a later
libsignal (Android 0.107.0, Desktop 0.106.0, iOS 0.106.1). This client speaks HTTP/1.1 to
`chat.signal.org`, which today only out-of-date clients do. See (c).

## Ranking: how identifying each difference is (most first)

| # | Difference | Status |
|---|---|---|
| 1 | Envelope length: our content padding was `80k` bytes, official `80k − 1`; after PKCS#7 every ciphertext and envelope was 16 bytes longer than any official client's. One message suffices to tell. | **Fixed** (libsignal profile): `buildOfficial`, kernel `signal-seal-official` |
| 2 | ClientHello: 1 cipher, minimal extension set and order, empty session id, record version 0x0303, our own sigalg list (JA4 `t13d0106h1_…` style, unique). | **Partly fixed**: layout, order, session id, record version, sigalgs, psk modes match; ciphers and groups need new capability |
| 3 | `User-Agent: tls-mpc`, header order/case, `Accept-Language: en`, stories header on the anonymous socket. | **Fixed** |
| 4 | Transport: HTTP/1.1 to `chat.signal.org` instead of HTTP/2 to `grpc.chat.signal.org`. | **Needs new capability** (HTTP/2 layer) |
| 5 | Request JSON: field order, `?story=false`, space-padded device/registration ids. | Order and path **fixed**; padding **specified, not built** |
| 6 | Timestamps: base + recipient index, built before the broadcast (they fall ever further behind the server clock, 1 ms apart). | **Fixed**: stamped from the agreed clock when sent |
| 7 | Request ids from 2^63 (libsignal: 0 per connection). | **Not fixed**: shape impact (size-class owner), specified |
| 8 | Keepalive: `GET /v1/keepalive` every 25 s (Android: WebSocket ping after 31 s idle). | **Fixed** (libsignal profile): a ping on the receive socket after 31 s without a record, and in a send session (device refresh; also the ceremony's waits) after 31 s without an exchange (`Session/Common.lean` `keepAlive`, `keepAliveSoft`: payload the ping count per connection from 1, not awaited); one closing `GET /v1/keepalive` of a receive session kept ((f)) |
| 9 | A client-initiated TLS KeyUpdate after the first delivered message (BoringSSL never sends one). | **Fixed** (not sent under the libsignal profile) |
| 10 | Ending a session without a WebSocket Close (libsignal: Close 1000). | **Fixed** (libsignal profile): every connection of a send, serve, receive or ceremony session that ends normally gets a masked Close 1000 with no reason (`PublicReceive.close`, `Session/Common.lean` `closeWebSocket`); no close_notify, as libsignal ((b)) |

Everything "fixed" is behind `SIGNAL_CLIENT_PROFILE=libsignal` (default `legacy` until the
harness passes with it; see "Regression check").

## (a) ClientHello

Reference: BoringSSL for libsignal-net (`rust/net/infra/src/tcp_ssl.rs` `ssl_config`: min version
TLS 1.3, ALPN per route, `set_verify_algorithm_prefs`, `set_curves_list("X25519:P-256:P-384")`; no
GREASE, OCSP, SCT, tickets or extension permutation are enabled).

| Field | Official (libsignal 0.106/0.107 via BoringSSL 427ec40) | Ours, legacy | Ours, libsignal profile |
|---|---|---|---|
| Record version of first record | 0x0301 (`tls_record_version` before version known) | 0x0303 | **0x0301** |
| legacy_version | 0x0303 | 0x0303 | 0x0303 |
| legacy_session_id | 32 random bytes (compatibility mode) | empty | **32 bytes** (`SHA256(r‖2)`, random `SHA256(r‖1)`, r the joint random; neither is a public function of the other) |
| Cipher suites | 1301, 1302, 1303 (ChaCha first without AES hardware) | 1301 | 1301 — *cannot honour 1302/1303* |
| Compression | [0] | [0] | [0] |
| Extensions, in order | server_name, supported_groups, ALPN, signature_algorithms, key_share, psk_key_exchange_modes, supported_versions (+cookie after HRR) | server_name, supported_versions, supported_groups, signature_algorithms, key_share, ALPN | **same as official** |
| supported_groups | x25519, secp256r1, secp384r1 | x25519 | x25519 — *cannot honour P-256/P-384* |
| key_share | x25519 only (first group; no PQ: libsignal's comment "chat-server doesn't support MLKEM in TLS yet") | x25519 | x25519 |
| signature_algorithms | 0807, 0403, 0804, 0401, 0503, 0805, 0501, 0806, 0601 | 0804 0805 0806 0403 0503 0603 0807 0808 0809 080a 080b 0401 0501 0601 | **official list** (a subset of what we verify; an unoffered CertificateVerify scheme is now rejected) |
| psk_key_exchange_modes | [psk_dhe_ke] | absent | **[psk_dhe_ke]** (no PSK offered; the server may now send NewSessionTicket, which the record parser already skips) |
| supported_versions | [0x0304] | [0x0304] | [0x0304] |
| ALPN | `h2` (direct route) / `http/1.1` (proxy routes) | http/1.1 | http/1.1 — *h2 needs the HTTP/2 layer* |
| SNI | grpc.chat.signal.org (20 bytes) | chat.signal.org | chat.signal.org (config) |
| padding ext | none (only after an empty last extension) | none | none |
| GREASE | none | none | none |
| JA3 (md5) | `771,4865-4866-4867,0-10-16-13-51-45-43,29-23-24,` (`e29d030d…`) | `771,4865,0-43-10-13-51-16,29,` | `771,4865,0-10-16-13-51-45-43,29,` (measured) |
| JA4 | `t13d0307h2_55b375c5d22e_3df4dd8a7a2a` (direct), `t13d0307h1_55b375c5d22e_3df4dd8a7a2a` (proxy) | `t13d0106h1_…` | `t13d0107h1_0f2cb44170f4_3df4dd8a7a2a` (measured: the extension/sigalg part c now equals the official one; a and b differ by the cipher suites) |

**Trade-offs for what we cannot perform** (owner's rule: never advertise what the server could
select and we cannot do):
- *TLS_AES_256_GCM_SHA384*: omit and differ (cipher count and JA4 part b), or advertise and abort if
  chosen. Building it: AES-256 already exists in Lean (Signal's message keys use AES-256-CBC;
  `Aes.expandKey … 8 14`), GHASH is unchanged; the new part is the SHA-384 key schedule (HKDF over
  SHA-384; SHA-512 compression already exists in `Signal/XEdDsaSha512.lean`). Cost: AES-256 is
  14 rounds vs 10 (≈ +40 % AND gates per record block), SHA-384 HKDF roughly doubles the handshake
  key-schedule hashing (order of +1.5–2.5M AND per handshake on today's ≈3M). New kernels:
  `tls-derive` / `tls-finish` / record seal and open for the 256-bit suite. Medium.
- *TLS_CHACHA20_POLY1305_SHA256*: ChaCha20 is ARX (≈10k AND per 64-byte block, cheaper than AES
  per byte), but Poly1305 is arithmetic mod 2^130−5: either a Boolean multiplier (≈17k AND per
  16-byte block, too slow for large records) or a second field engine for that prime with the
  same "shared key powers" trick as GHASH, plus a mod 2^128 truncation in the Boolean engine.
  Large.
- *P-256 / P-384 groups*: needed only if a server answers with a HelloRetryRequest for them;
  every official client sends an X25519 share, so a server preferring P-256 would make every
  client pay an extra round trip (implausible). Advertising them is a small risk of a failed
  handshake (fail-closed, no weakening), and HelloRetryRequest for an unsupported group already
  aborts. Building ECDH on P-256 needs a field engine over the P-256 prime (≈ 256 doublings and
  additions, ~10 field products each) and a Boolean conversion of the x-coordinate. Large.
- Matching JA3/JA4 exactly needs all three cipher suites and all three groups.

## (b) Rest of the handshake and the TLS layer

| | Official (BoringSSL) | Ours |
|---|---|---|
| ChangeCipherSpec from the client | none in a normal TLS 1.3 handshake (`tls13_client.cc`: only after HelloRetryRequest; `handshake_client.cc`: only with early data) | none |
| Client Finished | one record, 53 bytes of ciphertext | the same |
| Client Finished timing | milliseconds after the server flight | seconds (the key schedule and Finished run in two-party computation: `tls-derive`, `tls-verify-finished`, `tls-finish`); **identifying to the server and to any observer, not fixable without making the handshake circuits faster** |
| KeyUpdate from the client | never | **was** sent after the first delivered message; not under the libsignal profile |
| Record padding | never | never (would change under the (d) replacement, see there) |
| Closing | WebSocket Close 1000, empty reason (`rust/net/infra/src/ws/connection.rs` 328-346, `Event::ClientDisconnect`), and nothing after it: libsignal does not wait for the server's Close, and on the HTTP/1.1 WebSocket path sends **no** close_notify (tokio-tungstenite's `send` only flushes; tokio-boring sends close_notify only from `poll_shutdown`, which nothing on that path calls, and boring's `SslStream` `Drop` frees the `SSL` without it). Correction: this row said "then close_notify". (On the h2 route the h2 connection's own close does call `shutdown`, `h2-0.4.16/src/proto/connection.rs:306`; not our transport.) | legacy: the session ends without a Close frame. **libsignal profile: the same Close** (sealed as a public buffer, size class 32), then up to 150 counted polls (about 3 s) for the end of the connection, the server's records not opened; then the abort as before (no close_notify). Not on a failed session (an abort stays an abort) |

## (c) WebSocket upgrade

libsignal over HTTP/1.1 (`connect_http1`, tungstenite 0.29 `generate_request`): `Host`,
`Connection`, `Upgrade`, `Sec-WebSocket-Version`, `Sec-WebSocket-Key` in that case, then libsignal's
headers in insertion order with lowercase names (http's `HeaderMap`; tungstenite's removals keep
the remaining order). Signal-Android passes no languages, so no `accept-language`; the stories flag
only on the authenticated socket (Android: `Stories.isFeatureEnabled()`, usually `true`).

Authenticated (libsignal profile = official):
```
GET /v1/websocket/ HTTP/1.1
Host: chat.signal.org
Connection: Upgrade
Upgrade: websocket
Sec-WebSocket-Version: 13
Sec-WebSocket-Key: <16 random bytes, base64>
authorization: Basic base64("{aci}.1:{password}")
x-signal-receive-stories: false
user-agent: Signal-Android/8.36.0 Android/35 libsignal/0.107.0
```
Unauthenticated: the same without `authorization` and `x-signal-receive-stories`.

Ours before: `Upgrade` before `Connection`, `Authorization` capitalised with username `{aci}` (no
device), `X-Signal-Receive-Stories` and `Accept-Language: en` on both sockets, `User-Agent:
tls-mpc`. Changed: `RelayUpgrade.request` (the `signal-upgrade` kernels; no profile switch for the
authenticated one, the server accepts `uuid.1`) and `RelayUpgrade.anonymousRequest` (the legacy
form stays as `legacyAnonymousRequest`).

Remaining:
- **`x-signal-receive-stories: false`**: most Android users have stories enabled (`true`). Sending
  `true` makes the server deliver stories to the account, which the receive path then refuses and
  acknowledges. Owner's decision; cheap either way.
- **User agent is a deployment constant** (`RelayUpgrade.userAgent`): it must follow Android
  releases (versions age out in weeks), and `Android/35` is one plausible SDK level.
- **HTTP/2** (official direct route). What it needs: client preface + SETTINGS (hyper/h2 client
  defaults: ENABLE_PUSH 0, initial window, max header list) + WINDOW_UPDATE; the WebSocket CONNECT as
  a HEADERS frame (`:method CONNECT`, `:protocol websocket`, `:scheme https`, `:authority`, `:path
  /v1/websocket/`, `sec-websocket-version: 13`, then libsignal's headers; h2 HPACK-encodes literals
  with Huffman coding); every WebSocket frame inside DATA frames (9-byte public header each); SETTINGS
  ACK, PING ACK and WINDOW_UPDATE answers. All public except the authenticated socket's
  `authorization` value: its Huffman-coded length depends on the password's characters. Since we
  choose the password at registration, it can be chosen (rejection sampling) so its Huffman length
  is a fixed public number; then a small kernel (table lookup per base64 character, bit packing at
  public offsets) produces it. Request kernels take the 9-byte DATA header as more public bytes of
  their template (offsets shift; no new kernels). Receiving: the record-opening path must strip
  DATA frame headers inside records whose content is private; the 9-byte headers can be revealed
  (lengths/flags/stream id: the server's framing, no more than record lengths show), so it is a
  variant of the record parser. If Signal's remote config switches sends to gRPC
  (`grpc.MessagesAnonymousSendSingleRecipientMessage`, default *use gRPC* when absent), sends become
  gRPC messages on the same HTTP/2 connection (protobuf instead of JSON). Estimate: controller-side
  framing, HPACK and flow control ≈ 1–2k lines of Lean; one HPACK credentials kernel; one
  record-parser variant; new size classes for request records (+9 bytes per frame).

## (d) Requests

libsignal (`rust/net/chat/src/ws/messages.rs`, `keys.rs`; prost field order verb 1, path 2, body 3,
id 4, headers 5; headers `"{name}: {value}"`, lowercase):

| | Official | Ours, legacy | Ours, libsignal profile |
|---|---|---|---|
| WebSocketMessage field order | type, request | same | same |
| Request field order | verb, path, body, id, headers | same | same |
| Send path | `PUT /v1/messages/{uuid}` | `…?story=false` | **no query** |
| Send headers | `content-type: application/json`, `unidentified-access-key: <base64 16>` | same | same |
| Send JSON | `{"messages":[{"type":6,"destinationDeviceId":1,"destinationRegistrationId":N,"content":"…"}],"online":false,"urgent":true,"timestamp":T}` | content first, `timestamp` before `urgent` | **official order**; ids still space-padded slots |
| Prekey fetch | `GET /v2/keys/{uuid}/*` (or `/{deviceId}`) with `unidentified-access-key` (Android builds this itself: `KeysApiV2.kt`) | same | same |
| Request id | 0, 1, 2, … per connection | 2^63 + n (send), 2^63 + 2^32 + n (refresh) | unchanged |
| Masking | random 4-byte mask per frame | joint random mask | same |
| Response to a server request | `{type 2, response {id, status 200, message "OK"}}` | same bytes | same |

**Request ids** (not fixed): a counter from 0 changes the varint width (1 byte below 128, 2 below
16384), and the request kernels (`signal-request-ctr`, `bundle-request-ctr`, `bundle-fetch-ctr`)
are named by frame size and slot offsets, so each id width is another shape. Change: a
per-connection counter in the controller (Lean, small) and `request-shape … ID_WIDTH` so circuit
production makes widths 1 and 2 (about twice the request shapes). For the size-class owner.

**The space-padded device and registration ids** (`paddedDecimal` in `signalRequestCtr`; JSON
whitespace, valid, but no client emits it). Options, and what each reveals to the NODES (the
server knows both values anyway: they are in the request):
1. *Reveal the digit counts* and build the canonical layout with exact-width slots. The device id
   is always one digit (the server assigns the lowest free id, at most 6 devices), so 0 bits; the
   registration id is uniform in 1..16380 (`generateRegistrationId`), so its digit count has
   entropy H = 1.28 bits (5 digits 39.0 %, 4 digits 54.9 %, 3 5.5 %, 2 0.55 %, 1 0.05 %), stable
   per contact device. Any node operator with a Signal account can fetch a suspected person's
   registration ids (prekey bundles) and test them against it: about a 2.4× narrowing per device.
   Rejected: it reveals something new about a contact's identity.
2. **Chosen: canonical JSON at a private length inside a fixed-size TLS record.** A new kernel
   (`signal-request-canonical`) takes the public template split at the two numbers (prefix,
   middle, suffix — the suffix holds the base64 envelope, which comes AFTER the ids in libsignal's
   order), formats both numbers as variable-length digits (`PrivateDecimal.encode` already gives
   digits and length), shifts the middle and suffix left by the private number of unused digit
   positions (0..6: three mux layers, ≈ 24 AND per byte of suffix), recomputes the private length
   fields that precede them (WebSocket 16-bit length, the request and body length varints: small
   adders; their byte widths are public because both bounds fall in one width), applies the
   public WebSocket mask only below the private payload length (thermometer mask, ≈ 8 AND per
   byte), appends the TLS inner content type 0x17 right after the payload and zeros after it, and
   CTR-encrypts the fixed capacity (as `tls-seal-private-ctr` / `TlsPrivateSeal` already do). The
   record length is then public and the same for every registration id: **the nodes learn
   nothing new.** Cost ≈ 32 AND per byte of request (≈ 50k AND for a 1.5 KB request, under 2 % of a
   send). Residual: the server's TLS terminator sees 1–7 bytes of TLS record padding, which
   BoringSSL never writes (visible only to whoever terminates TLS for Signal, not in the request
   itself). Not built here: it needs the new kernel, its worker operation and controller wiring
   in files four other engineers are changing; this is its specification.

## (e) Message content

| | Official (all three apps) | Ours, legacy | Ours, libsignal profile |
|---|---|---|---|
| Padding | Content ‖ 0x80 ‖ zeros to `80k − 1` bytes (`PushTransportDetails`, `padMessage`, `Data+MessagePadding`), PKCS#7 then adds 1 byte → ciphertext `80k` | `80k` → ciphertext `80k + 16` | **`80k − 1`** |
| DataMessage (Android, plain text) | body 1, expireTimer 5 (= 0), profileKey 6 (if profile sharing), timestamp 7, isViewOnce 14 (= false), expireTimerVersion 23 | body, timestamp | unchanged |
| Timestamp | the message's send time, per message | broadcast base + recipient index, built ahead | **agreed clock when first sent**, strictly increasing, kept on a resend |

**Receiving** (2026-11-12): Signal-Android encodes with Wire, which writes fields in DECLARATION
order, so its first text is `0A len body ‖ 28 00 (expireTimer) ‖ B8 01 01 (expireTimerVersion) ‖
32 20 profileKey ‖ 38 timestamp ‖ 70 00`, padded to `80k − 1`, sealed with content hint
RESENDABLE (`20 01`). For a 108-character signup token that is 161 bytes of content, 239 padded,
**240 bytes of session ciphertext**. The receive kernels accept it: `ReceiveFirst.gaps` lets
`flags`, `expireTimer` (any value) and `expireTimerVersion` stand between the body and the
profile key, chosen inside the circuit (tested with `lss-provision`'s `LSS_DATA_LAYOUT=android`,
`android-tag`, `android-timer` and `legacy`).

The server sees only lengths, so the data-message fields matter only through the size class: with
Android's extra fields (+7 bytes, +34 with a profile key) the class boundaries move, but no length
we produce is impossible for an official client once the padding is `80k − 1`. The fields were not
added: `expireTimer = 0` with an `expireTimerVersion` can reset a disappearing-message timer the
recipient set, and we hold no profile key. Owner's decision.

Typical sizes (libsignal profile): each class holds one byte less than before, so the text-length
boundaries move down by one (legacy 1..68, 69..146, 147..226, 227..256): 1..67 bytes of text is
class 1 (79 padded bytes, 80 bytes of session ciphertext), 68..145 class 2, 146..225 class 3,
226..256 class 4; the sealed-sender envelope adds the same fixed overhead as before (certificate,
ephemeral key, MACs, the SPQR header) on top of `80k` instead of `80k + 16`.

**What the size-class engineer needs to know:** the libsignal profile's built text is `80c + 9`
bytes (`officialBuiltBytes`), padded content `80c − 1` (`officialPaddedBytes`); its kernel is
`signal-seal-official CERT CLASSES COUNTER PREVIOUS EPOCH INDEX` (`signalSealFixed … official :=
true`); multi-device sends use `bundle-seal CERT ONETIME 80c−1 …` (now accepted by `find`). The
worker chooses the name from the text size (`service_kernels.h` `seal_open`, `seal_devices`;
`tls_worker_v3.cpp` operations 41 and 61 accept both sizes). `CircuitInventory.lean` does not yet
list the official names, so `--strict` runs with the libsignal profile will refuse them; request
frames are smaller (no `?story=false`, reordered JSON), and `request-shape` follows
`SIGNAL_CLIENT_PROFILE`, so circuit production must run with the same setting as the sessions.

## (f) Behaviour over time

| | Official (Android) | Ours, libsignal profile |
|---|---|---|
| Keepalive | WebSocket ping, payload one byte (ping counter from 1), when 31 s pass without sending or without hearing from the server; no `/v1/keepalive` requests (Desktop and iOS do send `GET /v1/keepalive` every 30 s) | ping after 31 s without a record on the receive socket; in a send session (between the steps of a device refresh) a ping after 31 s without an exchange, not awaited, no request (2026-11-12; before: a `GET /v1/keepalive` after 20 s, still so under the legacy profile); one `GET /v1/keepalive` before leaving a receive session (its answer proves our acknowledgements were read; kept, allow-listed); then a Close 1000 |
| Server requests | `200 OK` acknowledgement of each delivered message; `queue/empty` answered | the same; delivered messages acknowledged only after the contact's state is stored (timing differs) |
| Connection lifetime | auth socket held while the app is foregrounded or a push arrives; unauth socket held while in use, closed 30 s after its last use in the background | one session per broadcast or receive window; N send connections opened together (Tor), each handshaking within seconds |
| What official clients do that we never do | profile fetches, `GET /v1/certificate/delivery` refreshes, prekey replenishment, receipts, typing indicators, sync messages to linked devices, storage service, attachments, group operations, reconnecting after network changes | none of these. Cheap and compatible with the owner's decisions: periodic `/v1/certificate/delivery` (needed anyway, PRODUCT_TODO section 2) and prekey checks on the authenticated socket. Never: receipts (owner), profile fetches of contacts (they would name the contact). |
| Timing | messages sent as the user types | a burst per broadcast, one response at a time (PRODUCT_TODO section 8: spreading in time) |

## Regression check

`local_signal_server/check_signal_service_local.py --fingerprint` (implies `--profile libsignal`)
runs one send and one receive session through `scripts/fingerprint_terminator.py` (port 18445; it
records the raw ClientHello and records and the decrypted upgrade and frames), then
`fingerprint/check_fingerprint.py` normalizes the capture (`fingerprint/analyze.py`: secrets and
identities become shapes) and compares it with `fingerprint/reference/reference.json`. Any
difference not in its `ALLOWED` table (each with its reason) fails the stage. Transcripts stay in
`local_signal_server/state/fingerprint/` (not in the repository; they hold local test
credentials); the stored reference has no account data.

**State (2026-11-11, `--runs 0 --fingerprint`, semi-honest and malicious): passes.** Residual
timing seen in the malicious run: a message's timestamp is 1.3–2 s older than the server's receipt
(the engines seal it after it is stamped); an official client's is tens of milliseconds old. 91 items compared over the
send connection (4 sealed sends, both recipients decrypted both texts: libsignal accepts the
`80k − 1` padding and the send-time timestamps) and the receive connection (one ping 32 s after
the last frame, a message delivered and acknowledged). Remaining differences, all allow-listed:
cipher suites, groups (and the lengths and JA3/JA4 they determine), the local hostname, the
space-padded ids, request ids from 2^63, the closing `/v1/keepalive`, no WebSocket Close, ALPN
`h2` of current libsignal, and the local test account's password length (22 characters; Android
generates 24 — the product account's password must be base64 of 18 random bytes, PRODUCT_TODO
section 2). Measured: the client Finished leaves 0.57–0.89 s after the ClientHello (semi-honest,
local), against milliseconds for BoringSSL.

**State (2026-11-12, after the Close and the send-session ping; `--runs 0 --fingerprint`,
semi-honest and malicious): passes**, 91 items compared over two connections. Both connections now
end with a masked Close whose payload is `03e8` (`close.websocket` compared, no longer allowed) and
no close_notify (`tls.client_records` now also compares `close_notify`, false on both sides); the
reference's authenticated connection (2) gained the same Close (`make_reference.py`). Remaining
allowed differences: `tls.cipher_suites`, `tls.extension_detail.supported_groups`,
`tls.extension_detail.server_name` (local hostname), `tls.record_length`, `tls.handshake_length`,
`tls.ja3`, `tls.ja3_md5`, `tls.ja4` (all following from the suites, groups and hostname),
`tls.alpn_of_current_libsignal`, `request.id`, `request.body.canonical`,
`request.body.space_padded_numbers`, `request.extra./v1/keepalive` (the receive session's closing
keepalive), `upgrade.password_length`. The stage's send session has no device refresh, so the
send-session ping is not exercised here (nor, so far, elsewhere: no harness refresh has yet stayed
31 s without an exchange).

Before making `libsignal` the default: run it in malicious mode and with `--db`,
`--multi-device`, `--signup`, `--recovery`; add the official kernel names to
`CircuitInventory.lean` (or `--strict` runs refuse `signal-seal-official`); produce circuits with
`SIGNAL_CLIENT_PROFILE=libsignal` (request frame sizes differ). Found 2026-11-12:
`malicious --runs 0 --recovery devices --profile libsignal` fails at the resend after the device
refresh: worker operation 61 (`seal_devices`) rejects "conversation shape"
(`service_kernels.h:960`) after running `bundle-seal` with the official `80c − 1` padding (its
`conversation` output is not `CERT + CONTACT` bytes). A kernel/worker matter for the multi-device
send under this profile, not the controller's; the legacy profile's `bundle-seal … 80c` passes.
