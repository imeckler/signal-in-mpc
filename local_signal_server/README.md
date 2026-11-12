# local_signal_server: testing the MPC Signal client against a LOCAL Signal-Server

Purpose: validate every request the MPC client (TLS 1.3 + Signal inside 2PC) sends against the
**real Signal-Server implementation running on this machine**, before anything is ever tried
against Signal's service. Malformed requests to production get accounts/IPs banned.

**Absolute rule: nothing here talks to Signal-operated hosts** (`*.signal.org`,
`*.whispersystems.org`, `build-artifacts.signal.org`, ...) and no real phone number is used.
Server, terminator and provisioning tool bind and connect to `127.0.0.1` only; the provisioning
tool refuses non-loopback servers.

## Layout

| Path | What |
|---|---|
| `scripts/fetch_jdk.sh` | user-local Temurin JDK 25 (macOS aarch64, from github.com/adoptium, sha256-checked) into `third_party/jdk/` |
| `scripts/build_server.sh` | clones `github.com/signalapp/Signal-Server` into `third_party/`, checks out the owner's commit `b9a24fede` (same HEAD as `/Users/izzy/repos/Signal-Server`), applies `patches/`, compiles `service` + test classes with Maven (via `config/maven-settings.xml`), writes `state/classpath.txt` |
| `config/maven-settings.xml` | mirrors Signal-Server's `signal-build-artifacts` repository (build-artifacts.signal.org) to Maven Central, so Maven never contacts a Signal host |
| `patches/0001-libsignal-0.86.5-from-maven-central.patch` | the only source change: `libsignal-server` 0.86.6 to 0.86.5 (0.86.6 exists only on build-artifacts.signal.org; 0.86.5 is the newest on Maven Central and API-compatible here) |
| `scripts/make_config.py` | writes `state/server/local.yml` = upstream `service/src/test/resources/config/test.yml` with only network/S3 endpoints changed (see Deviations) |
| `scripts/gen_tls_cert.sh` | local CA + leaf (`server.example`, `localhost`, `127.0.0.1`; Ed25519 by default, `LEAF_KEY=p256` optional) in `state/tls/` |
| `scripts/tls_terminator.py` | TLS 1.3 terminator 127.0.0.1:18443 -> 127.0.0.1:18080; same TLS profile as the existing fixture server (TLS 1.3 only, AES-128-GCM-SHA256, X25519, ALPN http/1.1, no tickets); forwards bytes unchanged; `TRANSCRIPTS=1` records plaintext transcripts |
| `scripts/start_server.sh` / `scripts/stop_server.sh` | start/stop server JVM + terminator (background, pid files in `state/`) |
| `scripts/probe_upgrade.py` | sends the MPC client's **exact** WebSocket upgrade bytes (from `TlsMpc/Signal/RelayUpgrade.lean`) through the terminator; `--listen N` decodes the server's frames; `--unauthenticated` drops the Authorization line; `--session N --action ping\|keepalive --every S --reply-queue-empty` keeps a socket and answers `queue/empty` with the working-tree controller's reply bytes; `--save DIR` (unauthenticated only) stores the request and 101 head |
| `provision/` | `lss-provision`, a conventional Rust Signal client (libsignal-protocol v0.106.1 from `../.deps`, offline vendored crates, same versions as `signal_backend/Oracle`). `src/mpc.rs`: `export-mpc`, `ref-send`, `probe-sockets` |
| `scripts/provision.sh` | builds and runs `lss-provision` (default: full provisioning) |
| `replay/Replay.lean` | runs recorded server bytes through the client's own Lean parsers (`TlsWebSocketUpgrade/Frame/Idle/Control`, `TlsChatResponse`, and verbatim copies of `PublicReceive` at HEAD e27de08 and in the working tree); executed with `lean --run` against the repo's existing `.olean`s, nothing is built and the lakefile is untouched |
| `testdata/` | server-originated byte samples from the local server (101 heads, frames, keepalive and send responses) and unauthenticated request samples. No passwords, Authorization headers or keys (checked) |
| `check_signal_service_local.py` | the local-server harness: start, provision, export, optional `--self-check`, MPC run (`NotImplementedError`, documented), verification, stop |
| `scripts/start_compact_server.sh` / `scripts/stop_compact_server.sh` | a SECOND server instance (ports 19080/19081, terminator 19443, pid files in `state/compact/`) issuing production's compact sender certificates (`make_config.py … compact`: `embedSigner: false`), behind `scripts/coalesced_terminator.py`: production's handshake shape (the encrypted flight in one padded record, one Ed25519 certificate). The default instance is not touched |
| `scripts/coalesced_terminator.py` | a small TLS 1.3 server (one profile: AES-128-GCM, X25519, Ed25519, http/1.1) that sends the whole encrypted flight in ONE record, as chat.signal.org does (OpenSSL cannot) |
| `check_signal_service_local_signup.py` | the first real test's flow (`real_signal/run_real_test.py`'s pieces): signups in the layouts official clients send (`lss-provision` `LSS_DATA_LAYOUT=legacy\|android\|android-tag\|android-timer`), a refused one before them, one reply; `--compact` against the second instance, `--manifest` strict (`deployment-compact.json`) |
| `scripts/make_fake_account.py` | a local account rewritten in the real registration tool's account format (for `export-account … local`) |
| `state/`, `logs/`, `third_party/` | generated; git-ignored. `state/accounts/*.json` and `state/mpc-export.json` hold LOCAL TEST keys and passwords |

## Tooling (this machine, 2026-11-10)

Present: Docker 29.4 via OrbStack (socket `~/.orbstack/run/docker.sock`), Docker Compose v5.1,
cargo 1.88 + `nightly-2025-09-24` (needed for libsignal v0.106.1), Python 3.15, Homebrew OpenSSL 3.
Missing system-wide: Java, Maven, Redis. Neither is installed system-wide: the JDK is a user-local
download in `third_party/jdk`, Maven comes from `./mvnw` (Maven Central), and Redis/DynamoDB run as
containers.

## Stages

```sh
# 0. one-time: JDK + build (about 1 minute after the first dependency download)
bash scripts/fetch_jdk.sh
bash scripts/build_server.sh

# 1. start (first start pulls images; later starts take ~15 s). TRANSCRIPTS=1 to record plaintext.
bash scripts/start_server.sh
curl -s http://127.0.0.1:18081/ping                       # -> pong
python3 -I scripts/probe_upgrade.py                        # bogus credentials -> 403
# 2. provision sender + recipient + recipient2 (server state is in-memory: rerun after EVERY server start)
bash scripts/provision.sh                                  # -> {"provisioned":true,...}
bash scripts/provision.sh export-mpc                       # -> state/mpc-export.json (see "Export for the MPC client")
bash scripts/provision.sh ref-send "hello"                 # reference sender from the export only (unauth socket)
python3 -I check_signal_service_local.py --self-check      # whole pipeline except the MPC run (exits 1: MPC run not implemented)
python3 -I scripts/probe_upgrade.py --account state/accounts/sender.json --listen 3   # -> 101 + queue/empty
# conventional send/receive (for checking what the MPC client delivers)
bash scripts/provision.sh send sender recipient "hello"          # unauthenticated socket + UAK
bash scripts/provision.sh mpc-send sender recipient "hello"      # MPC client's exact bytes, authenticated socket
bash scripts/provision.sh receive recipient 10                   # prints envelope source fields too
# 3. stop (also removes the Testcontainers containers)
bash scripts/stop_server.sh
```

Ports (all 127.0.0.1): 18080 application (plain HTTP/1.1 + h2c), 18081 Dropwizard admin,
18051 gRPC, 18443 TLS terminator. DynamoDB Local and Redis (+ socat, Ryuk reaper) run as
Testcontainers containers on random ports and are removed when the JVM exits.

## How the server runs

`org.whispersystems.textsecuregcm.LocalWhisperServerService` (upstream's own test-server entry
point, `service/src/test/java`) with `SIGNAL_SERVER_CONFIG=state/server/local.yml`. It loads
upstream `test-secrets-bundle.yml` and uses upstream "local" factories: DynamoDB Local and a Redis
cluster via Testcontainers, a stub registration service (any verification code is accepted; the
session asks for a captcha, answered with `noop.noop.registration.noop`). All controllers, request
validation, authentication, rate limiters, message delivery and WebSocket code are the real ones.

### Deviations from production (know these when reading results)

1. **TLS is terminated by `tls_terminator.py`**, not by Signal's edge. The server sees
   plaintext HTTP/1.1 from 127.0.0.1 exactly as the client sent it. Production edge behaviour
   (its TLS stack, certificate chain, any header rewriting, connection limits) is not reproduced.
2. **Sealed-sender trust root** is upstream's documented test root
   `BS/lfaNHzWJDFSjarF+7KQcw//aEr8TPwu2QmV9Yyzt0` (test-secrets-bundle.yml lines 149-151), not
   production's. The client must be configured with it for local runs.
3. **S3 is disabled** (endpoints point at the closed port `127.0.0.1:1`). Upstream test.yml would
   otherwise send one-time PQ prekey pages and CDN objects to real AWS. So one-time PQ prekeys
   (`pqPreKeys`) cannot be uploaded locally (the server answers 500); bundles carry the signed
   last-resort PQ key. Attachments do not work either.
4. **libsignal-server 0.86.5 instead of 0.86.6** on the server (patch above).
5. **State is ephemeral**: accounts, keys and queued messages disappear when the server stops.
6. Server version is the owner's pinned commit (2026-05-19), older than production today. Bump by
   `SIGNAL_SERVER_COMMIT=<sha> bash scripts/build_server.sh`, but newer commits need libsignal
   versions that exist only on build-artifacts.signal.org (current upstream wants 0.106.1), JDK 27,
   and a FoundationDB message store (`foundationDbMessages` in upstream test.yml at 2026-11-01);
   that needs an owner decision.
7. One harmless outbound DNS lookup remains: the ASN-table S3 monitor resolves the placeholder
   `a-bucket.s3.a-region.amazonaws.com` (does not exist; fails). No Signal host is involved.

## Provisioned state (`state/accounts/<name>.json`, LOCAL TEST KEYS)

`aci`, `pni`, `number` (fictional +1 202 555 01xx), `device_id` (1), `password` (22 ASCII
chars, matching the MPC client's 22-byte password slot), `registration_id`, `profile_key`,
`access_key` (16 bytes = zkgroup `derive_access_key`), ACI/PNI identity key pairs, signed prekey,
last-resort Kyber key, remaining one-time EC prekeys, `sender_certificate` (from
`GET /v1/certificate/delivery?includeE164=false`; currently 244 bytes), `trust_root`, and per peer
the libsignal `SessionRecord` + identity key. After `provision`, sender->recipient is an
**established** session (the recipient has replied), so the next sends are `SignalMessage`s in
sealed sender, which is the only kind of send the MPC client implements.

## Export for the MPC client (`lss-provision export-mpc` -> `state/mpc-export.json`)

Layout source (read-only): `TlsMpc/HybridKernels.lean` (`conversationBytes`, `signalConversationView`,
`signalSealFixed`, `signalRequestSeal`), `service_kernels.h` (`CERT=260`, `PASSWORD=22`,
`admit_fixture`, `fixture_id`), and the fixture generator
`signal_backend/TextNotificationWork/check_recipient.py` (-> `text-fixtures.json` ->
`prepare_fixtures.py` -> `PublicTextFixture.h`). All values hex unless noted.

| Field | Content |
|---|---|
| `server` | `endpoint` 127.0.0.1, `port` 18443, `hostname` server.example, `tls_trust_root_pem` (absolute path of `state/tls/ca.pem`), `plain_port` 18080 |
| `sealed_sender_trust_root_hex` | 33-byte upstream test trust root (recipients validate sender certificates against it) |
| `sender.aci`, `aci_hex` | sender ACI (text, 16 bytes) |
| `sender.password`, `password_hex` | 22-byte password; `upgrade_credentials_hex` = aci(16) ‖ password(22), the `credentials` input of `signal-upgrade` |
| `sender.identity_private_hex` / `identity_public_hex` | 32-byte X25519 identity private key (the `initial` blob's first 32 bytes) / its public key without 0x05 |
| `sender.certificate_hex` (244 B), `certificate_slot_hex` (260 B) | the server's sender certificate, and the same padded to the kernel's 260-byte slot |
| `contacts[i]` | `slot`, `name`, `contact_id_u128_hex` (00..01, 00..02 = `fixture_id(slot)`), `recipient_aci(_hex)`, `device_id`, `registration_id`, `access_key_hex/base64`, `request_id`, `session_block_hex` (262), `metadata_hex` (57), `conversation_record_hex` (579 = 260+262+57), `initial_hex` (611 = identity secret ‖ record, the exact `PublicTextFixture::initial(slot)` layout), `projection` (diagnostics, below) |

Session block (262 bytes; offsets as in `SpqrSend.Input` built by `signalSealFixed`), projected
from the sender's libsignal `SessionRecord` (`current_session`):
`0` session_version · `1..5` sender chain index (BE) · `5..9` previous_counter · `9..41` sender
ratchet public key (no 0x05) · `41..73` sender chain key · `73..105` SPQR send-link `next` ·
`105..109` SPQR send-link `ctr` · `109..117` SPQR message epoch E (BE; key from the chain link for
E-1, as `spqr::send` does `chain.send_key(epoch-1)`) · `117` 0 (kernel overwrites with the text kind)
· `118..150` local identity public · `150..182` remote identity public · `182..262` zero (plaintext,
overwritten). Metadata (57): `0..16` recipient ACI · `16..32` access key · `32..40` 0 (timestamp,
overwritten) · `40..48` request id 2^63+slot · `48` device id · `49..53` registration id (BE) ·
`53..57` 0 (mask, overwritten).
The forward projection did not exist in the repo; it is written as the exact inverse of
`signal-text-recipient-oracle.rs` (block -> receiver session) and consistent with Oracle's
`session_send_projection.rs` (send result -> record), which is reused unchanged for write-back.

**Certificate slot.** The kernels take `certificate := record[0..cert]` with `cert` a compile-time
constant (260) and embed it raw into the USMC: `08 02 ‖ 12 len(cert) cert ‖ 1a len(inner) inner`
(`TlsMpc/Signal/SealedSenderV1.lean usmc`). There is **no length prefix and no padding**: the slot
length IS the certificate's serialized length. `boundSeal` never parses the certificate (it
only checks the computed sender key against session bytes 118..150). Options:
(a) recompile the kernels with `cert = 244` (exact; production's length differs and may vary);
(b) **pad inside the protobuf**: append an unknown field 15 (`7a 0e` + 14 zero bytes) to the outer
`SenderCertificate`. The signature covers only the inner `certificate` field and parsers skip
unknown fields. **Verified locally:** libsignal 0.106.1 parses and validates the padded 260-byte
certificate, and both recipients decrypted messages sealed with it. The export uses (b).

**SPQR.** The kernel emits only chunk-less SPQR messages (`SpqrMessage.Shape … hasChunk=false`,
kind 0 = None or 4 = Ct1Ack). The real sender state after provisioning is phase
**`KeysSampled`** (the initiator is sending its KEM header). libsignal's own next send would carry
a 32-byte `Hdr` chunk (type 1) at the same epoch 1 and index, so the projection is **not exact**
(`projection.projection_exact=false`). Projecting the newest chain link with payload None is
nevertheless **accepted by real libsignal recipients** (verified, below). The consequence: as long as
the MPC client sends, SPQR never advances its epoch (no PQ ratchet progress); message keys still
mix in the SPQR chain key. That is a protocol-level question for the owner.

## Reference sender self-check (`lss-provision ref-send TEXT`): verified

Reads ONLY `state/mpc-export.json`. It rebuilds a send-only libsignal session from the 262-byte
block (inverse projection; root key and ratchet private key are dummies a send never reads; SPQR
state `NoHeaderReceived` at epoch E with the exported send link, whose send emits a payload-free
message exactly like the kernel). It seals with the 260-byte slot certificate, builds the request
with the client's exact `PublicRequest.build` bytes, and sends it on an **unauthenticated** socket.
It then writes the advanced block back into the export, and the real sender record via Oracle's
`session_send_projection::apply`.
Observed: 3 rounds × 2 contacts → `200 {"needsSync":false}`. SPQR messages `01 01 03 00`, `01 01 04 00`, …
(v1, epoch 1, index, None). Both recipients decrypted every text and every envelope had
`source_service_id=None, source_device=None`. A conventional libsignal send afterwards (with a Hdr
chunk) was also decrypted, so the write-back keeps the real record consistent.

## Replay of recorded server bytes through the client's parsers: executed

`lake -d <repo> env lean --run replay/Replay.lean (head|wip) FILE [EXPECT_ID]`. This runs the
repo's existing `.olean`s for `TlsWebSocketUpgrade/Frame/Idle/Control` and `TlsChatResponse`, plus
verbatim copies of `PublicReceive.step` at HEAD e27de08 (`head`) and in the working tree (`wip`).

| Sample (`testdata/`) | HEAD e27de08 | working tree |
|---|---|---|
| `send-unauthenticated-server-stream.bin`: real 101 (224 B, with Date/Vary/X-Signal-Timestamp) + 200 response frame (`82 7e 00 7f`, headers `Name:value`, body `{"needsSync":false}`), expecting id 2^63+4 | **accepted**, response correlated and successful | **accepted** |
| same with a wrong expected id (negative control) | rejected at byte 354 (last byte): "service response rejected or not correlated" | n/a |
| `unauthenticated-server-stream.bin`: 101 + keepalive 200 (no body) + idle close frame, expecting the keepalive id | **accepted** | **accepted** |
| `authenticated-server-stream.bin`: 101 + `PUT /api/v1/queue/empty` + keepalive response + close | **rejected at stream byte 224 = 0x82** (first byte of the queue/empty frame): "WebSocket frame rejected". With no request pending, HEAD parses with `TlsWebSocketIdle`, which refuses data frames | **accepted**: request scanned (`PUT /api/v1/queue/empty`), reply frame built |

The working tree's reply bytes for `queue/empty` (`08 02 1a … 08 <id> 10 c8 01 1a 02 4f 4b`,
masked) were sent to the real server by `probe_upgrade.py --reply-queue-empty`. The server kept the
socket open and answered later keepalives, so there was no 1007 close.

## Unauthenticated send socket: verified

* Upgrade: the client's request **without** the `Authorization` line (`GET /v1/websocket/`, Host,
  Upgrade, Connection, Sec-WebSocket-Key/Version, X-Signal-Receive-Stories, Accept-Language,
  User-Agent) gives 101 (`testdata/mpc-unauthenticated-upgrade-request.bin`,
  `…-response-head.bin`). Nothing else is required. An Authorization header must NOT be sent on
  it: any credentials turn every request on the socket into an identified one (rule 1 below).
* The server sends **no** `queue/empty` and no other request on it (2 s and 100 s observations).
* Sealed-sender PUT on it: header `unidentified-access-key: <base64 of the recipient's 16-byte
  access key>` (24 chars, padded), plus `content-type: application/json`. Same body as today, 200
  `{"needsSync":false}`, envelope without source fields.
* Idle: the server closes **both** kinds of socket after **90.0 s** without I/O, with close 1001
  "Connection Idle Timeout" (observed). The server never pings.
* `GET /v1/keepalive` (`testdata/keepalive-*-request.bin`, 35 bytes: `08 01 12 1f 0a 03 GET 12 0d
  /v1/keepalive 20 <id>`) gets 200, message `OK`, headers `X-Signal-Timestamp:…`,
  `Content-Length:0`, no body, on both sockets (`testdata/keepalive-*-response.bin`, 74 bytes).
* Keeping a socket alive past 90 s (observed on unauthenticated sockets, 110 s runs): client
  WebSocket **pings every 30 s** (each answered by a server **pong**) or **`GET /v1/keepalive`
  every 30 s** (each answered 200) both keep it open. For the MPC client the keepalive request is
  the safer choice: its 200 response is the kind the replay verified above. Whether the parsers
  accept an unsolicited server *pong* frame has not been replayed.

## Harness (`check_signal_service_local.py`)

Runs build (if needed), start, provision, `export-mpc`, optional `--self-check` (reference
sender + verification), the MPC run, verification (both recipients receive the expected texts;
every envelope must have no source fields), and stop. `run_mpc()` raises `NotImplementedError`;
its docstring lists the controller/worker arguments (`ENDPOINT=127.0.0.1 PORT=18443
HOSTNAME=server.example TRUST=<export tls_trust_root_pem>`) and the client changes it depends on:
credentials and admission from the export, a second unauthenticated socket for sends,
`queue/empty` replies, keepalive under 90 s, and record write-back.

## Server rules vs. what the MPC client sends today

V = verified by running against the local server (2026-11-10); S = read from server source
(`/Users/izzy/repos/Signal-Server` @ b9a24fede; paths below are relative to it).

| # | Server rule | Source | MPC client today | Status |
|---|---|---|---|---|
| 1 | **On an authenticated socket the principal wins: `Unidentified-Access-Key` is ignored, the send is IDENTIFIED.** The Envelope gets `source_service_id` + `source_device`, the recipient's server returns type-5 delivery receipts to the sender, `MESSAGES` limiter (60/s keyed sender+destination) applies | `controllers/MessageController.java:275-290`, `entities/IncomingMessage.java:62-66`, `websocket/WebSocketConnection.java:270-271` | sends sealed-sender PUTs on its single **authenticated** socket | **MISMATCH (V)**: delivered envelope carried the sender ACI and device 1; the sender received 2 receipts. Sealed sender is defeated and the server learns the contact graph. The fix is to send on a separate unauthenticated socket (V: then no source fields and no receipts) |
| 2 | Right after an authenticated upgrade the server sends `PUT /api/v1/queue/empty` (and `PUT /api/v1/message` per queued envelope); never on an unauthenticated socket | `WebSocketConnection.java:196-197,250-251` | HEAD: rejects; working tree: scans and replies | **MISMATCH at HEAD (V, executed replay: rejected at stream byte 224)**; working tree accepts |
| 3 | Replies to server requests need `id`, `status` AND `message`, else close 1007; only 2xx acknowledges a message | `websocket-resources/.../ProtobufWebSocketMessage.java:27-29`, `WebSocketConnection.java:264-284` | HEAD: none; working tree: `08 02 1a … 08 id 10 c8 01 1a 02 "OK"` | working tree MATCH (V: server kept the socket and served later requests) |
| 4 | Upgrade: path exactly `/v1/websocket/`; `Basic` base64(`uuid[.device]:password`), no suffix means device 1; bad credentials give **403** (Jetty `sendForbidden`), not 401 | `WhisperServerService.java:1077,1211`; `auth/AccountAuthenticator.java:39,54-110`; `WebSocketResourceProviderFactory.java:78-81` | exact bytes from `RelayUpgrade.lean` | MATCH (V: 101 with real creds, 403 with bogus) |
| 5 | `Host` unused; unknown UA (`tls-mpc`) allowed unless dynamic `requireSpqr` and no spqr capability (499); `Accept-Language` unused on the socket; `X-Signal-Receive-Stories: false` drops stories | `filters/RemoteDeprecationFilter.java:77-139`; `WebsocketHeaders.java:9-11` | `Host: chat.signal.org`, `User-Agent: tls-mpc` | MATCH (V). Production may differ in dynamic config. Accounts must keep the `spqr` capability (provisioning sets it) |
| 6 | 101 response carries `Date`, `Vary`, `X-Signal-Timestamp`, `Upgrade`, `Sec-WebSocket-Accept`, `Connection` | observed | upgrade parser was only tested on the fixture's 3-header 101 | MATCH (executed replay: `TlsWebSocketUpgrade` accepts the real 224-byte head) |
| 7 | Request proto: verb=1 path=2 body=3 id=4 headers=5; REQUEST needs verb+path; inner headers split on `:` and dropped unless exactly 2 parts; name lower-cased, trimmed | `websocket-resources/src/main/proto/WebSocketProtocol.proto`, `ProtobufWebSocketRequestMessage.java:54-59` | same layout, ids from 2^63 | MATCH (V: `mpc-send`, ids 2^63+n round-trip) |
| 8 | Response: id=1 status=2 message=3 body=4 headers=5; headers `Name:value` (no space); body `{"needsSync":false}` for sealed sender | `WebSocketResourceProvider.java:300-349` | fixture sent `content-type: application/json` and body `{}` | MATCH (executed replay: `TlsChatResponse` accepts and correlates the real 131-byte frame; `testdata/send-*.bin`) |
| 9 | Body: `messages` non-empty; `type` a known Envelope type other than 5 (6 OK); `destinationDeviceId` a Java byte (above 127 gives 422); `destinationRegistrationId` int; `content` base64, at least 1 byte; `timestamp` between 0 and 8.64e15, no clock check; `urgent` defaults true; `online`=true means ephemeral | `entities/IncomingMessageList.java:24-66`, `entities/IncomingMessage.java:23-89` | exact JSON with space-padded numbers | MATCH (V: 200 and decrypted) |
| 10 | Device set and registration ids: 409 `{missingDevices,extraDevices}`, 410 `{staleDevices}` (410 wins) | `MessageController.java:454-472`, `push/MessageSender.java:387-423` | one device per contact from its record | MATCH for single-device contacts; multi-device not supported |
| 11 | UAK (unauthenticated path): missing gives 401; wrong gives 401; unknown recipient gives **401** (not 404); not 16 bytes / bad base64 gives 401 even on authenticated | `auth/OptionalAccess.java:53-101`, `auth/Anonymous.java:16-24` | 24-char base64 of 16 bytes | MATCH |
| 12 | 413 above 96 KiB per device; 429 `INBOUND_MESSAGE_BYTES` per destination (128 MiB bucket), `MESSAGES` 60/s identified only; 428 only from the private spam filter (absent locally) | `MessageSender.java:79,364`; `limits/RateLimiters.java:26-27,51` | small texts | MATCH. Production spam filter (428) cannot be exercised locally |
| 13 | Idle timeout 90 s on any I/O; the server never pings; clients send `GET /v1/keepalive` | `WhisperServerService.java:1101`, `KeepAliveController.java` | answers pings, never sends keepalive | RISK (V: close 1001 after 90.0 s idle on both sockets; pings or keepalive requests every 30 s prevent it). MPC operations between requests must not leave a socket silent for 90 s |
| 14 | Sender certificate from `GET /v1/certificate/delivery?includeE164=false`, verified against the trust root | `CertificateController.java:75-89` | fixed CERT=260-byte slot | MISMATCH in size (V: 244 bytes locally); resolved for local runs by unknown-field padding to 260, accepted by libsignal recipients (V). Production's length still unknown |
| 15 | TLS: edge-terminated in production | n/a | TLS 1.3, AES-128-GCM-SHA256, X25519, ALPN http/1.1 | local terminator mirrors the fixture profile; production edge is untested (UNKNOWN) |

### Milestones
1. Authenticated upgrade accepted (101), `queue/empty` handled, idle connection kept alive
   (pings answered) for the session.
2. Sealed-sender send on an established session: `PUT /v1/messages/{aci}` returns 200 and
   `lss-provision receive recipient` decrypts the text (4 sends, 2 contacts: provision a second
   recipient).
3. Prekey-bundle fetch (`GET /v2/keys/{aci}/{device}` with UAK) and first-message (PreKey) send.
4. Receive: `PUT /api/v1/message` envelopes decrypted by the client, with acknowledgement.
5. Error paths on purpose (on the unauthenticated send socket): wrong access key (401), wrong
   registration id (410), extra/missing device (409), rate limit (429), with the client failing closed.

Milestone 2 needs rule 1 above fixed first: two sockets (authenticated for receive/keepalive,
unauthenticated for sealed-sender sends). Check by running `lss-provision receive recipient`:
it prints `source_service_id=None` for a correctly sealed send.

Only after milestones 1-5 pass locally, with transcripts reviewed, should a production attempt be
considered, and only on the owner's explicit go-ahead.
