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
| `scripts/probe_upgrade.py` | sends the MPC client's **exact** WebSocket upgrade bytes (from `TlsMpc/Signal/RelayUpgrade.lean`) through the terminator; `--listen N` decodes the server's frames afterwards |
| `provision/` | `lss-provision`, a conventional Rust Signal client (libsignal-protocol v0.106.1 from `../.deps`, offline vendored crates, same versions as `signal_backend/Oracle`) |
| `scripts/provision.sh` | builds and runs `lss-provision` (default: full provisioning) |
| `state/`, `logs/`, `third_party/` | generated; git-ignored. `state/accounts/*.json` hold LOCAL TEST keys and passwords |

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
# 2. provision two accounts (server state is in-memory: rerun after EVERY server start)
bash scripts/provision.sh                                  # -> {"provisioned":true,...}
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

## Pointing the MPC client at the local server (specification; harness not modified)

`handshake_backend/EmpHybridWork/check_signal_service_v3.py` today:
* starts `signal_backend/TextNotificationWork/fixture_server.py` behind an in-process bridge on a
  random port, and passes the controllers `ENDPOINT=127.0.0.1 PORT=<bridge> HOSTNAME=server.example
  AUTH=<public_auth> TRUST=<fixture ca.pem>`;
* runs workers with `TLS_WORKER_SERVICE_FIXTURE=text`, which admits compiled-in public state:
  `signal_backend/TextNotificationWork/PublicTextFixture.h` (two conversation records + four texts);
* uses hardcoded upgrade credentials in `service_kernels.h` (`upgrade()`: UUID
  `00112233-4455-6677-8899-aabbccddeeff`, password `'x' * 22`);
* lets the fixture server's libsignal recipient decrypt and check the texts.

A local-server variant (`check_signal_service_local.py`, to be written) needs:
1. **Network**: no bridge, no fixture server. Controller args `ENDPOINT=127.0.0.1 PORT=18443
   HOSTNAME=server.example TRUST=local_signal_server/state/tls/ca.pem` (same `public_auth`).
   The leaf is Ed25519 like the harness's chosen profile; `LEAF_KEY=p256` exists if needed.
2. **Credentials** (replace the hardcoded ones): sender `aci` as 16 bytes, sender `password` (22 bytes).
3. **Per-contact conversation record** (`initial` blob = 32-byte identity secret || record):
   * identity secret: sender ACI identity private key (`aci_identity_key_pair`);
   * certificate slot (CERT=260 bytes): the sender certificate. **The local one is 244 bytes**:
     the slot size or the certificate needs reconciling (see Risks);
   * session block (182 + text capacity bytes): projected from the sender's libsignal
     `SessionRecord` for `<recipient aci>.1` (same projection the oracle crate uses for the
     fixtures; the record is in `sessions` of `sender.json`);
   * metadata (57 bytes): recipient UUID (0..16), recipient access key (16..32), request id
     (40..48), device id (48), registration id (49..53), as read by `signalRequestSeal`.
   Write this as a small exporter next to `lss-provision` (`lss-provision export-mpc`) that
   emits the same JSON shape as `text-fixtures.json`, so `prepare_fixtures.py`-style code can
   produce the admission header or, better, a runtime admission file.
4. **Verification**: after the MPC run, `scripts/provision.sh receive recipient 30` must print
   the four texts with their timestamps. The recipient's local session must not have moved
   independently (do not send recipient->sender between provisioning and the MPC run).
5. **Receive handling**: the server pushes `PUT /api/v1/queue/empty` right after every
   authenticated upgrade (verified), and `PUT /api/v1/message` for any queued message. The public
   receive controller currently aborts on any server-initiated message. It must at least accept
   `queue/empty` (and answer it) before milestone 1 can pass.

## Server rules vs. what the MPC client sends today

V = verified by running against the local server (2026-11-10); S = read from server source
(`/Users/izzy/repos/Signal-Server` @ b9a24fede; paths below are relative to it).

| # | Server rule | Source | MPC client today | Status |
|---|---|---|---|---|
| 1 | **On an authenticated socket the principal wins: `Unidentified-Access-Key` is ignored, the send is IDENTIFIED.** The Envelope gets `source_service_id` + `source_device`, the recipient's server returns type-5 delivery receipts to the sender, `MESSAGES` limiter (60/s keyed sender+destination) applies | `controllers/MessageController.java:275-290`, `entities/IncomingMessage.java:62-66`, `websocket/WebSocketConnection.java:270-271` | sends sealed-sender PUTs on its single **authenticated** socket | **MISMATCH (V)**: delivered envelope carried the sender ACI and device 1; the sender received 2 receipts. Sealed sender is defeated and the server learns the contact graph. The fix is to send on a separate unauthenticated socket (V: then no source fields and no receipts) |
| 2 | Right after an authenticated upgrade the server sends `PUT /api/v1/queue/empty` (and `PUT /api/v1/message` per queued envelope) | `WebSocketConnection.java:196-197,250-251` | public receive aborts on any server-initiated message | **MISMATCH (V)**: arrives ~10 ms after the 101 |
| 3 | Replies to server requests need `id`, `status` AND `message`, else close 1007; only 2xx acknowledges a message | `websocket-resources/.../ProtobufWebSocketMessage.java:27-29`, `WebSocketConnection.java:264-284` | sends no replies | must be implemented with #2 |
| 4 | Upgrade: path exactly `/v1/websocket/`; `Basic` base64(`uuid[.device]:password`), no suffix means device 1; bad credentials give **403** (Jetty `sendForbidden`), not 401 | `WhisperServerService.java:1077,1211`; `auth/AccountAuthenticator.java:39,54-110`; `WebSocketResourceProviderFactory.java:78-81` | exact bytes from `RelayUpgrade.lean` | MATCH (V: 101 with real creds, 403 with bogus) |
| 5 | `Host` unused; unknown UA (`tls-mpc`) allowed unless dynamic `requireSpqr` and no spqr capability (499); `Accept-Language` unused on the socket; `X-Signal-Receive-Stories: false` drops stories | `filters/RemoteDeprecationFilter.java:77-139`; `WebsocketHeaders.java:9-11` | `Host: chat.signal.org`, `User-Agent: tls-mpc` | MATCH (V). Production may differ in dynamic config. Accounts must keep the `spqr` capability (provisioning sets it) |
| 6 | 101 response carries `Date`, `Vary`, `X-Signal-Timestamp`, `Upgrade`, `Sec-WebSocket-Accept`, `Connection` | observed | upgrade parser was only tested on the fixture's 3-header 101 | UNKNOWN: run the Lean `TlsWebSocketUpgrade` parser on the recorded 101 |
| 7 | Request proto: verb=1 path=2 body=3 id=4 headers=5; REQUEST needs verb+path; inner headers split on `:` and dropped unless exactly 2 parts; name lower-cased, trimmed | `websocket-resources/src/main/proto/WebSocketProtocol.proto`, `ProtobufWebSocketRequestMessage.java:54-59` | same layout, ids from 2^63 | MATCH (V: `mpc-send`, ids 2^63+n round-trip) |
| 8 | Response: id=1 status=2 message=3 body=4 headers=5; headers `Name:value` (no space); body `{"needsSync":false}` for sealed sender | `WebSocketResourceProvider.java:300-349` | fixture sent `content-type: application/json` and body `{}` | UNKNOWN: real 127-byte response saved in `state/transcripts/mpc-send-response.bin`; replay through `TlsChatResponse` |
| 9 | Body: `messages` non-empty; `type` a known Envelope type other than 5 (6 OK); `destinationDeviceId` a Java byte (above 127 gives 422); `destinationRegistrationId` int; `content` base64, at least 1 byte; `timestamp` between 0 and 8.64e15, no clock check; `urgent` defaults true; `online`=true means ephemeral | `entities/IncomingMessageList.java:24-66`, `entities/IncomingMessage.java:23-89` | exact JSON with space-padded numbers | MATCH (V: 200 and decrypted) |
| 10 | Device set and registration ids: 409 `{missingDevices,extraDevices}`, 410 `{staleDevices}` (410 wins) | `MessageController.java:454-472`, `push/MessageSender.java:387-423` | one device per contact from its record | MATCH for single-device contacts; multi-device not supported |
| 11 | UAK (unauthenticated path): missing gives 401; wrong gives 401; unknown recipient gives **401** (not 404); not 16 bytes / bad base64 gives 401 even on authenticated | `auth/OptionalAccess.java:53-101`, `auth/Anonymous.java:16-24` | 24-char base64 of 16 bytes | MATCH |
| 12 | 413 above 96 KiB per device; 429 `INBOUND_MESSAGE_BYTES` per destination (128 MiB bucket), `MESSAGES` 60/s identified only; 428 only from the private spam filter (absent locally) | `MessageSender.java:79,364`; `limits/RateLimiters.java:26-27,51` | small texts | MATCH. Production spam filter (428) cannot be exercised locally |
| 13 | Idle timeout 90 s on any I/O; the server never pings; clients send `GET /v1/keepalive` | `WhisperServerService.java:1101`, `KeepAliveController.java` | answers pings, never sends keepalive | RISK for sessions idle more than 90 s (fixture pinged the client; the real server does not) |
| 14 | Sender certificate from `GET /v1/certificate/delivery?includeE164=false`, verified against the trust root | `CertificateController.java:75-89` | fixed CERT=260-byte slot | **MISMATCH (V)**: local certificate is 244 bytes; production's size depends on its signer cert and E164 choice |
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
