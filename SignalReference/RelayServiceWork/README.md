# Actual relay service dependency checkpoint

The relay in `../secret-shared-db/server/relay-node` uses an authenticated
HTTP/1.1 WebSocket connection to `chat.signal.org/v1/websocket/`. It fetches all
recipient device keys, encrypts each with sealed sender, and sends a JSON
`PUT /v1/messages/{UUID}?story=false` inside a WebSocket protobuf request.
The synthetic gRPC helper is not this service path.

The implementation target remains libsignal `904c8dc` (v0.106.1). The relay
locks the older imeckler `c1d9fb55`. Their WebSocket schemas are byte-identical;
SSv1 formats are tracked separately. Both inner wire versions are4, but SPQR
versions differ (1.4.0 versus1.6.0). Historical session interoperability and
current deployed-server compatibility are unverified. Exact sources/hashes
are in `compatibility.json`.

Implemented Lean circuits:

- `RelayEncoding`: oblivious base64, canonical UUID text and bounded decimal
  conversion with shared canonical-width rejection.
- `RelayUpgrade`: secret UUID/password Basic auth for the actual WebSocket
  upgrade route. Server HTTP101/accept-header validation is still absent.
- `SealedSenderV1`: established USMC MESSAGE serialization, two96-byte HKDF
  derivations, AES256-CTR32BE from zero, ten-byte HMAC, and0x11 outer protobuf.
  Computed all-zero DH and retained/computed sender identity mismatches are
  rejected by shared masks; no caller-provided correctness flag is substituted.
- `RelayRequest`: one-device type6 JSON, secret UUID/UAK/numeric fields,
  actual WebSocket request protobuf and masked binary frame.
- `SealedRelay`: composes envelope and request rejection inside the circuit.

Universal map/compiler theorems build in Lean. They establish agreement with
these executable Lean definitions, not full actual Rust/Aeneas refinement.
The native oracle calls unchanged target libsignal encrypt/decrypt-to-USMC,
validates generated certificates, rejects modified envelopes, and decodes
requests using the generated actual schema. `report.json` distinguishes
Boolean tests with native-generated DH inputs from the separately implemented
mixed producer, which computes its own DH and fresh ephemeral scalar.

Run `python3 SignalReference/RelayServiceWork/check.py` after exporting the
profiles under `.deps/relay-service-artifacts/`. `SealedExport`, `BoundExport`,
`RequestExport`, `ServiceExport` and `UpgradeExport` are standalone Lean
emitters; their public arguments are shown in each file. Raw build artifacts
stay outside Git. All fixture data is public and disposable; no account or
real-message side effects are performed.

Required dependency order before usable delivery:

1. Complete private-DH/native producer binding and then feed its unopened frame
   to the generic TLS handle. Retire all old VM/protocol traces after each
   private computation, not merely old host vectors.
2. Implement private variable-length framing for canonical Signal/PQ counter
   and JSON/protobuf widths. Width1 versus2 regressions expose127→128 rejection;
   a fixed profile must not silently continue by transmitting zero wire.
3. Bind trusted recipient UUID/UAK/device records and sender certificate to
   authenticated private session state. Complete SPQR epoch/chunk selection,
   all-device fanout and inner-session transitions. One-device encoding is
   usable only for a recipient actually having one device.
4. Complete authenticated HTTP101 and persistent WebSocket control/fragment
   handling. Parse actual response protobuf, including missing/duplicate/unknown
   fields and malformed suffixes; correlate IDs. Only2xx is relay send success.
   Non2xx/timeout never rolls back a ratchet already committed before release.
5. Replace the temporary persistent tombstone fence with authenticated per-party
   share snapshots, globally consistent epoch/attempt/commit IDs and rollback
   detection. No keys may be reconstructed. The current fence refuses every
   restart; it is not recoverable or Byzantine durable storage.
6. Repair pinned Aeneas Step metadata/model translation in an isolated reviewed
   candidate, then finish actual point recovery/XEdDSA/certificate/prekey
   refinement needed for fresh sessions.

No production readiness, complete delivery, proactive-refresh or throughput
claim follows from these component checks.
