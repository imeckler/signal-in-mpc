# Native private variable conversation candidate

`VariableShape(260,0,false,false)` has no public varint-width selectors:
input531 bytes; output1269 bytes = status1 + selected chain/request state80 +
BE16 private length2 + frame capacity1186. The store returns typed payload1189
and unopened current requestID8. It retains identity secret, certificate,
recipient/UAK/device bindings, selected chain state and next request ID; each
call accepts only shared payload(kind/chunk/plaintext) and timestamp. The native
function computes four X25519 products and generates an independent fresh
SS ephemeral scalar and WebSocket mask. No DH/scalar import API exists.

`VariableSendStore<Bits>` commits selected state before exposing its payload,
serializes attempts, and unlocks only through `response_complete(ticket)`.
Actual callers must first validate an authenticated correlated response policy;
failed/uncertain send, timeout or non2xx closes under the current policy.
Never roll back a possibly consumed chain. Temporary fsynced tombstones reject
all restarts: they are not recoverable or Byzantine durable storage. Stable
authoritative slot mapping and no tombstone rollback/deletion are assumptions.

The five-party public synthetic native fixture uses unopened output state and
request IDs for its second send across127→128. Actual pinned Signal wire,
SS decryption/certificate/tamper and relay-schema checks pass; mismatched
sender binding rejects. It opens only synthetic final payload/status. Its
acknowledgements are explicitly fixture-only, with no TLS/service response.
Elapsed380.93s is startup plus three component calls, not throughput.

Descriptor/manifest:
`.deps/private-variable-conversation-native/260-0-0-0/service.manifest`
`signal_private_variable_conversation_260_0_0_0-sbv:[4248x1]-sbv:[10152x1]`

Compiler upper bounds:6,378,373 bit triples,119,043 VM rounds,20,404 integer
multiplications,1024 integer randoms,8 masked/integrity integer opens,32 WS
random bits. The conversion/runtime/compiler backend remains unverified;
Lean compiler agreement does not establish every integer packing/hash semantic
refinement. Active epoch/KEM transitions, authenticated initial state binding,
all-device fanout, real response/TLS integration, recoverable snapshots and
full Rust/Aeneas refinement remain open. Application readiness stays closed.

Local integration helpers (PUBLIC DISPOSABLE FIXTURE ONLY):

- `PublicFixtureProducer.h`: `PublicVariableProducer<Bits>(public_bits,slot)`;
  `produce(eval,public_bits,timestampBE8)` returns `{ticket,payload,request_id}`;
  `response_complete(ticket)`, `close()`, `shape()`. Limit two sends. Initial
  state exactly matches the tested native fixture. Timestamp public fixture
  bytes come from `PublicVariableFixture::timestamp()`. Runtime link probe
  compiles this exact API but does not execute private computation.
- `fixture_server.py CERT KEY FRAGMENT no http/1.1 [--report PATH]`: executable
  memory-BIO line peer. Input ciphertexthex or `-`; output `ready|waiting HEX`
  (`-` means no bytes); `quit` asserts both requests/pongs completed and exits.
  TLS1.3, X25519, H1 and AES128 are asserted for the native controller. No
  unsolicited application banner. Header response writes are<=127 bytes with
  coalesced WS ping. Binary responses are fragmented around interleaved ping.
  Masked client controls/fragments are parsed without dumping plaintext.
- `server-fixture.json` contains disposable recipient/root/expected-inner and
  protocol assertions only; no client identity secret or chain state. The
  server checks actual generated request schema, SS decrypt/certificate and
  exact expected inner, then copies the ID into a200 JSON{} response. Response
  encoding is checked by actual prost plus the explicitly copied inspected
  target validator. It never calls live Signal services.

`check_fixture_server.py` passed a local standard Python TLS1.3 MemoryBIO
exchange using both actual native frames, split HTTP headers, coalesced ping,
a fragmented second client request, client ping, three masked pongs, fragmented
correlated responses and close. This standard-client test permits its default
TLS1.3 cipher; native AES128/controller integration is separate and unclaimed.
The server implementation is an unverified test harness, not a new production
protocol implementation or private parsing proof.
