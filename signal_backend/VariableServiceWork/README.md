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
