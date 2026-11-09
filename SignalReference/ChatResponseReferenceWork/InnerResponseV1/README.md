Candidate inner WebSocketResponseMessage source integration. This is not yet the
whole response-wire→streaming/compiler theorem.

The unchanged pinned generated default and field dispatcher extract/translate.
Replayed shares identical pinned Rust primitive types with BytesContentV1 and
uses the established String byte-content interpretation. Computational Funs
changes imports only. ScalarSource replays the actual generated uint32/uint64
bodies with namespace qualification only; their full varint/error/suffix proof
has no primitive correctness or termination premise.

All five known fields are connected to actual proved primitives: full-width ID,
low32 status, String, bytes::Bytes and repeated String/header. StringBridge
executes the separately proved total DropGuard.clear on Err before returning to
the field callback, preserving the empty error-time field state and exact suffix.
The Bytes adapter shim is proved equal to the actual native content merger.
Unknowns call actual skip_field, with the inherited finite derivation establishing
termination for every slice, wire kind and recursion budget, including zero.

DispatcherReference proves the actual default and complete field normal form,
including absent/existing optional values and ordinary error initialization.
Result failure/divergence and diagnostic append effects remain in order before
record return; no success-only observation or assumed parser validity is used.
The diagnostic callbacks are the explicit SchemaV1 model: static-reference
DecodeError.push extraction is OPEN/trusted. Warning log text is excluded only
at the documented native caller's functional pending-state/event observation.

Other inherited boundaries remain: optimized unsafe std UTF8 versus executable
grammar, bounded successful Vec/String allocation and immutable buffer/Take/raw
loan content representation. Unused encode-only methods fail closed. No arbitrary
segmented Buf or unsafe-memory theorem is claimed.

Remaining: bounded complete scan relation; actual outer envelope/submessage and
owned decode composition; native HTTP header/name/value/Unicode trim validation;
private end, correlation and compiled endpoint composition. Structural response,
non-2xx validity, 2xx success and stricter Mux abort policy remain separate.
check.py reuses hash-verified inherited object receipts and checks only the new
owned integration modules in separate output during the native TLS build hold.
