# Current parser proof ledger

Historical frozen receipts and global obligations.json are evidence of their
recorded versions; this scoped ledger tracks the current response work.

| Component | Current proof checkpoint | Remaining boundary |
| --- | --- | --- |
| SignalMessage, bounded public input | d76db87; root review 1dd9d55 | Accepted only in its stated bounded/model scope; unchanged here. |
| SignalMessage, true private length | root review 0dc19ed | Accepted scoped take-n/actual-source composition; unchanged here. |
| Contiguous Vec copier | aacda3d (mixed TLS/parser commit) | Exact generated contents/suffix/all-model outcomes; bounded allocation and Take/raw loan content model. |
| Single String field | 82d5b2f; StringContentV3/full-audit.json | All-outcomes actual Prost control composed with varint/copier; executable UTF8 grammar versus optimized unsafe std body remains explicit. |
| Native bytes::Bytes field | be37d6e; BytesContentV1/audit.json | Actual sealed adapter and merger, exact errors/replacement/suffix; immutable allocation/reference-count/pointer content model. |
| Repeated String/header field | RepeatedStringV1/audit.json | Actual body composed with String; exact errors/old headers/order/suffix and Vec effects; inherited String/UTF8/content boundaries. 9,504 native comparisons supplement the kernel theorem. |
| Inner response default / dispatcher | InnerResponseV1/audit.json | Exact generated default/field normal form with actual primitive bridges, String error clear, scalar/Bytes/String/header full references and finite skip. Diagnostic/static/std memory boundaries remain; no full scan or streaming theorem yet. |
| Diagnostic stack / owned error | ad0acce; SchemaV1/diagnostic-audit.json | Exact executable Vec append effects before projection; actual static-reference push extraction remains OPEN/trusted. Functional pending-state/event observation excludes warning log text. |

Next implementation/proof work:

1. Inner default/field integration is implemented and kernel checked. Complete
   the field-to-full-scan invariants, including absolute cursor, private end and
   error state observation; the actual primitive bridges are now available.
2. Prove the bounded full-scan relation to the streaming response state, including
   private actual end, varint/field/group bounds and sticky rejection.
3. Compose actual outer envelope/default/submessage/owned decode behavior.
4. Close actual HTTP header/name/value and Unicode trim validation composition;
   existing status and UTF8-machine component proofs are narrower checkpoints.
5. Connect source eligibility/result to private ID correlation and the existing
   compiled_runByte_correct endpoint. No whole response source→circuit theorem yet.

Core response structural acceptance, valid non-2xx response, successful 2xx,
private pending-ID match, and Mux/application abort policy remain separate.
Malformed DataError frames are ignored by the native caller (with a warning);
matched invalid HTTP responses complete their native request with an error.
No complete ChatConnection scheduling, retry/fanout, log-trace, or Signal session
security theorem is claimed.

Shared TLS/Word64/parser core APIs remain untouched by this response work.
