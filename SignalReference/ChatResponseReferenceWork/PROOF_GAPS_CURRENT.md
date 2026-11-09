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
| Inner owned merge driver | InnerScanV1/audit.json | Actual dispatcher installed; key strict consumption, scalar/String suffix bounds and all-effects finite-run framework; finite success/error traces project to actual merge loop; exact owned error result. Complete actual inner scan finite execution now proved from complete all-wire field consumption, preserving outer fail/div. Full outer schema and streaming composition remain open. |
| Borrowed-triple FnMut ABI | 6a7b07b; FnMutBorrowV1/audit.json | Grounded typed raw/trait inverse projection; six-module original caller check,8192 native cases,two fail-closed shape guards. Canonical translator/model unchanged. |
| Actual generic Prost submessage | SubmessageV1/audit.json | Actual message::merge/merge_loop/closure computations kernel check with grounded typed projection; exact wire/recursion/end/overrun facts and10800 native result/mutation/suffix comparisons. Complete instantiated inner-response parent-limit loop finite execution now proved from actual key/field bounds, preserving Err/fail/div and overrun behavior. Outer/streaming composition remains open. |
| Actual outer envelope fields | OuterEnvelopeV1/audit.json | Eight-module kernel check: actual default/envelope dispatcher and signed enum scalar; reachable response field/submessage equals proved inner source on all outcomes. Encoding/clear slots fail closed and proved irrelevant to parse. Request/full envelope scan and streaming/HTTP/correlation/compiler relation remain open. |
| Diagnostic stack / owned error | ad0acce; SchemaV1/diagnostic-audit.json | Exact executable Vec append effects before projection; actual static-reference push extraction remains OPEN/trusted. Functional pending-state/event observation excludes warning log text. |

Next implementation/proof work:

1. Inner default/field integration and complete scan finite execution are
   implemented and kernel checked. Compose the scan invariants with absolute
   cursor/private end and the streaming error-state observation.
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
