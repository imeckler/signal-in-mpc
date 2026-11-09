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
| Actual outer envelope fields | OuterEnvelopeV1/audit.json | Sixteen-module kernel check: actual default/envelope dispatcher and signed enum scalar; reachable response field/submessage equals proved inner source on all outcomes. Encoding/clear slots fail closed and proved irrelevant to parse. Actual request dispatcher/all-wire consumption and both actual submessage finite scans now proved without primitive validity/termination premises. Complete actual owned outer scan finite trace now composes full returned-buffer bounds, constructor/context100 and exact error result, with ordinary Err/fail/div preserved. Streaming/HTTP/correlation/compiler relation remains open. |
| Numeric streaming varints/scalars | StreamingV1/audit.json | Three checked modules: actual Core3-lane nonterminal prefix invariant; all10payload/terminal/strict-overflow guards; actual ID/type/status terminal updates and native signed enum/u32 low32 projections preserving errors/old value/suffix. Full span/cursor/schema relation and HTTP/correlation/compiler remain open. |
| Numeric/native prefix span and cursor | StreamingV1/span-audit.json | Three new modules: complete Core nonterminal prefix→shared reader; actual native strict-row success/reject→exact value/count and absolute suffix; no-wrap4096-byte cursors. Native fast-error unchanged cursor retained; not equated to Core bytes-read count. Terminal→strict row and full schema-streaming/HTTP/correlation/compiler relation remain open. |
| Diagnostic stack / owned error | ad0acce; SchemaV1/diagnostic-audit.json | Exact executable Vec append effects before projection; actual static-reference push extraction remains OPEN/trusted. Functional pending-state/event observation excludes warning log text. |

Next implementation/proof work:

1. Inner default/field integration and complete scan finite execution are
   implemented and kernel checked. Compose the scan invariants with absolute
   cursor/private end and the streaming error-state observation.
2. Prove the bounded full-scan relation to the streaming response state, including
   private actual end, varint/field/group bounds and sticky rejection.
3. Actual outer envelope/default/submessage/owned decode finite execution is
   composed. Establish absolute-cursor/success-span and numeric streaming
   invariants against that complete actual source computation.
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

Terminal lexer checkpoint: `StreamingV1/terminal-audit.json` now records a clean
two-module combined exit0 in separate output `terminal-v1-final`. Actual Core
accumulation constructs the accepted strict numeric row, then the pinned native
Prost value/exact tail with explicit in-input bound. Noncanonical encodings are
included. Lane/position/span establishment across the schema and malformed/EOF
lexer cases remain subsequent work; no whole streaming theorem is claimed.

Rejection lexer checkpoint: `StreamingV1/rejected-audit.json` records a clean
three-module combined exit0. Truncated all-continuation inputs and invalid tenth
bytes now derive native rejection with exact error suffix; actual Core rejects
bad tenth bytes after the prefix invariant, and finish rejects scalar/length EOF
or a nonempty incomplete key. Clean key boundaries are explicitly distinguished.
Whole-schema/private-end induction and HTTP/correlation/compiler composition
remain open; this is not a full response acceptance theorem.

Key/sticky checkpoint: `StreamingV1/key-closure-audit.json` records clean two-module
aggregate0. The actual Core terminal value now composes with native key
validation and the generated driver's adapter (all key-validation errors retained).
Actual Core invalidity is sticky under arbitrary byte tails and finish; the bad
tenth-byte theorem composes through complete remaining input. Common key checks
and field transitions still need connection to Core guards in the schema invariant.

Key transition checkpoint: `StreamingV1/key-transition-audit.json` records a
clean kernel exit0. Native successful key validation supplies the exact tag and
wire-kind equalities for actual Core stored-tag and next-lane transitions across
all six wire kinds; actual terminal value reset is proved. The common key guard,
known-field wire/depth guards and full schema/private-end induction remain open.

Common key rejection checkpoint: `StreamingV1/key-guard-audit.json` records
clean aggregate0 for the affected accepted KeyCircuit dependency and two new
modules. Native key-validation Err now implies zero actual Core validity and
sticky rejection through arbitrary tails/finalization. The original range/
wire/tag diagnostic ordering/suffix remains in the native bridge. Known-field
wire/depth conditions and whole schema/private-end induction remain open.

All-input attempted-key-error branch: `StreamingV1/any-key-error-audit.json`
records clean two-module aggregate0. Exhaustive lexer classification removes
supplied-prefix/table premises: every nonempty input whose actual generated
schema driver key decoder errors is rejected by the actual Core fold/finish.
Native error contents/cursor remain exact in the source key reference. The
successful field/group/schema/private-end induction remains open.

All-input successful-key branch: `StreamingV1/any-key-success-audit.json`
records clean two-module aggregate0. Every actual generated driver successful
key supplies exact input/tail span, bounded count, actual Core stored tag,
wire-kind lane, accumulator reset and position reset without supplied-prefix/
table premises. Both attempted-key branches are now composed; successful field/
group/private-end/full-scan and HTTP/correlation/compiler work remains open.

Scalar payload checkpoint: `StreamingV1/scalar-payload-audit.json` records clean
two-module aggregate0. The actual uint64/u32 mergers compose with actual Core
payload accumulation/reset and error rejection on every input/outcome. Exact
source scalar values, old-value/error/suffix observations and low32 projection
are preserved. This does not yet supply inner-end bounds, optional-field
initialization/duplicates or message-state updates in the full scan invariant.

Bounded scalar state checkpoint: `StreamingV1/scalar-update-audit.json` records
clean four-module aggregate0. An explicit native child-cursor check derives
inside-response terminal span and actual Core prefix tag/recognition/inner
preservation plus exact remaining decrement; actual ID/status updates equal
full64/low32 source values without prefix/table premises. Whole scan must still
derive those cursor/counter/recognition relations at each field, and compose
optional initialization/duplicates/other fields/groups/private end/HTTP/compiler.
