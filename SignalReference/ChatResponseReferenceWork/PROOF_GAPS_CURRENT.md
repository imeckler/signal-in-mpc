# Current parser proof ledger

Historical frozen receipts and global obligations.json retain their recorded
scope. This mutable scoped ledger summarizes the latest response work; receipts
and module statements define the exact hypotheses. No complete ChatResponse
source→streaming→HTTP/correlation→circuit theorem is claimed.

| Component | Latest checked evidence | Current scope / remaining boundary |
| --- | --- | --- |
| Bounded SignalMessage public input | d76db87; root review 1dd9d55 | Accepted bounded all-outcomes composition; unchanged. |
| SignalMessage true private length | root review 0dc19ed | Accepted scoped take-n/actual-source composition; unchanged. |
| Actual contiguous Vec copier | aacda3d (mixed TLS/parser provenance) | Generated loop/content/suffix bridge; bounded allocation and contiguous Take/raw-loan model. |
| Actual String / bytes::Bytes / repeated headers | 82d5b2f; be37d6e; RepeatedStringV1/audit.json | Actual primitive control/effects composed, including String clear and repeated append/errors. Explicit std/content boundaries below. |
| Actual diagnostic stack model | ad0acce; SchemaV1/diagnostic-audit.json | Exact executable push effects/order; actual static-reference push extraction remains OPEN/trusted. |
| Grounded borrowed-triple FnMut ABI | 6a7b07b; FnMutBorrowV1/audit.json | Typed inverse projection, original caller kernel check, native comparisons and fail-closed guards; canonical translator/models unchanged. |
| Actual schema defaults/field dispatch | InnerResponseV1/audit.json; OuterEnvelopeV1/audit.json | Actual request/response/envelope dispatch and primitives, all outcomes; encoding/clear slots proved irrelevant to parse. |
| Actual full owned source scan | 5b2ee7d; OuterEnvelopeV1/audit.json | Complete finite inner/request/submessage/outer scan composition; exact constructor/context100, parent-limit overrun, ordinary Err/fail/div. No primitive-validity/termination premise. Streaming equality still open. |
| Core prefix / strict reader / native cursors | StreamingV1/audit.json; span-audit.json; terminal-audit.json | Three lanes, exact accumulator/terminal/tenth guards, native success/rejection, exact relative/absolute suffix and no-wrap4096 cursor. Original audit's raw-log limitation remains recorded; newer combined receipts have immutable clean logs. |
| All-input attempted key branches | any-key-error-audit.json; any-key-success-audit.json | Exhaustive lexer classification removes prefix/table premises. Actual driver key Err forces Core rejection; successful key gives exact span/tail/tag/lane/value+position reset. |
| Native key field recognition | native-recognition-audit.json | Native key success derives actual Core scalar/response/body/message/header recognition outer and bounded inner; exact kind-list shape. Child cursor/counter/depth conditions remain explicit. |
| Bounded scalar context / updates | scalar-payload-audit.json; scalar-update-audit.json; prefix-context-audit.json | Actual all-outcome native scalar payload relation; exact prefix counter/tag/recognition/depth/inner preservation; actual full64 ID and low32 status updates. |
| Actual known-field wire checks | c39e00c; wrong-wire-audit.json | Exact all-six-kind guard; native wrong-wire key branches reject complete Core fold/finish outer and bounded inner. Nested groups have no schema recognition. |
| Actual scalar dispatcher field composition | scalar-field-audit.json | Every source ID/status outcome retains optional initialization/duplicates/errors/diagnostics/suffix. Bounded successful fields match Core ID+presence/status; errors reject. Full scan must derive child bounds and other state preservation. |
| Actual generated message String field | string-field-audit.json | All native length outcomes preserve optional initialization/duplicates/source total clear/suffix/diagnostic effects; exact UTF success/failure results and invalid-UTF source result join Core rejection on same copied bytes. Post-header state explicit; successful full-state/headers/full scan joins remain open. |
| Actual String payload UTF rejection | string-rejection-audit.json | Every nonempty complete bounded message/header payload rejected by executable grammar forces actual Core valid0, including incomplete final scalars; no initial valid255 premise. Exact post-header count/reset/recognition and source String result joins remain for field composition. |
| Actual streaming String UTF state | string-utf-audit.json | Actual Core reset and bounded payload UTF state match executable grammar for all byte lists, including malformed/truncated and already rejected records. No success premise; std raw-pointer validator bridge and actual String/headers/full-field joins remain open. |
| Native length-header validity | body-header-validity-audit.json; length-validity-audit.json | Actual native varint success and complete payload fitting private child derive header validity, including zero-length exact child closure. Key/scalar/length continuation invariants checked. Payload/data/event joins and full scan remain open. |
| Complete actual successful body field | body-complete-audit.json | Actual generated Bytes merger/source content/suffix joins one consumed prefix, complete body cache update/other-cache preservation, valid255, key mode/zero skip and exact copied-byte payload events. Header/private counters derived, including empty exact-end and duplicate bodies. Full scan must establish entry relations and join error/overrun branches; cache remains partial, header reset trace separate. |
| Joined actual scalar success | scalar-complete-audit.json | Actual generated ID/status source result joins one exact consumed-prefix/suffix, cached-data/other-cache preservation, validity and key/position/value reset. Full scan must establish initial relations and post-field scope/counters; errors/overruns remain explicit separate branches. |
| Native scalar success validity | scalar-valid-audit.json | Actual native successful scalar within child/public budget preserves Core validity through exact consumed prefix/suffix; terminal/tenth/count facts derived. Full scan must establish initial-state/budget/depth relations and join data/control. |
| Declared-child overrun rejection | child-overrun-audit.json | Varint prefixes/native successful varints crossing child end and physically available length payload overruns reject Core, with explicit positive bounded remaining/cursor conditions. Native later error/suffix retained separately; full trace derivation and zero-remaining prior-rejection joins remain open. |
| Complete copied-body cached data | body-data-audit.json | Exact source successful copy plus full consumed-prefix/native-suffix and post-payload cache/key-mode/zero-skip relation. Other cached response fields preserved; cache is not the final observation. Valid/event/full-state relation remains open. |
| Actual Bytes body dispatcher | body-field-audit.json | All-input/outcome source copy/default/duplicate/error/suffix effects and exact copied length; Core derived length/presence/mode, malformed varint and physical body underflow rejection. Payload-state/event/validity and child overrun joins remain open. |
| Opaque/body numeric transitions | opaque-body-audit.json | Exact prefix/count/completion/truncated EOF and body length/presence/reset, including empty duplicates; event masks equal next-valid. Source Bytes copy/event equality and valid-mask preservation remain open. |
| Inactive padding / compiler endpoint | 7201891; inactive-audit.json | Actual process state shape, complete inactive state preservation and zero events through arbitrary padding; existing AIG byte endpoint composed under explicit raw-state/zero-control hypotheses. Not active private-EOF/source refinement. |

Next implementation/proof work:

1. Compose the complete actual source scan with the numeric message-state
   invariant. Derive child cursor/counter/depth/recognition conditions from real
   submessage execution; prove preservation of all remaining state fields and
   optional/duplicate semantics. Scalar field components are checked; whole scan
   composition, correct-wire String/Bytes/header transitions and derivation of the checked
   child-overrun conditions are still open.
2. Prove numeric unknown/group skipping agrees with the actual finite skip
   semantics, including matching tags, stack restoration and 100/99 recursion
   budgets. Exact source skip totality is available; complete Core agreement is
   not supplied by the schema guard component.
3. Join active prefix/input bounds and actual private EOF, including truncated
   varints/lengths/fields and declared submessage lengths beyond actual input.
   Inactive padding is proved independently and does not substitute for this.
4. Compose actual HTTP header/name/value and Rust Unicode trim validation, source
   envelope/type/ID validation and private correlation. Status range, signed enum
   and low32 projections, and full UTF8 byte-machine/spec components are proved.
5. Compose the resulting active source eligibility/result relation with the
   existing production compiler endpoint. Preserve full native errors/cursors
   before the justified owned-result observation; no full response theorem yet.

Explicit source/model boundaries:

- The optimized unsafe std UTF8 raw-pointer/word implementation is not bridged.
  Executable UTF8 grammar↔Core byte machine is proved for all byte lists; it does
  not itself prove the optimized std body.
- Successful bounded Vec/String/Bytes allocation/content, immutable Bytes
  reference counting/pointers and safe contiguous buffers/Take/raw loans are
  scoped model boundaries, not general allocator or unsafe-memory verification.
- Actual static-reference DecodeError.push extraction remains OPEN/trusted.
  The executable diagnostic model retains mutation order, allocation/fail/div
  effects before any quotient of unobserved stack contents. Warning log text is
  excluded from the functional observation.
- Native owned decode hides a failed message value; source partial-record/error
  mutation remains exact in the reference. No full Core/internal merge-error
  record equality is asserted. Native submessage fields may consume beyond the
  child limit before reporting DelimitedLengthExceeded; Core may reject earlier.
  Native fast varint errors can leave the cursor unchanged. These exact source
  suffixes remain explicit and are not falsely equated to Core bytes processed.

Core structural acceptance, valid non-2xx, successful 2xx, private pending-ID match
and stricter Mux/application abort remain separate. Native malformed DataError
frames are ignored with a warning; matched invalid HTTP responses consume their
request with an error. No complete ChatConnection scheduler/retry/device-fanout
or Signal-session security theorem is claimed. Shared TLS/Word64/parser runtime
APIs and historical accepted checkpoints remain untouched by this work.
