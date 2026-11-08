Isolated diagnostic overlay v1 (candidate; partial attribution)

The additive runtime builds in .deps/tls-backend-diagnostic-runtime/MP-SPDZ,
from a complete hashed source/config identity. It preserves the tested runtime.
The quiescent getter instantiates against actual Processor/DataF types. Byte
hooks follow the existing Player sent accounting, including virtual pairwise
sends; they do not include TLS/socket headers. Static domain/phase scopes tag
Beaver exchanges and triple requests. Nested preprocessing stays preprocessing;
new threads/other protocol paths remain explicitly unattributed. Scope duration
subtotals overlap and must not be summed. ASAN/UBSAN counter checks pass nested
scope, exception restoration, thread-default and exact byte-partition tests.

The public microprogram uses64 Boolean ANDs,8checked bit→field conversions,
oneFp25519 multiplication, and the existing exact canonical field→binary
conversion using255checked daBits (compiler security128, -X, no edaBits). A
separate comparison circuit opens only a255/0 synthetic equality byte. Three
calls retain private derived state across real worker/transport epochs, then
abort through the erased-host barrier. All five parties passed in1.86 Python
awake seconds; no cleanup errors, source/product integrity unchanged. This is
CCD baseline only: no MASCOT/Tinier, malicious tamper or OT lifecycle pass yet.

Per party0 mix call, consumed DataF receipt is field triple1, field daBits263,
binary triples1852. These are observed consumed entries, not generated-buffer
sizes. This single-worker closure uses the last per-worker usage getter; do not
sum it across arbitrary parallel/reused-worker schedules without job accounting.
Measured load_schedule time~177–179ms/call and prepare~197–203ms/call show public
loader cost can be material on this tiny workload. This is not a full-run
loader fraction or a cache speedup. No cache changes are made.

Attribution v1 is incomplete:9,450,816bytes/call remain unattributed versus field
online267,776/preprocessing469,760 and binary online237,056/preprocessing415,328.
Next add checked-daBit fetch and per-domain input/open/check tags, then reconcile
all buckets against independent total-byte deltas on this same small fixture.
No full application rerun is needed. Preserve this run as v1 evidence.

Failed pre-MPC raw5d12c6ddbf273105 was a dyld library search issue; all children
were reaped. The stage now explicitly binds the diagnostic library. Positive
raw3a16e36c17661dc0 and ccd-native-report.json preserve exact hashes. No live
handles remain after the baseline (42051 terminal0).

V2 attribution and Tinier boundary

Fresh v2 library plus3-step native fixture pass all five parties/1.414awake
seconds, clean epochs/abort and unchanged hashes. The worker schedule must have
exactly one worker for the usage getter; parallel/stale per-worker usage sums
are rejected. Scope context now follows worker jobs; per-domain input/open/check
and checked-daBit fetch tags attribute most prior unknown traffic. Party0 percall:
field-preprocessing10,343,520B; binary-preprocessing258,240B; binary-online237,632B;
field-online384B; unattributed960B. Counters include initialization while original
Player/queue statistics deliberately reset after Processor construction. Their
difference is576B forparty0/512B forothers; an explicit initialization reset
receipt is the next reconciliation step. Generated/discarded preprocessing
batches are NOT measured by the consumed DataF getter. All3calls renew the epoch:
this measures that policy, not a mandatory per-record protocol property.

Tinier statistical128 is unsupported in the pinned implementation. The real
ShuffleSacrifice constructor rejects security_parameter>40; TinyPrep's secret
triple generation uses this class. Compiled guard regression confirms rejection
at128 with no parties. Its minimum batch tables support onlybucket sizes3/4/5
at the implemented40-bit setting. A128-bit MAC field does not change the triple
sacrifice boundary. No guard removal, lower-security run, ad hoc repetition or
Tinier128 native pass is claimed. Supported primary-source alternatives must be
examined before any new sacrifice design or backend switch.

V3 exact reconciliation

The fresh v3 library records Player.total_comm().sent immediately before the
runtime's explicit initialization reset. All15native observations reconcile
exactly: all domain/phase buckets = original recorded bytes + reset receipt
(576B party0,512B others). Three state/epoch calls and abort pass allfive/1.452
awake seconds, cleanup empty, immutable products stable. Timing may overlap
other public compiler work and is not an uncontended speed comparison. No
application runtime or default backend has changed.

Supported BMR experiment preparation (not native-certified)

The pinned malicious Shamir BMR entrypoint usesGF(2^128), with live malicious
Shamir preprocessing and encrypted honest-majority channels. A fresh source-bound
candidate raises MAX_N_PARTIES3→5 and builds the standard binary plus small
component entrypoints. Explicit-S128 and globaln5/t2 are checked. Upstream
RealProgramParty creates a new parser without-T: the wrapper keeps the already
validated ShamirOptions threshold2 and omits only that duplicate CLI option from
the second parser; it checks the threshold again on return. No security guard
is removed. This is a purebinary381AND three-state comparison experiment, not
the mixed-Fp conversion benchmark, a retirement capability, or a default switch.

The tiny CCD group executed successfully, but the first harness incorrectly
expected party0's comparison printouts on every party (raw68ecfd894db33e90,
all5exit0). Fixed print handling then reached BMR's pre-network secondary parser
failure (raw2f2c9ba094713443). All children were reaped in both cases. The BMR
wrapper fix compiles/links; its native retry is held for another agent's active
receive test. A successful BMR protocol or performance comparison is pending.
