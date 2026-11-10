# Signal reference and Lean implementation

The production implementation path is Lean → proved circuit lowering → numeric
artifact → an unverified MPC adapter. Python files here only orchestrate extraction,
audit provenance, or run independent public test fixtures.

Completed implementation-reference results include:

* `LibSignalReference/Generated/KeyAccessors` is the actual Charon/Aeneas output
  for nine constructors/accessors in pinned libsignal `ratchet/keys.rs`.
  `Proofs/KeyAccessors.lean` proves the state representation and seven projections
  through the numeric MPC artifact. There are no external function templates.
* `Generated/Clamp` is the actual output for `scalar::clamp_integer` in
  `curve25519-dalek@5.0.0`, selected from libsignal's locked Cargo dependency
  graph. `Proofs/Clamp.lean` proves the complete function, including absence of
  bounds errors for every 32-byte input, and its Boolean/AIG artifact. It does
  not claim to verify libsignal's full private-key deserializer or X25519.
* `Generated/Sha256Round` is the actual scalar round in the locked
  `sha2@0.11.0` wasm32 backend. `Proofs/Sha256Round.lean` proves its full eight-word
  result and numeric-circuit equivalence for every input. The extraction uses
  the supported `wasm32-wasip1` target with SIMD enabled, but the selected
  function itself contains only scalar operations. Wrapping addition and
  rotation use existing Aeneas standard-library models; no opaque crypto body
  or replacement Rust implementation is accepted. This result does not cover
  the compression loop, byte loading, buffering, or full HMAC/HKDF wrappers.
* `Generated/ServiceIdEncode` includes the actual fixed-width service-identifier
  encoder and the real locked `uuid@1.23.4` implementation of `as_bytes`.
  `Proofs/ServiceId.lean` proves all seventeen output bytes and its numeric
  circuit for both identifier kinds and every UUID. The kind uses one secret
  input bit and the UUID uses sixteen secret input bytes. The proof includes
  absence of bounds/length failures; it is not merely a leading-tag theorem.
* The same core extraction and `Generated/MessageType` include the complete
  `ServiceIdKind::try_from` and `CiphertextMessageType::try_from` operations.
  `Proofs/Tag.lean` proves their circuits equal to the actual results for all
  256 byte inputs, including invalid tags and the original byte in the error.
  The two-byte circuit representation (acceptance status, tag) is proved
  injective for these Rust result types. Exhaustive finite proofs run through
  Lean's kernel, without native-checker assumptions.
* `Generated/Padding` is the actual locked `block-padding@0.4.2` PKCS#7
  `raw_pad` operation. `Proofs/Padding.lean` proves its complete translated
  success/failure behavior for every slice and position, then bridges the
  numeric CBC padding circuit for all final-block bytes and tail positions.
  The bridge permits an arbitrary unchanged prefix of full blocks, including
  empty and block-aligned messages. Unused generic trait defaults are excluded
  explicitly; no called computational body is replaced by an opaque stub.
* `Generated/AesSubBytes` is the actual locked `aes@0.9.1` portable software
  S-box and its omitted-NOT correction. `Proofs/AesSubBytes.lean` proves the
  selected composition equal to the MPC S-box for every input word and every
  one of its 64 parallel byte lanes, through numeric artifact semantics.
  Incorrect slice lengths give the translated assertion failure. This is a
  leaf result: the actual AES key schedule moves those four NOTs into round
  keys, so complete cipher correspondence still requires round and wrapper
  composition. The actual full key schedule is proved separately below.

* `Generated/Unpadding` contains the actual locked PKCS#7 unpad function and
  its actual Rust slice-iterator `any` loop. `Proofs/Unpad.lean` proves the
  complete strict result for every sixteen-byte final block, including all
  invalid suffixes, and its numeric MPC encoding. Validity, retained length
  and data are secret outputs; rejection encodes eighteen zero bytes. The
  encoding is proved injective on the translated result. This is a final-block
  operation, not yet the complete CBC decrypt/authentication path.
* `Generated/AesLayout` contains the actual software AES `bitslice`, nested
  `read_reordered` and `delta_swap_2`. `Proofs/AesLayout.lean` proves every
  numeric output bit for all four sixteen-byte inputs and any initial
  eight-word output buffer. `TlsMpc/Signal/AesLayout.lean` implements the proved
  permutation with zero AND gates. The reverse-layout wrapper and round
  composition remain unfinished.
* `Generated/AesMix` and `Generated/AesShift` contain the actual portable
  `mix_columns_0` and all three `shift_rows` operations, including their rotate,
  masked-swap and iterator bodies. `Proofs/AesLinear.lean` and
  `Proofs/AesShift.lean` connect the existing byte-oriented AES operations to
  those translated bitplane operations for all four input blocks. The three
  ShiftRows circuits use only wiring; MixColumns uses 2,176 XOR gates and no
  executed AND gates.
* `Generated/AesMixPhases` and `Proofs/AesMixPhases.lean` cover the remaining
  actual `mix_columns_1/2/3` operations. Their byte circuits implement
  `S^(-k) ∘ MixColumns ∘ S^k`, with the round representation transition proved.
  A direct public-index permutation avoids repeated list construction and is
  proved equal to that composition. Each four-block circuit uses 2,176 XORs
  and zero executed ANDs. Complete cipher composition remains unfinished.
* `Generated/AesInverseWrite` is the unchanged nested `write_reordered`
  operation used by both twelve-byte writes in the actual inverse-layout
  wrapper. `Proofs/AesInverseWrite.lean` proves all twelve output bytes,
  including the four preserved bytes, through a wiring-only numeric circuit.
  Since Charon cannot directly select nested functions, a reviewed declaration
  selection retains this closed builtin-only function without changing it.
  That extra extraction step is trusted and recorded in
  `Extraction/aes-inverse-write-selection/review.json`. The full `inv_bitslice`
  wrapper still encounters unsupported hybrid-array construction and is not
  claimed.

* `Generated/Sha256Compact` is the actual `sha2@0.11.0` portable compact
  compression operation, selected with `sha2_256_backend="soft"` and
  `sha2_backend_soft="compact"`. `Proofs/ShaCompact.lean` proves all sixty-four
  rounds, the rolling message buffer, bounds checks and final feed-forward
  through the numeric artifact for every eight-word state and sixteen-word
  input block. `TlsMpc/Signal/ShaCompact.lean` supplies the proved circuit.
  `Proofs/ShaCompactEquivalence.lean` also proves the existing full-list
  `TlsMpc.Sha256.compress` and its numeric artifact equivalent to this actual
  operation, so the result applies to the compression used in our HMAC path.
  This extraction has one additional trusted preprocessing step: removing two
  unused `Step` dictionary fields that the pinned Aeneas standard model lacks.
  The independently reviewed filter preserves every computational body and
  checks the complete retained semantic graph for references to removed fields.
  It is not a mechanized transformation; the exact diff and provenance are in
  `Extraction/sha256-compact-metadata/review.json`.

`../TlsMpc/Signal/Symmetric.lean` implements HMAC chain derivation and
HKDF-SHA256 `WhisperMessageKeys`, with the 32/32/16-byte split. Its symbolic,
prepared-HMAC and numeric-artifact correctness proofs are checked for all
inputs against the executable Lean definition. **Equivalence of that definition
to libsignal's complete RustCrypto call graph is still unfinished.** The
unsuccessful actual extraction attempts are inventoried in `Extraction/`;
no handwritten Rust replacement or opaque cryptographic model was accepted.

`AesKeyScheduleWork/FullSchedule.lean` proves the complete actual AES-256
software key schedule equal to its numeric circuit for every 32-byte key and
all 120 output words. The actual checked operations, borrow write-back, loops
and final exit are preserved. Its called reverse iterator is retained; a
reviewed trusted preprocessing step removes only unused dictionary metadata.
`AesKeyScheduleWork/schedule-proof-check.json` audits 37 endpoints with only the
three standard Lean axioms and no source substitutions or cryptographic stubs.
The artifact uses 1,664 ANDs and 8,860 XORs with all input/output bits secret.
The separate backend report records five-party MP-SPDZ compilation and public
clear-source checks at batches 1 and 16. Sixteen actual translated fixtures
also check native export. No native MPC execution or throughput is claimed.
This isolated proof package reuses canonical primitive proofs and adds the
complete copy, column, initialization, expansion and finishing composition;
its README lists reproduction commands and the precise trusted selection.

`AesAddRoundKeyWork/` proves the selected actual core u64 XOR-assignment leaf.
The complete AES round-key caller still has an unsupported mutable `Zip`
borrow-write-back translation, and `inv_bitslice` still has its hybrid-array
initialization boundary. These remaining callers and full AES/CBC composition
have not been replaced by handwritten Rust or opaque primitive assumptions.
`AesZipInvestigation/README.md` records exact actual-source reproductions of
the iterator model mismatch and Charon's partial-monomorphization substitution
defect. `AesInverseLayoutWork/wrapper-boundary-report.json` records three
unaccepted full-wrapper profiles, including unchanged-source MIR inlining.
These diagnostics identify tool/library-model work; they add no proof claims.

`ShaWordsWork/` records an unaccepted byte-loading candidate. The complete
`array::from_fn` caller fails translation, and even the isolated conversion
closure inherits an opaque Formatter type from the standard Debug dictionary.
That candidate is excluded from the completed refinement count.

`Sha256WrapperWork/Initial.lean` now connects the actual SHA-256 core
constructor to that accepted compression proof. It preserves all actual
28/32/invalid output-size branches and proves constructor-plus-compression
equals the numeric circuit for every sixteen-word input. Eight endpoints use
only the standard three axioms. `Sha256InitialReview/` independently checks
the three unused ArraySize metadata deletions, unchanged emitted roots and
the complete selected dependency closure. Non-emitted wrapper references
remain explicit exclusions; `Sha256WrapperWork/acceptance.json` accepts only
this constructor/compression result. Actual Digest/update/finalize and
block-buffer equality remain unfinished.

`../TlsMpc/Signal/Cbc.lean` implements the AES-256-CBC sending operation with
PKCS#7 padding, sharing one expanded AES key across the blocks. Its symbolic and
numeric-artifact correctness proofs hold for all inputs against the executable
Lean definition. **The actual RustCrypto AES/CBC composition is still an open
implementation-reference obligation.**

`../TlsMpc/AesInverse.lean` now implements inverse AES-128/256 with reusable
forward expanded keys. Its inverse S-box uses the existing 32-AND circuit and
linear transforms; both byte inverse identities are kernel-checked.
`AesInverseCircuitWork/check-report.json` records 296 OpenSSL/FIPS/public-byte
fixture lanes and 20 audited theorem endpoints. This is an executable Lean
decryption specification with verified circuit lowering; complete equivalence
to the actual RustCrypto decryption wrappers remains pending.

`../TlsMpc/Signal/CbcOpen.lean` decrypts AES-256-CBC blocks and applies the
strict final-block padding circuit. `OpenResult.lean` produces a shared
acceptance byte, eight-byte big-endian retained length and a fixed-size
plaintext buffer. Padding or authentication rejection zeros every output
byte, including the status and length. `MessageMac.lean` implements the pinned
SignalMessage MAC domain: serialized sender identity key, serialized receiver
identity key and message content, with the first eight HMAC-SHA256 bytes kept.
`AesInverseCircuitWork/PaddingBridge.lean` composes the actual Aeneas strict
unpadding result into this receive output for every final block, including
rejection; `LengthEncoding.lean` proves the retained uint64 length is lossless
when the candidate has fewer than 2^64 bytes. Its separate 13-endpoint audit is
`AesInverseCircuitWork/padding-proof-check.json`.

`../TlsMpc/Signal/Receive.lean` composes those operations over one shared
serialized input. MAC content excludes its final eight bytes; the ciphertext
and optional address encoding are selected from that same authenticated
content. It also checks the actual accepted high version nibbles, 3 and 4,
and optional fixed-width sender/recipient address/device matching. The direct
acceptance specification and its numeric-circuit theorem are in
`ReceiveSpec.lean`; `receive-circuit-proof-check.json` audits 33 endpoints with
only the standard foundational axioms.

This receive interface has an explicit bounded-input contract: ciphertext and
optional address offsets, lengths and presence are public profile metadata.
An in-MPC protobuf parser must establish that they denote the actual fields
before this interface can handle arbitrary Signal wire messages. The circuit
does not implement full parsing, ratchet/session transitions, replay handling
or atomic persistent updates. Authentication and padding results remain
secret; the modules contain no reveal operation. Public OpenSSL/HMAC fixtures
and backend compilation are recorded by
`scripts/check_lean_signal_receive.py` in
`benchmarks/results/lean-signal-receive-checks.json`. They do not establish full
RustCrypto wrapper equivalence or networked MPC performance.

`../TlsMpc/Signal/Serialization.lean` now constructs the bounded send content
from shared version, counters, ratchet key, ciphertext, optional PQ bytes and
optional typed addresses. It emits the optional scalar fields even when their
value is zero, omits PQ exactly when empty, and uses the pinned constructor's
version expression `((version & 15) << 4) | 4`. Public counter widths range from
one to five bytes; secret canonical-width checks reject a mismatched profile.
The address-present profile checks both ServiceId kinds and device IDs. The
profile assumes addresses have already been parsed into these typed encodings;
the Rust constructor's fallback for unparseable address names is not implemented
by this profile.

`../TlsMpc/Signal/Send.lean` composes AES-256-CBC encryption, this serialization,
and the eight-byte MAC over the same resulting content. It consumes already
derived message keys and emits shared `status || complete SignalMessage wire`.
Every output byte is zero on a failed counter-width/address check. The
`send-circuit-proof-check.json` audit checks 28 new endpoints, including the
operation-level acceptance specification and numeric compiler equality, with
only the standard foundational axioms. This does not prove equivalence to the
whole actual Rust constructor or implement ratchet state persistence.

The standalone CLI is `lake env lean --run SignalReference/SendExport.lean`.
Its modes are `signal-serialize CT_SIZE PQ_SIZE COUNTER_WIDTH PREVIOUS_WIDTH
none|present` and `signal-send PLAINTEXT_SIZE PQ_SIZE COUNTER_WIDTH
PREVIOUS_WIDTH none|present`. The root `emit_mpc` CLI now exposes the same
modes. Both wrappers use the same proved protocol/compiler modules and an
explicitly unverified JSON transport. Sizes are limited to 1024 bytes per payload. Inputs
start with version(1), counterBE(4), previousBE(4), ratchetRaw(32). Serialization
then takes ciphertext, PQ and addresses(0/36); sending instead takes cipherKey(32),
IV(16), macKey(32), senderIdentityRaw(32), receiverIdentityRaw(32), plaintext,
PQ and addresses(0/36). All these inputs remain secret; lengths, address
presence and encoded counter widths are public.

`scripts/check_lean_signal_send.py --isolated-exporter` passed 33 artifact
profiles and 984 synthetic public fixture lanes. Six selected batch-1/batch-16
MP-SPDZ compilations and clear-source checks passed. The full send profile with
16 plaintext bytes, seven PQ bytes and addresses uses 418,880 ANDs after the
unverified adapter's XOR recovery; this is a circuit count, not a measured
networked rate. `benchmarks/results/lean-signal-send-checks.json` pins the exact
exporter, circuit, adapter, backend and fixture sources. An additional 83
artifact-to-artifact send/receive fixture lanes pass in
`benchmarks/results/lean-signal-roundtrip-checks.json`; generated numeric send
outputs become numeric receive inputs.

`../TlsMpc/Signal/ChainSend.lean` now composes the established-chain step: it
derives the message keys inside the circuit, encrypts and authenticates the
same serialized content, and returns candidate next chain state. Its secret
SPQR-key presence byte must be zero or one; zero selects the HKDF zero salt
inside MPC. Accepted output is `255 || nextChainKey32 || nextCounterBE4 || wire`.
Rejection returns `0 || oldChainKey32 || oldCounterBE4 || zeroWire`, preserving
the supplied state. It rejects the exhausted counter `2^32-1`, invalid presence
bytes and failed serialization profiles. Counter exhaustion is an explicit
bounded-profile policy, not a claimed equivalence for Rust overflow behavior.

The standalone entry point is `lake env lean --run
SignalReference/ChainSendExport.lean signal-chain-send SIZE PQ_SIZE
COUNTER_WIDTH PREVIOUS_WIDTH none|present`. The fixed input prefix is
version(1), counterBE(4), previousBE(4), ratchetRaw(32), chainKey(32),
PQkeyPresent(1), PQkey(32), senderIdentityRaw(32), receiverIdentityRaw(32),
followed by plaintext, PQ message bytes and addresses(0/36). All values are
shared. The same public payload caps, encoded widths and address profiles
apply as for `signal-send`.

`chain-send-proof-check.json` audits 20 endpoints, including exact equality
to the canonical Lean key derivation and the branch-based state/output spec.
The two chain-send artifact profiles pass 56 independent public fixture lanes
and selected MP-SPDZ batch-1/batch-16 compilation plus clear-source checks;
see `../benchmarks/results/lean-signal-chain-send-checks.json`. The larger
profile (17 plaintext bytes, five PQ bytes, typed addresses) uses 1,386,798
ANDs after the unverified adapter's XOR recovery. The SPQR key, flag and
outgoing bytes remain inputs that must come from one future SPQR transition.
Atomic state commitment, rollback protection and proactive refresh are not
implemented by this pure operation. Full actual RustCrypto/ratchet equivalence
and native MPC execution remain unclaimed.

The next SPQR component is `../TlsMpc/Signal/SpqrChain.lean`, matching the
symmetric computation described by the pinned SPQR 1.6.0
`ChainEpochDirection::next_key_internal`: increment the secret uint32 counter,
HKDF-SHA256 with zero salt and `counterBE || "Signal PQ Ratchet V1 Chain Next"`,
and split 64 bytes into next-chain and message keys. It returns shared
`status || nextKey32 || nextCounterBE4 || messageKey32`; exhausted counters
preserve the old key/counter and zero the message key. Twelve compiler/spec
endpoints pass the standard-axiom audit, and 56 independent public fixtures
pass, including consecutive transitions and byte-boundary counter increments.
The artifact uses 493,664 optimized ANDs. The standalone exporter is
`lake env lean --run SignalReference/SpqrChainExport.lean signal-spqr-chain`,
with 32 secret key bytes and four secret big-endian counter bytes. Reports are
`spqr-chain-proof-check.json` and
`../benchmarks/results/lean-signal-spqr-chain-checks.json`.

`../TlsMpc/Signal/SpqrMessage.lean` now implements bounded SPQR V1 message
serialization, including all seven payload kinds and optional chunk data.
Epochs, message indices, chunk indices and payload bytes stay secret; their
encoded widths and chunk presence are public. The serializer preserves the
actual `Ct1Ack(bool)` behavior: kind 4 is emitted without a Boolean byte.
Its 23-endpoint audit and 1,089 fixtures across 21 profiles pass, including
all 256 kind-byte inputs and all ten uint64 epoch widths. The maximum-width
profile uses 416 optimized AND gates (the largest count across tested profiles
is 430). Reports are `spqr-message-proof-check.json`
and `../benchmarks/results/lean-signal-spqr-message-checks.json`.

`../TlsMpc/Signal/SpqrSend.lean` joins both SPQR components to established
Signal sending for an already selected active SPQR epoch. It computes the
SPQR message key, uses that key in Signal message-key derivation, and binds
the emitted SPQR message index to the same incremented counter used by HKDF.
The result is shared `status1 || nextSignalChain32 || nextSignalCounterBE4 ||
nextSPQRChain32 || nextSPQRCounterBE4 || completeSignalWire`. Rejection
preserves both old chain states and zeros the wire; it rejects either exhausted
counter, zero epoch, invalid payload kind, width mismatch or invalid typed
addresses. Twelve compiler/spec endpoints pass with standard axioms only.
The independent fixture suite passes 108 lanes, including eight consecutive
coupled chain advances. The two tested profiles use 1,823,986 and 1,895,705
optimized ANDs; these are compiler counts, not throughput measurements.

The standalone command is `lake env lean --run
SignalReference/SpqrSendExport.lean signal-spqr-send SIZE COUNTER_WIDTH
PREVIOUS_WIDTH EPOCH_WIDTH INDEX_WIDTH CHUNK_INDEX_WIDTH none|present
none|present`, where the final flags select chunk and address presence.
Inputs are version1, Signal counterBE4, previousBE4, ratchet32, Signal chain32,
SPQR chain32, SPQR counterBE4, epochBE8, kind1, optional chunkIndexBE2+chunk32,
sender32, receiver32, plaintext and addresses0/36. Reports are
`spqr-send-proof-check.json` and
`../benchmarks/results/lean-signal-spqr-send-checks.json`.

SPQR chain, serialization and coupled send also pass selected five-party
MP-SPDZ batch-1/batch-16 compilation and public clear-source checks. The
larger coupled send uses 1,895,705 bit triples at batch 1 and 30,331,280 at
batch 16. These checks execute the unverified source adapter on public
fixtures and compile bytecode; they do not execute a network protocol.

The active-epoch composition requires the caller to select the SPQR chain for
`message.epoch - 1` and the outgoing payload from the real SPQR state machine.
It does not implement epoch selection, KEM/chunk state transitions, the
inactive/no-chain branch, persistent state encoding or atomic updates.
Actual HKDF/SPQR/Signal implementation-reference composition and native MPC
execution remain separate obligations. This is not a complete SPQR/session
implementation.

The actual SPQR varint implementation has a separate accepted refinement in
`SpqrReference/`. `uint64_refines_artifact` proves the numeric encoding equals
the actual translated `spqr::encode_varint` for every uint64 input, canonical
public widths 1–10 and an initial buffer with ten bytes of model capacity;
the widened uint32 index operation is also covered. `encode_eq_run` preserves
all actual modeled buffer results without a capacity assumption. The
21-endpoint audit uses only the standard three Lean axioms. Independent
`SpqrVarintReview/` checks the seven reversible dead-metadata edits, both
unchanged computational bodies, all 99 upstream source files and all 87
official standard-model files. `SpqrReference/acceptance.json` records this
precise scope. The full serializer still encounters unresolved RangeFull
dictionary/Vec inlining translation and is not claimed as refined.

`../TlsMpc/Signal/DhRatchet.lean` adds the selected `RootKey::create_chain`
operation: existing X25519 field computation, canonical private conversion,
and HKDF-SHA256 `WhisperRatchet` produce the next root, next chain and counter
zero. All-zero agreement rejects, retains the old root and zeros the chain.
Its 15-endpoint audit includes a field/Boolean composition theorem with the
conversion's exact representation relation stated explicitly. Forty-six
public X25519 cases and 81 KDF/output cases pass, including low-order points,
noncanonical peer encodings, private-key clamping and zero rejection.
The field stage reuses 9,437 nodes/4,589 multiplications; the Boolean stage
uses 554,330 optimized AND gates. `DhRatchetWork/adapter.py` composes shared
registers in one mixed VM and contains no key/status reveal. Its production
conversion implementation is unverified; full actual dalek/RustCrypto
equivalence, fresh-key generation, complete DH-ratchet state transitions and
persistence remain separate. Reproduction and exact boundaries are in
`DhRatchetWork/README.md`.

The DH Boolean stage passes five-party batch-1/batch-16 compilation and
public clear-source checks. The shared-register X25519/conversion/KDF
composition also compiles in one mixed VM, using exact prime 2^255−19 and
the existing checked conversion adapter. It retains all outputs as shares.
Neither native execution nor throughput has been measured.

Actual Prost varint/Vec refinement is now complete for the selected operation
in `ProstEncodingWork/`. `CircuitBridge.uint32_refines_artifact` proves every
numeric output bit equals the bytes appended by actual Prost for every uint32
and canonical public width from one to five. The concrete buffer methods are
the actually extracted Vec override and byte default, using the official
Aeneas Vec model; buffer size must leave room for ten bytes. The generic loop
theorem separately preserves all supplied buffer failures/divergence.
`ProstEncodingWork/check-report.json` audits 35 endpoints and exact Vec dispatch.
`prost-selection-independent-review.json` reviews the reversible metadata-only
selection of the actual generic loop and default byte append. Whole generated
SignalMessage encoding remains a separate pending composition. The subsequent
`SignalMessageWork/UInt32Reference.field_refines_artifact` also covers the two
actual counter field tags and checks, composing their full byte output with
the actual Vec buffer; eight additional endpoints and a separate independent
selection review are recorded in `SignalMessageWork/uint32-proof-check.json`. `SignalMessageWork/`
records extraction of the actual pinned derive-generated `encode_raw`; its
unaccepted profiles retain unresolved or unsupported dependencies, including
the actual slice-buffer advance method. No generated external template is
accepted as an implementation assumption.

The newer generic bytes-field candidate in `SignalMessageWork/BytesFieldWork/`
has nine standard-axiom proof endpoints. Its exact generic operation equation
preserves supplied dictionary errors/divergence, while the artifact theorem
explicitly assumes the concrete payload length/append equations. Those remain
undischarged. Actual Vec append depends on as_slice, reservation and the
slice-buffer methods; no generated external template is imported as a proof
assumption. The helper's isolated exact-pin Aeneas repair for Never-returning
calls passes `TranslatorNeverReview/` engineering review. Its 20-endpoint audit
splits into 14 standard-only endpoints and six actual slice endpoints carrying
the existing noncomputational `Aeneas.Std.core.fmt.Formatter : Type` dependency.
That scope decision remains pending, and neither the candidate binary nor a
custom library model has replaced the accepted toolchain.

`../TlsMpc/Signal/SpqrParse.lean` and `SpqrParseSpec.lean` now parse complete
bounded SPQR V1 messages using shared cursors. The only public parameter is
wire length (0–256 bytes); epoch, index, kind, chunk presence/index and data
remain shared. It checks a nonzero epoch, uint32 message index and uint16 chunk
index, supports all seven payload kinds, and retains noncanonical varints and
trailing extension bytes. The output is 49 secret bytes:
`status || epochBE8 || indexBE4 || kind || hasChunk0/1 || chunkIndexBE2 || chunkData32`.
Every byte is zero on rejection; successful non-chunk messages zero the chunk
fields. `ReadAt.lean` proves fixed-width reads at a shared cursor, including
bounds failure and cursor preservation. The final parser theorem replaces all
shared cursor scans with ordinary Nat-cursor decode/read semantics.

The parser's 36 endpoints use only standard foundational axioms. The checker
`scripts/check_lean_signal_spqr_parse.py --compile-backend` passes 2,443 public
fixtures over 15 capacities, including all 256 version/kind values, all tenth
varint bytes in each field, size boundaries, truncation and trailing data.
Five-party batch-1/batch-16 compilation and clear-source checks cover every
accepted payload kind plus rejection. A 64-byte wire costs 28,777 optimized
ANDs; the 256-byte profile costs 54,559. These are circuit/compiler results,
not native MPC runs or throughput. The isolated exporter is
`lake env lean --run SignalReference/SpqrParseExport.lean signal-spqr-parse SIZE`.

The decoder leaf now has an accepted actual-Rust refinement in
`VarintDecodeWork/`. Its 19-endpoint audit covers every official `Slice U8`
and `Usize` starting offset, exact results/errors/cursors, and both prefix and
shared-offset numeric AIG bridges. `SpqrDecodeReview/` independently reproduces
the proof build and byte-identical Aeneas output, checks all 99 pinned upstream
files and 87 official model files, and accepts this exact leaf scope. No LLBC
preprocessing, source edits or custom models are needed. The whole parser's
Rust refinement remains open: `SpqrPreambleWork/` records the actual
`msg_preamble` extraction reaching complete Charon output but failing in the
accepted Aeneas translator. No patched translator or replacement Rust wrapper
was adopted. V0 negotiation, full Signal protobuf parsing, epoch/KEM/polynomial
chunk transitions and persistent session handling remain separate work.

`../TlsMpc/Signal/SpqrEpoch.lean` now supplies SPQR chain initialization and
next-epoch key material for 32-byte initial/epoch secrets. The two exact HKDF
labels, 96-byte root/A2B/B2A split, secret direction selection and zero counters
follow `Chain::new` and `Chain::add_epoch`. Addition checks the shared proposed
uint64 epoch equals current+1 and rejects exhaustion. Its 113-byte result is
`status || root32 || epochBE8 || sendKey32 || sendCounterBE4 || recvKey32 || recvCounterBE4`.
Failed additions retain the old root and epoch and zero the candidate chain
record; invalid initialization direction zeros all output. The API produces a
candidate epoch record: it does not insert/select/trim retained links or commit
persistent state, and the epoch secret still must come from the KEM transition.

The 20-endpoint epoch audit covers compiler/spec equality and uses only standard
foundational axioms. `scripts/check_lean_signal_spqr_epoch.py --compile-backend`
passes 628 independent public fixtures, both directions, every direction byte,
uint64 boundaries and invalid increments, plus eight successive additions fed
from actual artifact outputs. Both operations compile for five parties at
batches 1 and 16 and pass clear-source fixture checks. Initialization costs
638,783 optimized ANDs; addition costs 755,520. No native MPC run, throughput,
full RustCrypto/SPQR wrapper equality or complete epoch-state transition is
claimed. The isolated modes are `signal-spqr-epoch-new` and
`signal-spqr-epoch-add` in `SpqrEpochExport.lean`.

All key outputs and counters are secret wires. These modules provide no reveal
operation. The chain-send circuit selects the optional SPQR salt inside MPC;
SPQR itself is still an explicit dependency. Complete AES-CBC/HMAC Rust
refinement, full SignalMessage implementation equivalence, general parsing and
atomic session-state updates remain outside the completed derivation and
bounded send/receive circuit components.

The root native exporter now exposes the completed bounded operations:
`signal-serialize`, `signal-send`, `signal-chain-send`, `signal-spqr-chain`,
`signal-spqr-message`, `signal-spqr-send`, `signal-spqr-decode`,
`signal-spqr-decode-at`, `signal-spqr-parse`, `signal-spqr-epoch-new`,
`signal-spqr-epoch-add`, `signal-dh-field` and `signal-dh-ratchet`.
`TlsMpc/Signal/Export.lean` supplies the unverified CLI/JSON dispatch;
`TlsMpc.lean` imports the completed components and `TlsWorkerProcess`.
The root and isolated modes use identical argument profiles described above.
`scripts/check_lean_signal_root_export.py` compares 20 root native exports
against the already checked isolated artifacts: every numeric field, node and
output reference is byte-identical after removing descriptive text. Seven
existing TLS/primitive dispatch profiles and seven rejected invalid Signal
profiles also pass. The report is
`../benchmarks/results/lean-signal-root-export-checks.json`. Root integration
adds no actual-Rust equivalence, native MPC execution or deployment-security
claim.

## Reproduce

`pins.json` fixes libsignal, Aeneas, Charon, the Rust compiler and relevant source
hashes. Aeneas and Charon are matched using that Aeneas revision's `charon-pin`.
The proof package uses Lean 4.31.0 and mathlib 4.31.0 without changing the root
Std-only package. Exact commands and source locations appear in the extraction
inventories.

For an ordinary connected machine, install the pinned Rust nightly with
`rustc-dev` and `llvm-tools`, build the pinned Charon source, install the pinned
Aeneas release, and resolve the isolated Lake package. This workspace keeps all
installed tools in `.deps/`; `extract.py` uses those pinned locations and offline
Cargo resolution. No libsignal Rust source was edited. The local Cargo source
configuration only redirects locked dependencies to verified local archives;
inherited Git-dependency Cargo metadata was expanded for directory vendoring.

From the repository root:

```sh
python3 SignalReference/extract.py key_accessors
python3 SignalReference/extract.py clamp
python3 SignalReference/extract.py sha256_round
python3 SignalReference/extract.py service_id_encode
python3 SignalReference/extract.py message_type
python3 SignalReference/extract.py pkcs7_pad_selected
python3 SignalReference/extract.py aes_sub_bytes
cd SignalReference
lake build
lake env lean Checks.lean
```

For the existing offline dependency cache, the following checks package revisions
and reads the cache without modifying it:

```sh
python3 SignalReference/check.py --packages-dir /path/to/matching/.lake/packages
```

`check.py` verifies pinned source files and generated-file hashes, rejects
incomplete references and placeholders, compiles the Lean modules, and checks
the theorem axiom lists. The only foundational axioms currently reported are
Lean's `propext`, `Classical.choice` and `Quot.sound`; there are no cryptographic
assumptions, generated external axioms or `sorryAx` in these theorems.
It also compares the standard scalar/slice model sources used by the new
padding and AES bridges with the pinned official Aeneas archive. Their discarded
panic-formatting metadata is listed explicitly; the translated failure guards
remain in the functions and are included in the proofs.

The actual extraction toolchain is part of the trusted reference boundary:
Rust/Cargo, Charon and Aeneas are not proved by this project. Aeneas's standard
array/scalar models are also part of that boundary. Proving a circuit equal to
the generated Lean semantics does not independently verify those translators.
JSON transport, native execution and the MPC backend remain unverified as agreed.

`BAF_REVIEW.md` and `Extraction/baf-review.json` audit the Beneficial AI Foundation
repositories at exact commits. Their SPQR source pin matches ours, but extraction
patches and opaque crypto links still need checking. The imported pure
`External/BafRFC5869.lean` specification has a proved bridge to our concrete
HKDF and numeric circuit. It is reusable specification work, not evidence that
RustCrypto equivalence is complete. The user's requested proof target is circuit
equivalence to the faithfully translated implementation, not an independent
protocol-correctness or cryptographic-security proof.

## Export and test

```sh
lake build emit_mpc
.lake/build/bin/emit_mpc signal-derive-keys > signal-keys.json
.lake/build/bin/emit_mpc signal-clamp > signal-clamp.json
python3 scripts/check_lean_signal.py
python3 scripts/check_lean_signal.py --compile-backend
python3 scripts/check_lean_signal_metadata.py
python3 scripts/check_lean_signal_cbc.py
```

`signal-derive-keys` takes 32 chain-key bytes and 32 SPQR-salt bytes and returns
112 secret bytes: next chain key, AES key, MAC key, then IV. Prepared HMAC states
are shared in the Lean implementation; their equivalence to the direct
specification is proved. `signal-clamp` takes and returns exactly 32 bytes and
does not reduce a byte string modulo a field.

The differential check includes the pinned upstream chain-key fixture, independent
HMAC/HKDF fixtures with zero and nonzero salts, and scalar-clamping edge cases.
The optional backend check compiles the generic adapter for five parties at
batches 1 and 16 and interprets it on public synthetic shares. It does not run
a network MPC protocol or measure WAN throughput. See
`../benchmarks/results/lean-signal-checks.json` for the latest actual results.

The general AIG lowering contains 3,144,259 AND nodes for the 112-byte derivation
output. The current generic adapter recognizes XOR patterns and prunes unused
intermediates, leaving 978,359 executed AND gates and 905,340 XOR gates. Clamping
needs zero AND gates. The rewrite traversal remains unverified. These are
correctness prototype costs; they do not establish the requested sending rate.
The earlier adapter's completed batch-one baseline is recorded separately in
`../benchmarks/results/lean-signal-baseline.json`, with its original source hash.

`signal-cbc-encrypt SIZE` takes 32 key bytes, 16 IV bytes and `SIZE` plaintext
bytes. Message length is a public circuit parameter; all input bytes and output
ciphertext remain secret wires. The CBC check passes 27 public fixtures at nine
lengths, including the pinned upstream example, empty input and full-block
padding. It also compiles and checks the generic five-party backend at batches
1 and 16 for plaintext lengths 0, 16 and 64. The first ciphertext block costs
8,832 executed AND gates including the AES-256 key schedule; each further block
adds 7,168. The report is `../benchmarks/results/lean-signal-cbc-checks.json`.
It is fixture/compiler evidence, not a proof against the actual RustCrypto
implementation and not a native MPC run or throughput measurement.

`signal-unpad16` takes sixteen secret final-block bytes and returns eighteen
secret bytes: a 255/0 acceptance mask, the retained length, and sixteen
zero-padded data bytes. It does not open validity or length. The independent
PKCS#7 check passes 440 fixtures, including all 256 terminal-byte values and
all valid padding lengths. Five-party batch 1 and 16 compilation and public
clear checks pass; the circuit uses 1,978 AND and 1,740 XOR gates. See
`../benchmarks/results/lean-signal-unpad-checks.json`. No native MPC execution
or message-level authenticated-release composition is claimed.

The compact compression checker is
`python3 SignalReference/ShaCompactWork/check.py --packages-dir PATH`. It audits
its operation theorem and compares 45 exported public cases with OpenSSL
`SHA256_Transform`, including arbitrary initial states; nine padded cases also
match `hashlib.sha256`. The artifact has 59,759 executed AND and 55,549 XOR gates
with all 768 input bits secret. The full-list compression variant has a separate
all-input equivalence proof; digest buffering, padding and HMAC/HKDF wrappers
remain unproved against their translated implementations. No native MPC execution or
throughput measurement is claimed. See `ShaCompactWork/proof-check.json`.

The ServiceId and tag exports are checked separately in
`../benchmarks/results/lean-signal-metadata-checks.json`. The fixed-width encoder
takes 129 secret input bits (one kind bit and sixteen UUID bytes); both tag
decoders cover every input byte, including rejected values.

## Extraction problems still to solve

The default Aeneas preset reaches generic associated types in
`hybrid-array@0.4.13`, used by `hkdf@0.13.0`, `hmac@0.13.0` and `sha2@0.11.0`.
Charon reports warnings and writes `has_errors: true`; its process can still
return zero, so checking the exit status alone is insufficient. This run has
173 opaque function declarations and 46 opaque types. Aeneas subsequently fails.

Monomorphizing and extracting bodies removes those Charon errors and produces
597 structured function bodies, but also 48 intrinsics, 9 missing bodies and 4
extern functions. Aeneas then reports unsupported pointer/standard-library
representations and `Z.Overflow`. The complete inventories are retained in
`Extraction/symmetric_keys*.json`; these runs are not accepted proof references.

The unprocessed portable compact SHA-256 profile still fails because the pinned
Aeneas release lacks two newer Rust `Step` fields. The reviewed profile now
removes only those unused opaque dictionary entries and proves the complete
selected compression operation. Reproduce it with
`python3 SignalReference/extract.py sha256_compact_reviewed`. The input graph is
pinned in full, allowing only nondeterministic ordering of the diagnostic
`short_names` map. No input or output LLBC field is reordered by that fingerprint
check. The exact seven-slot filtering step and every standard model remain
explicit trusted translation dependencies. Monomorphized alternatives and the
September toolchain failures are retained in `TOOLCHAIN_CANDIDATES.md`.

Actual PKCS#7 iterator extraction requires a full-MIR sysroot built from the
matching official Rust sources with official Miri. Reproduce it with
`python3 SignalReference/PaddingWork/Unpad/build_sysroot.py`, then run
`python3 SignalReference/extract.py pkcs7_unpad_selected`. The accepted profile
checks both source and sysroot artifact hashes against
`Extraction/unpad-sysroot-provenance.json`; no Rust body or MIR is patched. The
exact excluded unused trait methods and standard iterator model boundary are
listed in `Extraction/unpad-review.json`.

The pinned Charon also mishandles declaration ordering for an inherent-method
entry written as `ChainKey::new`. The extractor uses method-name glob patterns
and checks both declaration order and generated definition count. It rejects
empty output even if both tools exit successfully. Extracting a locked registry
dependency requires invalidating its disposable Cargo build cache; otherwise
Cargo can report success without rerunning the extraction driver.

For trait methods, the path resolver and declaration-ordering pass need
different matching patterns. The working profiles use the resolved trait entry
in `--start-from` and a full lexical-name glob in `--start-from-if-exists`.
This retains the actual `try_from` functions without source or translator
patches. Core encoding and kind decoding are exported together because this
Aeneas release otherwise generates colliding discriminant-instance names for
two independent copies of the same type.

The complete fixed-width address decoder has also been attempted. Its generic
and monomorphized exports fail while translating the actual Rust standard
library `Result::ok`, with `There should be no bottoms in the value` at
`core/src/result.rs:714–718`. The successful tag results above do not imply
the surrounding Option/Result parser composition is complete.

Next work is the real RustCrypto dependency boundary, followed by
`protocol.rs::SignalMessage` and `triple_ratchet.rs`, including errors, state
updates and randomness. `obligations.json` records the remaining contracts and
the arithmetic/byte conversion boundaries for the hybrid MPC design.

The deployment also requires proactive security against at most two compromised
nodes per refresh epoch, with different nodes potentially compromised later.
Every retained Signal key, recipient identifier, pending message key and SPQR
state must participate in authenticated refresh and secure erasure. The pure
circuits and current backend checks do not establish that system property.

## General shared-layout receive and bounded state transactions

`ProtoParse.lean` and `ProtoParseProofs.lean` parse all six pinned SignalMessage
protobuf fields with secret offsets and lengths. The public wire capacity is
bounded by512 bytes. Duplicate singular fields replace earlier values, including
empty byte fields; a wrong wire type is still an error. Unknown fields and
matching groups are skipped with Prost's default100-level recursion limit.
Valid uint64 varints truncate to uint32 for counters; uint64 overflow fails.
The ratchet key follows the pinned type5/at-least33-byte rule, including accepted
trailing public-key bytes. Missing required fields, truncated spans, invalid
versions and malformed keys fail closed. Output is90 shared bytes: status,
ratchet32, counter4, previous4, ciphertext offset8/length8, PQ offset8/length8,
address-present1 and address offset8/length8. Offsets refer to the protobuf body.
Rejection zeros the whole output.

The33 compiler/shape/arithmetic theorem endpoints use only standard foundational
axioms. `scripts/check_lean_signal_proto_parse.py` compares1184 concrete cases
with an actual pinned Prost0.14.4 Rust oracle and the Lean implementation; another
1217 lanes exercise the exported64/128-byte numeric AIGs. Five-party batch1/16
backend compilation and clear-source checks pass for both profiles. These are
fixture and compiler checks, not an all-input proof against Prost.

`ProtoReceive.lean` authenticates the exact original wire, selects ciphertext
with secret offsets/length, validates optional addresses, decrypts a fixed
public maximum number of CBC blocks and privately selects the corresponding
strict PKCS7 result. No public layout assertion is supplied. Its11 checked
endpoints and107 fixtures across96/160-byte wire profiles cover successful and
rejected messages. `ChainReceive.lean` adds in-order chain-key derivation,
ratchet/counter matching and candidate state commit;25 fixtures check its96-byte
profile. `SkippedKeys.lean` implements first-match lookup, stable compaction,
newest-first insertion and exact rollback over69-byte seed slots. It has31
checked endpoints,3540 numeric fixture lanes and15 artifact composition steps;
capacity4 consume/insert backend batch1/16 checks pass. `SkippedReceive.lean`
connects that lookup to key derivation and authenticated receive, with24 fixtures
including duplicate bad-first matches and failed-MAC rollback.

`ReceiveAdvance.lean` derives a public bounded number of future chain steps,
selects the shared target counter, inserts intermediate seeds and returns a
candidate next chain/counter/store. Its32 theorem endpoints and1144 numeric
fixtures cover eligibility, uint32 overflow rejection, insertion and rollback.
The pinned policy distinguishes MAX_FORWARD_JUMPS=25000 from
MAX_MESSAGE_KEYS=2000; the current export's public maxJump and capacity are
explicit smaller bounds, not an implementation of the full storage policy.
`BoundedReceive.lean` composes future, in-order and retained skipped-seed paths
with authentication. Its96-byte/maxJump2/capacity4 artifact passes27 independent
fixtures and seven chained deliveries: a future message, skipped delivery,
replay rejection, failed-MAC rollback, successful retry and an older ratchet's
retained key. It rejects unknown ratchet keys without a stored seed; generating
and committing a new DH ratchet remains separate.

Reports are `../benchmarks/results/lean-signal-{proto-parse,proto-receive,
chain-receive,skipped-receive,bounded-receive}-checks.json`, with standalone
SkippedKeys/ReceiveAdvance reports in their work directories. Separate
`*-backend-checks.json` files record completed larger receive backend runs when
available. Backend clear checks reveal only synthetic public fixtures. None of
these reports claims native MPC execution or throughput.

`Pqxdh.lean` implements the pinned FF32/DH1/DH2/DH3/optionalDH4/KyberSS HKDF input
and exact WhisperText label. Its isolated exporter and adapter under
`PqxdhWork` check both KDF profiles and a same-VM three/four-X25519 composition.
The mixed program keeps outputs in secret memory, rejects zero DH agreements
and records the generic compiler's statistical parameter40 explicitly. It does
not claim the separate native worker's128-bit configuration. Kyber production,
prekey/identity/signature validation and complete new-session setup remain open.

## Prost model-extension candidate

`ProtoParseWork/extract.py` extracts unchanged locked Prost sources. The complete
varint decoder's original graph exposes missing Step overflow-method metadata.
`select_step_metadata.py` records a candidate seven-slot reversible removal of
only unused opaque declarations/dictionary fields, checks all remaining
computational bodies are identical, and rejects any remaining semantic reference
to removed methods. This is explicit extra translation trust, not a proof or
accepted reference. The resulting full decoder still has three external bytes
Buf wrappers.

The unrolled `decode_varint_slice` translates without preprocessing or external
templates, but the unchanged official `core.slice.Slice.get_unchecked` wrapper
contains `sorry`, so its original axiom audit includes `sorryAx` and is
quarantined. `ProtoParseWork/ModelCandidate` is an isolated model extension:
its exact diff replaces that wrapper with the existing checked index operation
and proves its valid-usize-index lemma in the kernel. Every affected Aeneas
module is rebuilt; the original model tree and translator are untouched. The
new translation assumption is restricted to valid Rust unsafe usize indexing
agreeing with checked indexing. No claim is made for out-of-bounds Rust UB.
Actual decoder access-bounds/arithmetic bridges and independent acceptance are
tracked separately; this candidate does not yet extend accepted Rust scope.

The remaining full Signal boundary includes new DH-ratchet selection/commit,
SPQR KEM/chunk/epoch-link state, PQXDH/Kyber/XEdDSA/prekeys, legacy expanded-key
records, complete actual RustCrypto/prost wrappers, persistent atomic state,
and deployment refresh/erasure. Secret fields are not opened by these circuits.

## New DH first-message transaction and retained receiver chains

`RatchetStep.lean` now implements both RootKey half-steps in the pinned
`double_ratchet.rs::dh_ratchet_step` order. The receiving root feeds the sending
half; the outgoing previous counter is the old sender index saturating minus
one. Authentication other than255 or either all-zero agreement preserves every
old sender/root byte and clears the receiver candidate. Its9 compiler/rollback
endpoints use only standard foundational axioms;72 public concrete and numeric
fixtures pass, including counter boundaries and zero agreements.

`NewRatchetReceive.lean` connects that candidate to general parsed and
authenticated first-message receive, starting the new receiver at counter zero
and retaining bounded skipped seeds. Failed authentication preserves the old
sender/root state and clears new receiver state/plaintext. Its3 proof endpoints
and26 numeric fixtures pass for jump2, two skipped slots and96 wire bytes;
the artifact executes5,473,355 AND gates. The same-VM adapter in
`NewRatchetReceiveWork/adapter.py` computes the fresh public key and both
agreements using three proved X25519 field DAG evaluations, then feeds the
Boolean artifact without releasing outputs. Five public composition fixtures
exercise15 actual DAG evaluations, including clamping supplied entropy before
persistence. The MPC harness obtains fresh secret entropy from joint daBits;
this is source-level integration, not tested native randomness or network MPC.

`ReceiverStore.lean` implements secret first-match chain lookup, authenticated
replacement, and append/oldest-eviction. Fixed slots are oldest first, initialized
with invalid prefix slots; thus dropping the first physical slot and appending
agrees with growing the logical list until full and then evicting its oldest
entry. The pinned capacity is five receiver chains. Its24 standard-axiom
endpoints,1,728 numeric fixture lanes, and11 artifact transactions pass across
capacities0/1/5, duplicate keys, malformed validity flags and rejected updates.
Actual Rust storage refinement, the retained-versus-new branch composition,
SPQR evolution and atomic persistent commit remain separate obligations.

The actual pinned Prost `decode_varint_slice` leaf is now accepted separately in
`ProtoParseWork/root-review.json`. Its unchanged Charon/Aeneas body is proved for
all inputs satisfying the function's executable assertions: a nonempty slice
and either more than ten bytes or a final byte below128. All ten success lengths
and the exact invalid-varint branch agree with the strict numeric prefix circuit;
every reached unsafe access and scalar arithmetic bound is proved. The audit
has72 endpoints with only standard foundational axioms. Root independently
rebuilt57 affected model modules and checked282 source hashes and identical
object hashes. The explicit extra translation assumption is valid-usize unsafe
indexing agreeing with checked indexing; arbitrary SliceIndex instances and
out-of-bounds Rust UB are outside the accepted statement. The original candidate
manifest flags remain unchanged; the separate root review is the acceptance
record. Whole `decode_varint`, Prost fields/groups, Signal parsing and RustCrypto
wrapper refinement remain distinct obligations.

`RetainedReceive.lean` connects the general shared parser to receiver-chain
selection and authenticated chain/skipped-key updates. Its5 proof endpoints,
37 concrete/numeric fixtures and6 sequential transactions pass with five chains,
four skipped slots, jump2 and96-byte wire. `SessionReceive.lean` adds secret
selection between this path and new-DH receive, committing the sender/root and
receiver stores together as circuit outputs. Its3 compiler endpoints,54 fixture
lanes and5 successive new/retained/replay/failure transactions pass; the checked
five-chain/two-skipped/jump2/96-byte artifact executes7,368,992 AND gates.
The adapter parses the remote key inside MPC before its three X25519 DAG runs.
Six public composition cases exercise18 field DAG evaluations, and54 parser
lanes also match the actual pinned Prost oracle. No branch choice, identifier,
state key, status or plaintext is opened. The40-profile root export audit
includes these modes and preserves7 TLS dispatch checks. All configured jump,
wire and skipped-store bounds remain public and explicit; this does not claim
the full25000-jump/2000-skipped-key profile is practical or exported.

`Keccak.lean` provides the remaining KEM hash component: Keccak-f[1600],
SHA3-256/512 and SHAKE128/256, including multi-block absorption, padding and
squeezing. Its18 standard-axiom endpoints include complete numeric compiler
refinement and exact output length for valid rates.168 concrete fixtures agree
with both hashlib and unchanged pinned `libcrux-sha3@0.0.10`;128 numeric fixture
lanes cover rate boundaries and multi-block SHAKE output. This is a Lean
implementation plus independent Rust differential evidence, not an accepted
Aeneas libcrux refinement. Polynomial arithmetic, sampling, KEM key generation,
encapsulation/decapsulation and the SPQR state machine remain unfinished.

The additional generic MP-SPDZ receive checks completed for general receive
(wire96 and160), in-order chain receive (wire96), and skipped-key receive
(capacity4/wire96), each at batches1 and16 with five parties. Separate
`lean-signal-*-backend-checks.json` reports pin the artifacts, compiler, fixture
harness and bytecode. These are compilation and public-fixture checks; they do
not claim native MPC network execution or deployment security testing.


ML-KEM polynomial implementation now includes canonical arithmetic and CBD/noise
(`MlKemArithmetic`), NTT/inverse/base multiplication (`MlKemNtt`), packed encoding
and rounded compression (`MlKemEncoding`), and bounded secret rejection sampling
(`MlKemSample`). Their separate reports under `benchmarks/results/lean-signal-mlkem-*-checks.json`
record 27, 12, 14 and 16 kernel-audited endpoints respectively; 1,444 arithmetic/noise,
48 transform, 235 encoding, and 4,169 sampling concrete/numeric fixtures passed.
The transform pipeline additionally matches full negacyclic schoolbook multiplication.
The encoding profiles exhaust each scalar domain, and the sampler fixtures include
actual SHAKE prefixes that exhaust the fixed budget. Sampling returns shared status0
and zero coefficients on exhaustion; no secret rejection count is revealed.

`MlKemPke` and `MlKem` compose these components into polynomial key generation,
encryption/decryption, and ML-KEM/Kyber encapsulation with implicit rejection.
Whole-composition numeric-compiler theorems compile. Native differential tests against
pinned libcrux0.0.10 passed36 PKE and36 CCA cases across ML-KEM512/768/1024
and Kyber1024, including12 tampered-ciphertext cases. The24 combined PKE/CCA
proof endpoints use only foundational axioms. Staged numeric-artifact composition
passed all6 ML-KEM1024/Kyber1024 profiles (8 lanes;78–120 component calls each). The oracle's isolated Cargo
manifest removes an unavailable, disabled optional tls_codec dependency; every Rust
source byte remains pinned and unchanged, recorded in
`MlKemPkeWork/Oracle/{manifest-only.diff,source-provenance.json}`. This differential
oracle is not an Aeneas refinement. Full actual-libcrux refinement, typed Signal KEM
wrappers, malformed-key policy and complete PQXDH/SPQR integration remain separate.

The full actual Prost varint wrapper has separate scoped root acceptance in
`ProtoParseWork/FullReferenceWork/root-review.json`. This includes the reviewed
contiguous-slice Buf models and exact unused-Step metadata selection; it does not
accept arbitrary Buf implementations or the whole protobuf parser. The decode_key
wrapper has its own scoped acceptance in `ProtoParseWork/KeyReferenceWork/root-review.json`.
Actual `skip_field` now has its own scoped acceptance in
`ProtoParseWork/SkipTranslatorWork/root-review.json`: every finite recursive
skip-grammar derivation agrees with the actual translated function, including
exact buffer/error/recursion behavior. The three-line translator pass insertion,
capture-free Result::map model and inherited slice models remain explicit trust
boundaries. Its 27 audited endpoints use only foundational axioms. This does not
prove totality or whole-parser agreement.

`ProtoParseWork/SkipPlanWork/proof-report.json` adds 36 kernel-checked endpoints:
existing numeric parser bounds, masks and cursors for fixed32/fixed64, varint and
length-delimited fields inside groups, plus actual skip outcomes and recursion
limit rejection. Group masks, depth/cursor updates, stack lookup/write and the
no-overwrite invariant compile. Closing-tag decisions agree with actual Rust
under decoded-key and stack-content correspondence. Establishing these premises
across the complete decoder table/cursor/scan remains required; this is not an
unconditional whole numeric parser refinement.

Actual uint32 field merging has separate scoped acceptance in
`ProtoParseWork/FieldReferenceWork/uint32-root-review.json`: wire-type-first
rejection, exact varint suffix/error behavior, u32 truncation and duplicate
replacement. Byte-field merging and actual Vec replacement are accepted in
`ProtoParseWork/BytesReferenceWork/root-review.json` for valid contiguous U8
buffers under successful bounded allocation below isize::MAX. Its 92 audited
endpoints (26 new), 20 rebuilt modules and 5,638 pinned native cases pass. Bytes
content and Vec clear/reserve models do not establish allocator failure, generic
Drop, arbitrary Buf, erasure or whole-parser equivalence.

The frozen `ProtoParseWork/TopFieldWork/proof-report.json` adds 38 endpoints for
top-level masks/metadata overwrite, bounded shared decoder-table and payload
window agreement with actual varint/key calls, positive key consumption, and
inactive/failed scan preservation. Root review is pending. Complete logical
field/group trace, cursor/stack invariant preservation, scalar/bytes metadata
composition and successful whole-parser/AIG reference remain outstanding.

Remaining transport composition must follow the pinned client/server evidence in
`../handshake_backend/SIGNAL_SERVER_REVIEW.txt`: current main chat is TLS1.3 with
ALPN h2 at grpc.chat.signal.org. Legacy relay HTTP/1.1 framing cannot silently stand
in for the pinned client transport. Shared Signal ciphertext/identifier operations
here still require the private HTTP/2 request and server-control framing integration.


Signal KEM wire framing (`KemWire`) passed4,608 concrete/numeric cases across
Kyber768, Kyber1024 and ML-KEM1024: all status/type byte values are exercised,
including mismatches and rejection zeroing. Five proof endpoints include the
whole composed compiler theorem. The new KEM-producing PQXDH adapter handles
both initiator and recipient handoffs;12 paired cases and84 numeric X25519 DAG
evaluations pass, with actual numeric wire/KDF stages and a native-Rust fixture
at the KEM boundary. Its identity/prekey validation status remains an explicit
shared input in that adapter. Separately, the six `XEdDsa*` Lean modules now
provide shared decode, field recovery/double-scalar, SHA512, challenge reduction
and binding stages, with a branch-free abstract shared composition. The frozen
`XEdDsaWork/completion.json` records 62 proof endpoints and actual pinned native
oracle agreement; this is not actual Aeneas crypto refinement or native mixed
MPC execution. Root CLI `signal-xeddsa` reproduces all 33 stage artifacts exactly
(`lean-signal-xeddsa-root-export.json`). Private field/Boolean conversion and
production PQXDH wiring remain open.

The frozen `PreKeyWork/completion.json` adds typed EC/KEM/device normalization,
actual required-field/optional-zip policy and ordered trust/two-signature
composition. Its 28 proof endpoints, 9,480 numeric lanes, 36 actual
`process_prekey_bundle` validation-prefix cases and 18 complete numeric
two-signature cases pass. Trust-store results remain external shared inputs;
there are no store writes, native MPC or actual Aeneas prekey claims. XEdDSA
and prekey scoped root reviews are pending.

The root CLI now exposes all completed KEM components. The55-profile exact
numeric comparison is `lean-signal-kem-root-export-checks.json`;10 malformed
public shapes reject. Full KEM execution uses the staged executor rather than
requiring a very large monolithic export. The generic backend completed all8
session/store/Keccak profiles at batches1/16, including117,903,872 triples for
SessionReceive batch16. These are compilation/public-harness results.

The throughput target is 100,000 logical sends/hour (27.78/sec) using a retained
TLS session. The authorized root context completed six native public-fixture
profiles with five malicious-CCD GF128 parties, statistical parameter128 and
live preprocessing. All outputs matched and all parties exited0. At batch16,
17-byte classical sends reached593 recipient encryptions/hour including startup;
coupled SPQR sends reached433/hour and sent667.9 decimal MB per party per
recipient. That SPQR traffic would require148.4 Gbps outgoing per party at the
target before device fanout, TLS or H2. This baseline does not meet the target.
See `lean-signal-native-checks.json`, `lean-signal-throughput-baseline.json`, and
the separate root review `lean-signal-throughput-root-review.json`.

Realistic established SPQR payloads of256 and1024 bytes pass independent
HMAC/OpenSSL fixtures and cost2,184,573 and3,251,891 optimized ANDs respectively.
Those profiles have no native timings yet. Current circuits already reuse
prepared HMAC states within chain derivation and HKDF expansion. The isolated
Tinier128 candidate exposed three 64-bit MAC truncations, repaired by an explicit
field-width-preserving patch with 4,352 local correlation checks. Native input
authentication then advanced, but the first AND failed because upstream shuffle
sacrifice rejects security parameters above 40. No 128-bit Tinier throughput or
production protocol change is claimed; the guard remains intact. See
`TinierWork/security128-assessment.json`.
Per-device fanout, private H2 framing, TLS sealing, new-session/epoch work and
mobile refresh remain additional costs. Compiler VM rounds and runtime
communication counters are not measured WAN round trips. Persistent-runtime
throughput and WAN performance remain unmeasured; the child's own networking
remains denied and only the authorized root context runs native networking.
