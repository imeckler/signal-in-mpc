# Session transition dependency and ownership map

This is a focused callable-path inventory, not a new acceptance audit. Target:
libsignal904c8dc/v0.106.1 and its locked SPQRv1.6.0/06959b47 dependency. Relay
notify.rs is a historical behavioral reference; deployed compatibility is separate.

| Operation | Existing implementation | Missing system binding |
|---|---|---|
| Established send | Native VariableService + normal private provider; selected Signal/PQ chain/index and request-ID progression | Store lacks root, own DH private/public pair, receiving chains, complete SPQR/KEM state; cannot initialize or rotate sessions |
| Root/DH ratchet | DhRatchet/RatchetStep/NewRatchetReceive/SessionReceive Lean/compiler endpoints | Supplied DH agreements/fresh keypair and receiving PQ key are still external composition boundaries; no native computed-DH/authenticated transition/store commit |
| Active receiving PQ chain | New ActiveSpqrReceive actually parses bounded private-length wire and derives next receiving key | Candidate must be gated by actual Signal MAC/decrypt before any retained state is committed |
| PQ epoch | SpqrEpoch HKDF new/add circuits | Genuine epoch secret must come from full SPQR KEM/chunk/authenticator phase machine; caller-supplied secret is not a replacement |
| KEM | MlKem/KemWire modeled keygen/encap/decap with compiler endpoints | Bounded sampler/entropy, pinned algorithm/profile choice, SPQR incremental libcrux header/polynomial/chunk state and native full-state integration |
| PQXDH | Pqxdh KDF composition | Actual computed DH/KEM binding, authenticated identities/prekeys, fresh entropy, initialization of both DR and full SPQR state |
| Prekey | Frozen PreKey/XEdDSA decoder/constructor/validation/reference candidates | Full actual verifier/to_edwards and process_prekey_bundle/store refinement remain separate; do not treat supplied EC/PQ verification flags as bootstrap |
| Persistence | O_EXCL/fsync immutable attempt fence and selected-state commit before output | Recoverable authenticated per-party shares, full-state schema, globally consistent commit/attempt IDs, rollback detection and outbox/response policy |

Signal worker owns the new receive/DH/SPQR/bootstrap and share-state integration
modules. TLS worker owns opaque transport/provider admission/mux, authenticated
response correlation and runtime retirement. Parser worker owns actual response
parser refinement. Existing frozen references are not edited by this checkpoint.

## Implemented first receive dependency

`ActiveSpqrReceive.prepare` input79 bytes is retained wireEpochBE8, receiving
chain32, receiving counterBE4, and private wire(validity8/BE16length/capacity32).
Output77 bytes is computed status, selected epoch8/chain32/counter4, messageKey32.
All contents remain shares. It requires V1 kind0, same selected epoch, exactly
next index and private cursor end<=actual private wire length. A truncated prefix
cannot use zero padding as a missing kind/varint. Noncanonical varints and trailing
bytes accepted by pinned SPQR remain supported in this bounded domain.

The conservative retained-counter bound is <2^31-1. This keeps actual SPQR's
`ctr + max_ooo_keys` arithmetic within its documented hax resource precondition;
near-u32MAX actual debug SPQR panics at chain.rs266. Our profile rejects instead,
preserving old state and zeroing the candidate key. This is not full error
refinement outside the supported domain. KEM/chunks/acks, epoch changes,
skipped/old receiving keys and negotiating states are rejected/unsupported.

The oracle constructs a disposable selected-established V1 KeysUnsampled phase,
then invokes actual locked `spqr::recv`; no final message key is supplied.
39 accepted cases match exact next chain/counter/key, including127/128, large
epochs, noncanonical varints and ignored trailing bytes.20 rejection cases cover
private status, truncation, length overflow, kind/epoch/index mismatch and counter
profile exhaustion. Six foundation-only endpoints prove Hom/numeric compiler
agreement. The five-party threshold2 native fixture passes two receives across
126→127→128 and a truncated-wire rejection, feeding returned receiving shares
into the next call. It opens only secure comparison bits against independent
public oracle constants, never key/state shares.58.307s includes startup, three
candidate operations and three comparisons; it is not service throughput. Actual Rust/Aeneas full source refinement remains open.

This is candidate derivation, **not authenticated message acceptance**. Native
adapter has no commit/open/import/RPC API. The next composition must derive this
key from the actual SignalMessage PQ field, compute fresh joint DH keypair and
both agreements, authenticate/decrypt the original Signal bytes, and only then
commit root/private/receiver/PQ state together. Rejection preserves all old state.

The native `NativeComputedDh` internal stage takes old own-DH private32 and the
actual parsed remote point32. It generates a joint shared fresh scalar, retains
its clamped32-byte representation, and computes the matching public key and both
receive/send agreements with the existing X25519 field artifact. Its512→1024-bit
manifest is `.deps/private-dh-receive-native/dh.manifest`. It does not accept
supplied agreements or open any field/key; it has no RPC or commit API. Mixed
field/byte conversion and runtime/randomness remain existing unverified backend
boundaries; this is not a new actual-source cryptographic refinement claim.

The new private-length parser dependency is owned by the parser worker:
`PrivateProtoParseV1` cap256, shared BE16 true entire Signal wire length and
upstream computed validity. It must prevent suffix decoders from borrowing
capacity bytes, validate dynamic field ends and keep body-relative PQ offsets.
Its take-n semantic/circuit theorem is pending. The composed receive transaction
must authenticate the original private prefix/MAC and bind this exact parsed
point/PQ field into both native candidate stages before atomic state selection.

## Recoverable share-state design coordination

Do not extend the80-byte sender selection into an alleged durable session store.
A recoverable record must include identity shares, root/DH private/public shares,
both active/retained receiving chains/skipped keys, full SPQR phase/KEM secrets,
registration/prekey origin, counters, outbox and committed response policy.
Per-party snapshots may serialize only that party's own shares into authenticated
local encrypted storage; there is no reconstruction or public share-import RPC.
The snapshot's schema/profile/version and opaque conversation/epoch/attempt IDs
must be authenticated with its contents.

Local AEAD/fsync alone does not prevent rollback or globally inconsistent recovery.
Before implementing recovery, select an authenticated monotonic global commit
witness/linearizable log and authenticated per-party storage/key admission model.
An untrusted host may not relabel an old snapshot under a new fence slot. Reserve
an attempt durably before evaluation; persist selected next state/outbox on all
required participants; obtain one consistent commit certificate before release;
recovery admits only the same certified epoch/attempt and never retries consumed
chain/nonce state. Unknown outcomes remain pending/poisoned, never rolled back.

Byzantine durability is not established by a3-of5 signature quorum (two quorums
can intersect only in corrupt parties at t=2). Availability/consensus assumptions,
certificate quorum, anti-rollback witness and recovery key lifecycle must be
specified explicitly. Current no-MAC runtime and embedding authentication are
separate trust boundaries. Until that protocol is implemented and tested, restart
refusal stays a temporary fail-closed boundary, not recoverable database support.

## Parse-once new-DH candidate composition

`NativeNewDhReceive::evaluate` is an internal848B→608B bounded transaction,
using `programs/signal_private_new_dh_receive.mpc`. The old525B state and identity
public keys remain shares. A single actual private parser summary supplies the
remote point, field offsets and acceptance mask. The program jointly generates a
clamped own-DH private scalar, derives its public key, and computes both agreement
values using that same parsed remote point. It feeds those values directly into
the split receive transaction; no supplied-DH input or raw-DH RPC is admitted.

The C++ adapter compile/link probe passes. The emitted summary/crypto stages have
separate all-output public differentials and exact inverse/composition theorems.
A native compile receipt is distinct from execution: no actual native two-way
receive/reply interoperability result exists yet. The next test must keep the
fresh own private key/root as shares across a reply and second actual peer DH
transition, so simply opening a predicted fresh key is not sufficient evidence.
Actual full RustCrypto/session-source refinement, fresh authenticated bootstrap,
full SPQR KEM phases, retained/skipped receiving paths and durable recovery remain
open. The production provider does not admit this candidate.

`new_dh_native_check.py` is a separate public-fixture harness. Its C++ binary
compiles/links, but its build receipt intentionally records **no native execution**
until the actual runner completes. The planned positive comparison checks status,
receiving slots/PQ and private plaintext against actual libsignal; it omits the
fresh136B sender/root region entirely. The planned bad-MAC comparison checks all
608B against unchanged old state plus zero plaintext. Only two equality bits would
be opened. This narrower first test will not establish retained fresh-private
correctness across a reply; the stateful peer preflight prepares that next test.

### Current native build blocker

The monolithic entry's compiler timed out after900seconds, with its last progress
line at9,200,000 compiler lines. It produced no bytecode or manifest. The compiler
was killed/reaped and a process inventory found no remaining receive compiler or
fixture processes. `receive-compile-report.json` records this **failed** attempt,
source/artifact/log hashes and cleanup; no native receive test was launched.

The next build should split the proven parser-summary and crypto-summary into
separate pinned VM entries around the existing computed-DH entry. All intermediate
summaries/scalars/agreements must remain move-owned shared Bits, and the C++ binding
must use the same actual parser result for both DHs and the crypto summary. This
preserves one parser and one crypto computation while bounding compiler closures.
The public model peer preflight and C++ fixture build results remain valid; they
are not evidence that the failed monolithic native build executed.
