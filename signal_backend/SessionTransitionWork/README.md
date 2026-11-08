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
agreement. Actual Rust/Aeneas full source refinement remains open.

This is candidate derivation, **not authenticated message acceptance**. Native
adapter has no commit/open/import/RPC API. The next composition must derive this
key from the actual SignalMessage PQ field, compute fresh joint DH keypair and
both agreements, authenticate/decrypt the original Signal bytes, and only then
commit root/private/receiver/PQ state together. Rejection preserves all old state.

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
