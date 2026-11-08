# Candidate recovery protocol: five members, t=2, abort permitted

This is a proposed protocol with an incremental implementation, not a secure
restore admission or full recovery claim. Existing immutable burn fences remain
until encrypted full-state snapshots, runtime re-admission and protocol wiring
are implemented. No external witness is silently assumed.

## Evidence and assumptions

Malkhi–Reiter distinguish consistency from availability: signed self-verifying
values still require an honest quorum intersection; their full dissemination
construction also requires an available quorum despite the fault set. We use the
honest-intersection condition, not their availability guarantee. Two4of5 signer
sets intersect in at least3 members, exceedingt2. Two3of5 sets may intersect only
in one corrupt member. Two withholding members can prevent4signatures, and this
protocol then aborts. This arithmetic is our inference, not a claim of implementing
a live asynchronous BFT replication algorithm. [Primary paper, §5.1](https://users.ece.cmu.edu/~reiter/papers/1998/DC.pdf).

Assume at most2 faulty member identities per signing-key epoch, authentic fixed
member public keys/genesis, unforgeable domain-separated signatures, collision
resistant hashes, and honest members' durable no-double-sign journals. A corrupt
journal/disk rollback counts as a faulty member. Rotating membership/keys needs a
certified joint epoch transition; it is not implemented. Rolling back3or more
honest durability roots together is outside this model and cannot be detected
from the same rolled-back state alone. Supporting that case needs an independent
anchor/hardware monotonic state chosen explicitly by the user.

SQLite's atomic-commit description emphasizes durable journal flushes before
changing committed data. We likewise require successful file+directory flushes;
we do not assume writes are power-loss atomic. A torn/invalid journal fails closed.
Filesystem/controller behavior remains a platform assumption. [Official implementation documentation](https://www.sqlite.org/atomiccommit.html).

## Private data and phase order

Every node stores only its own encrypted share bundle. The bundle must contain
FULL Signal state (identity/root/own ratchet, all retained/skipped receiving
chains, complete SPQR negotiation/KEM/chunk/epoch state), private input intent,
immutable final outbox, allocator/attempt state and representation/authentication
metadata. The current525B selected receive state is not full Signal state.
Only opaque public context/epoch/attempt IDs, pinned manifests/schema hashes,
ciphertext digests and member signatures appear in agreement evidence. No UUID,
key, private request ID, plaintext or aggregate share is opened by this protocol.

1. Persist the complete private intent and pre-state share bundles on all nodes.
   Freeze builder output, timestamp, recipient/request data and request-ID
   reservation. Obtain a4of5 reservation certificate before consuming a key.
   Honest participants durably record their reservation before returning a vote.
2. Run the pinned private transition using exactly that frozen intent/pre-state.
   A restart can only resume that same intent; it cannot substitute a new message
   under the old counter. Different fresh ephemeral randomness may create a new
   candidate, but no candidate is released without the unique commit certificate.
3. Persist complete selected post-state and immutable outbox share bundles. Each
   member checks its own durable ciphertext against its proposed digest and binds
   the same MPC execution/intent/parent/manifest. All5 prepared snapshot receipts
   are needed while the runtime still requires all5 state owners; missing data can
   abort. These receipts do not themselves certify polynomial consistency.
4. Obtain4distinct commit signatures. An honest member durably records at most
   one commit digest for a given context/epoch/slot before signing. Persist the
   certificate before any outbox becomes eligible for transport. Two conflicting
   commit certificates would require an honest member to double-sign.
5. Mark delivery only from authenticated correlated response policy. Lost/negative
   responses never roll back consumed Signal state. The immutable pending outbox
   remains; retransmission/duplicate-delivery policy is separate from key reuse.

Reservations/commits/acknowledgements have separate signature domains. A recovery
query includes a fresh challenge and obtains4signed responses covering BOTH the
last certified head and every higher reservation/vote. A committed signer set
intersects the response set honestly. Any higher unresolved evidence blocks
restoring an older state; recover its exact certificate/bundles or abort. A hidden
certificate or coordinator crash never permits forgetting a vote. Reissuing the
SAME durable vote is idempotent. Phase-chain/certificate validation must precede
resume; a bare latest-file timestamp is not evidence.

## Fresh runtime re-admission: REQUIRED, not implemented

File signatures/hashes do not show that local share values form one polynomial
or carry valid MACs. The embedding Bits factory is not a secure restore path.
Bind share field/modulus/polynomial, evaluation indices, degree, byte/bit order,
party IDs, backend/profile, schema and sharing/MAC-key epoch in the snapshots.
Do not copy old authenticated shares under a fresh MAC key.

A candidate private import inputs each stored local evaluation INSIDE a fresh
actively secure MPC. Check the5 evaluations lie on one degree≤2 polynomial and
that each decoded bit is Boolean, then produce fresh sharing/authentication.
No constant term or key is opened to a host. Three honest fixed evaluations
uniquely determine the polynomial; thus2faulty inputs cannot change its value and
pass exact consistency. This follows from interpolation, not from quorum votes.
[Shamir's primary paper, §2](https://people.cs.pitt.edu/~litman/courses/cs2001/lectures/lecture-02-p612-shamir.pdf).
The concrete field checks, authenticated private-input binding, fresh backend
import/re-sharing, malformed-share abort and MAC-state migration remain explicit
bootstrap dependencies. This reasoning assumes the fresh MPC itself is secure;
existing functional backend tests do not establish the security of that new import.
The current configured StrongShamirShare selects MaliciousShamir/MaliciousCCD
protocols; their concrete import/configuration still needs review, rather than
being relabeled passive or assumed correct from an embedding factory.

Restart ALWAYS creates a fresh TLS connection/handshake/runtime transport state.
Never restore TLS traffic keys/nonces, record sequence numbers or opaque handles
as if the old peer connection remained live. Signal snapshots/outbox survive;
transport state does not.

## Current implementation boundary

The first component implements actual member signatures, distinct4of5 certificate
verification and durable public no-double-sign evidence across process restart.
It is a control-plane candidate only. It does not admit a snapshot, validate
share consistency, enforce all phase transitions or restore a Signal provider.
Encrypted share serialization, full-state schema, private import and complete
reservation/commit/recovery transport remain necessary before replacing fences.
