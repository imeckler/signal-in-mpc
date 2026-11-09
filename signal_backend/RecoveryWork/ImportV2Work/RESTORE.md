# Partial shared-session restart checkpoint

The fresh-process positive fixture passes on all five parties:102.860s including
startup, checked import, one continued service evaluation and teardown. It uses
the actual encrypted local evaluations produced by the prior two-send MPC run.
The actual Rust recipient decrypts the third output, and aggregate equality
checks compare both restored and newly updated canonical/selected/service state.
No state, private key, root, DH or identifier share is reconstructed. Disposable
final application wires, known-fixture validity/equality and public diagnostics
are the only opened results.

The exact packet is63896 original wire bits /7987 bytes, each stored as one128-bit
local GF evaluation:

-5550-byte canonical capacity snapshot: bounded current SessionRecord fields,
 five receiver-chain slots without skipped message keys, pending-prekey fields,
 bounded Kyber pending ciphertext, active PQ link plus bounded opaque inner
 state, two opaque previous-session slots and Tahini bookkeeping. See the
 authenticated V1 schema; PQ epochs in this schema are32-bit bounded values.
-525-byte selected state: root/own ratchet private+public/sender chain and
 counters136, five receiver slots345, receive PQ epoch/key/counter44.
-611-byte service view: sender identity private32, certificate260, supported
 no-chunk body262 and recipient/access/timestamp/request/device metadata57.
-1293-byte prior typed outbox: validity8, private BE16 length and public frame
 capacity1290, followed by its separate8-byte shared request ID.

The snapshot uses the unchanged CCD128/GF128/t2/n5/x1..5 representation. Every bit
is imported through full-field masked private input, polynomial/bitness checks
and fresh sharing; no bit-only masking or host interpolation is used. The helper
is scoped and destroyed while its borrowed Player still lives. Its completed
ErasedHostCall precedes a separate initialized-VM epoch retirement and completed
host barrier. The pinned private coherence guard initializes the VM and checks
record/selected/service consistency; it is not an empty retirement bypass.

The isolated ExceptionWork runtime supplies constructor-safe prep owners and
leaf cleanup. Allocation wiping is additionally tested against both legacy and
exception runtimes (nine public local checks each). The test records helper
completion, both host barriers, successful socket/thread-owner closure and39
stack-wipe observations per positive party. These observations do not prove
complete OS/crash/swap erasure. No runtime is promoted to the normal profile.

The continued transaction retains the old immutable outbox, writes/read-checks
its own encrypted local evaluations, and appends the new outbox in the new
commit. Its public sharing-epoch tag is freshly jointly generated. The new
partial commit contains9288 logical bytes. It replaces the whole canonical and
selected/service views; it is not a stale record plus an overlay.

Six focused negative modes pass (30 party exits): one/two altered contributions,
non-bit constant, cancellation after helper construction, inconsistent selected
state and AEAD failure before import. Helper failures clear fresh accumulated
shares and quarantine ownership. Semantic failure yields computed validity0 and
never invokes the producer. AEAD failure reaches collective readiness and never
constructs the helper. Per-case receipts distinguish which barriers were reached.

The first launch lacked fixture SSL PEMs and exited before archive import. Its
separate rejection receipt is a setup failure, not an import or cleanup test.
Copied public-test credentials are hash-pinned; the recorded verification was
post-launch and is labeled accordingly. Later setup should pin them before
launch.

**This is not whole-account or certified recovery.** Missing: complete account
credentials/registration/prekey stores/global allocator and conversation schema,
real quorum/current-head/fresh-status authorization, anti-rollback protocol,
normal provider/fresh TLS activation, authenticated pending-outbox disposition
and retry policy. The continuation uses an explicit synthetic component ACK
policy; it makes no exactly-once claim. It preserves an old pending outbox but
does not implement the real response policy. No TLS keys/nonces are restored.
Full fresh-session/PQXDH/SPQR epochs/skipped-key transitions and actual-source
refinement remain required. Normal account recovery admission stays closed.
