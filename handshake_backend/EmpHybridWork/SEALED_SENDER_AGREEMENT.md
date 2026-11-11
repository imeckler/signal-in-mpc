# Sealed-sender key agreement without a per-message ladder

Status: **design; the recommended variant (C) is being implemented. Lean
statements: `TlsMpc/OffsetAgreement.lean` (C) and `TlsMpc/MaskedAgreement.lean`
(A, including the attack on its first form).**

## Why

Every sealed-sender message needs an ephemeral key pair and the agreement
`k·R` with the recipient's identity key R, which is private (it identifies a
contact). Today both come from the shared-scalar Montgomery ladder in the field
engine: 6,348 products per message, about 0.8 GB in malicious mode — 36 % of a
message's bytes after the other optimisations.

Affine coordinates do not improve the ladder itself: a division costs two
products in MPC, an affine x-only step needs two, and a step comes to about 12
products against 11 projective. The saving has to come from avoiding the
ladder.

## Variant A: additive scalar shares and a masked point

`k = kA + kB`, each summand known to one party. The engines open
`Z = R + M_A + M_B` for private mask points; each party multiplies Z by its own
summand locally and supplies the result and a correction; the engines combine
them with a few point additions (about 50 products).

**As first proposed this is insecure against a deviating party.** If A may
choose its mask freely, `M_A = a·B − R′` for a guessed recipient R′ makes the
honest party's contribution computable from A's own values exactly when the
guess is right (`MaskedAgreement.guess_attack`), and the MAC in the opened
envelope then confirms the guess: one guess per message.

Repair: each mask must come with a proof of knowledge of its discrete
logarithm that does not reveal the mask. A cut-and-choose Schnorr proof does
it with point additions inside the engines (about 64 per party per message).
With known logarithms the agreement is terms the deviating party can compute
plus `(kB + c)·R` (`MaskedAgreement.contribution_with_known_logs`), so testing
a guess needs a Diffie–Hellman value. Cost about 950 products per message in
malicious mode, about 50 in semi-honest mode. Fine in the semi-honest model;
more delicate than C in the malicious one.

## Variant B: constant secret increment

Two ladder pairs per conversation, then `k_(m+1) = k_m + t`: one shared-point
addition per message. Successive ephemeral public keys differ by the constant
`t·B`, so the server can link a sender's messages to a recipient. Incrementing
by powers of a fixed secret would hide that under a power-DDH assumption, but
then the private side needs `s^m·R`, a scalar multiplication of a shared point
per message, which is the cost being avoided.

## Variant C (recommended): public offset from a per-conversation key

Once per conversation, inside the engines:

1. R as a shared affine Edwards point, derived from its stored Montgomery
   coordinate by field arithmetic alone (the square root is a power chain).
2. A table of shared multiples `(j·16^w)·R` for every 4-bit window `w` and
   digit `j`, built with point additions only.
3. A secret scalar `k₀ = k_A + k_B`, each summand one party's private input
   (bit-checked): the shared point `k₀·R` is a sum of table entries selected
   by the scalar bits, and `K₀ = k_A·B + k_B·B` is public, its two halves
   exchanged commit-then-open. No ladder is involved.

As implemented, steps 1–3 are one Lean field program
(`TlsMpc/EdwardsAffine.lean`, `prepare`: 11,149 products, once per
conversation) and step 6 below is another (`offsetSum`: 638 products per
message). The offset is written in signed base-16 digits, so the table holds
only the multiples 1–8 for each of 64 windows (512 points, 1,024 shared field
elements per conversation); the program applies the signs. The programs use a division operation that the runtime evaluates by
masked inversion; the C++ (`edwards_points.h`) only supplies inputs, opens the
values the program marks as must-be-zero, and does the public-point arithmetic.
A party that publishes a half of `K₀` inconsistent with its scalar input makes
the recipient unable to decrypt; the agreement inside the engines does not
depend on the published halves.

Measured, whole Signal service run (handshake, upgrade, four sends in two
conversations, warm circuit cache): malicious 4.9 GB Boolean + 2.8 GB field in
56 s (9.6 GB + 5.6 GB with per-message ladders); semi-honest 0.54 GB + 0.40 GB
in 20 s. These are whole-run figures, not per-message ones. A run after the
Lean emitter is rebuilt re-lowers every kernel and takes several minutes
longer.

Per message:

4. The parties jointly sample an offset τ (commit, then open). Both know τ; the
   server does not.
5. Ephemeral public key `K₀ + τ·B`, computed in the clear.
6. Agreement `k₀·R + τ·R`: the engines add the table entries selected by τ's
   digits to `k₀·R` — about 63 shared-point additions — and pass the result's
   u-coordinate to the key derivation.

Properties:

- **Server.** Each public key is `K₀` plus a uniform multiple of B, so the keys
  are independent of each other and of `k₀`
  (`OffsetAgreement.public_key_independent`): statistical unlinkability, no
  extra assumption. τ is drawn from `[0, 2^252)`, statistically close to
  uniform modulo the group order.
- **Parties.** They know τ but not `k₀`. The agreement for a candidate
  recipient differs from something they can compute by `k₀` times the
  candidate (`OffsetAgreement.candidate_needs_initial`), a Diffie–Hellman value
  of the public `K₀`.
- **Deviation.** No party supplies a point, so there is nothing to choose;
  the engines' own guarantees (authenticated shares, checked openings) apply.
  The complete Edwards addition law has no exceptional cases for curve points,
  so the masked inversions inside the additions never open a zero.

Cost: about 570 field products per message with 4-bit windows (63 additions at
about 9 products), about 380 with 6-bit windows and a larger table, against
6,348 today. One-time per conversation: the ladder pair, the lift, and the
table (about 950 shared points for 4-bit windows).

Assumptions not proved in Lean: hardness of Diffie–Hellman; the envelope
revealing only a way to check a candidate agreement (key derivation and MAC as
random oracles); correctness of the point-addition field programs with respect
to the curve's group law; and that R is a point of the prime-order subgroup
(it comes from the conversation's stored state).

## The preparation in constant depth (implemented, `TLS_WORKER_HINTED=1`)

The once-per-conversation program above is 1,289 multiplication levels and 484 openings deep
(the square root is a power chain and the table is 256 successive doublings): over a link
between the nodes that is about 10 s per contact at a 2 ms round trip. `TlsMpc/EdwardsHinted.lean`
(`liftOpen`, `liftPoint`, `prepareHinted`) computes the same table and initial point in about 45
multiplication rounds and 13 openings, for any number of contacts at once (operation 66):
the square root comes from an opened masked value, and the 63 window bases `16^w·R` are entered
by the parties as hints and checked inside the program (each window computes `16·base_w`
itself; `entries_sound`). The products are the same (11,083 against 11,149 per contact), so
what a batch costs is its triples (about 0.75 GB each way per contact in malicious mode), no
longer its rounds. The per-message sum has a division-free form (`offsetSumFast`: 606 products,
17 rounds and one opening, against 638, 23 and 8), and the long-term agreement with the
recipient is summed from the table's entries `2^i·R` (`affineBitSum`) instead of a ladder.
What is opened: `NEEDS_REVIEW.md` section 3b.

## Keeping the table across sessions (proposal; not implemented)

A contact's table (1,024 field elements), its initial point `k₀·R` (2) and the public `K₀` do
not change until its identity key does. Recomputing them at each session costs about 11,000
field triples per contact: 0.75 GB each way, which a 1 Gbit/s link carries in 6 s. Stored, a
contact needs nothing. The contact's stored state is a Boolean-side record sealed by an AES
circuit; putting the table through that circuit would cost millions of AND gates, so the table
has to be stored as field shares. Requirements: neither node alone learns anything; a node
cannot make the session use a different table undetected (or the difference is harmless); a
computation node keeps nothing durable that is useful without the other node and the database
nodes; the contact's blob is at most 64 KiB and is written before each send; the table goes
when the identity key or device list changes.

**Option 1 (recommended if a persistent MAC key is accepted): shares with their MACs.**
- The field engine's MAC key `Δ` becomes a long-lived secret: one scalar on the database nodes,
  of which each computation node is given its additive share at session start
  (`FieldEngine`'s `mac_key_share`, already built and tested by `check_field_import.py`).
- After a contact is prepared, each party tells the other its share of every element and of
  its MAC, each minus a pad (`export_share`; no engine round). The sums are two public vectors,
  `d = x − ρ_A − ρ_B` and `d' = Δ·x − μ_A − μ_B`, where `x` is the table and initial point and
  `ρ`, `μ` are pads each party derives from a key of its own
  (`ρ_A = PRF(κ_A, contact, version)`). `d`, `d'` and `K₀`
  are public and go into the contact's blob beside the sealed record. They are uniform to
  everyone who lacks one of the pads: to the database nodes, and to either computation node.
- At a later session each party imports its share with no interaction (`import_share`):
  A holds `(d + ρ_A, d' + μ_A)`, B holds `(ρ_B, μ_B)`. No rounds, no triples.
- *A malicious node* can change only its own share or MAC share. Then `Δ·x ≠ m`, and the
  engine's MAC check fails at the first opening that depends on the table: the masked
  denominator of the message's agreement, before the agreement reaches the seal circuit. It
  cannot swap in another contact's or an older table either: its half alone breaks the same
  relation. The blob (`d`, `d'`, the sealed record, the version) is one unit that both nodes and
  the database nodes agree on, so the table cannot be newer or older than the record.
- *What a node keeps:* only its pad key `κ`, useless without the blob and the other node. Losing
  it costs a re-preparation.
- *Size:* window 63 needs one entry, not eight (the offset is below 2^252), so 1,012 elements:
  64.8 KiB with both vectors, 65.2 KiB with a one-device record. A contact with a device list
  does not fit and would store the 64 window bases only (8.3 KiB; the multiples are rebuilt in
  about 4,000 products and 12 rounds).
- *Invalidation:* a write after an identity or device-list change (`scratch_commit`) carries no
  table; the next session prepares again.
- *What it changes for a reviewer:* `Δ` outlives a session. The MASCOT MAC check does not open
  `Δ`, and a failed check gives a deviating party no more than one guess at it, but every value
  ever authenticated under `Δ` stays valid, so the argument that a node cannot recombine old
  shares (above: one half alone always breaks the relation) carries all the weight; and three
  database nodes together with one computation node could forge. The worker would also have to
  receive its MAC key share before the field engine starts (today the engine starts first).

**Option 2 (no persistent key): the same public vector `d`, checked by a one-time-key tag.**
Only `d` is stored (32.9 KiB). At a later session each party enters its pad as private inputs
(fresh MACs under the session's key) and the engines recompute `x = d + ρ_A + ρ_B`. A deviating
party can enter another pad, which adds an error it chooses to the table; to detect that, the
blob also carries a masked tag `t = Σ κ_i·x_i + κ₀·u_R` under a key vector `κ` that is the sum of
two more pads, and the load recomputes and compares it (masked difference opened, must be
zero). An error `e ≠ 0` in the table changes the tag by `Σ κ_i·e_i`, uniform to the deviating
party because half of `κ` is the other party's pad. Cost per contact and session: about 1,030
products and 4,100 private inputs in 4 rounds (roughly 100 MB each way) instead of 11,000
products. Nothing persists but pad keys.

**Not chosen: the table as shares on the database nodes.** The nodes would hold 1,026 shared
field elements per contact and hand each computation node additive shares; those arrive without
MACs, so the load needs the same tag as option 2, and the nodes need new write and read rules.
**Not chosen: re-deriving with fewer rounds only.** That is the constant-depth preparation
above: it removes the latency, not the 0.75 GB per contact.

Both options also need: the blob format (`openState`, `sealState` in the controller) to carry
the public vectors; a worker operation to export after preparation and one to import at load;
the write-before-send rule unchanged (the vectors are copied, about 33 or 65 KiB per write
instead of 0.4 KiB).

## Other ladder optimisations considered

- Masked inversion for the final division: already implemented
  (`x25519_fast.h`).
- Conditional swap: the ladder already uses XOR-of-adjacent-bits swap bits and
  two selection products per step, not four.
- Restructuring a step to fewer communication rounds: reduces latency on a
  WAN (the ladder is about a thousand rounds deep), not the number of
  products. Worth doing when latency is measured.
