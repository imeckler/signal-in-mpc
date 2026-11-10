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
(`TlsMpc/EdwardsAffine.lean`, `prepare`: 15,051 products, once per
conversation) and step 6 below is another (`offsetSum`: 565 products per
message). The programs use a division operation that the runtime evaluates by
masked inversion; the C++ (`edwards_points.h`) only supplies inputs, opens the
values the program marks as must-be-zero, and does the public-point arithmetic.
A party that publishes a half of `K₀` inconsistent with its scalar input makes
the recipient unable to decrypt; the agreement inside the engines does not
depend on the published halves.

Measured, whole Signal service run (handshake, upgrade, four sends in two
conversations): malicious 5.1 GB Boolean + 3.4 GB field in 53 s (9.6 GB +
5.6 GB with per-message ladders); semi-honest 0.56 GB + 0.49 GB in 20 s.

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

## Other ladder optimisations considered

- Masked inversion for the final division: already implemented
  (`x25519_fast.h`).
- Conditional swap: the ladder already uses XOR-of-adjacent-bits swap bits and
  two selection products per step, not four.
- Restructuring a step to fewer communication rounds: reduces latency on a
  WAN (the ladder is about a thousand rounds deep), not the number of
  products. Worth doing when latency is measured.
