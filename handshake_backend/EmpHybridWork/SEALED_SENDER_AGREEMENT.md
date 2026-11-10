# Proposal: sealed-sender key agreement without a ladder

Status: **design for review, not implemented.**

## Why

Every sealed-sender message needs an ephemeral key pair and the agreement
`k·R` with the recipient's identity key R, which is private (it identifies a
contact). Today both are computed by the shared-scalar Montgomery ladder in
the field engine: 2 × 2,794 products plus bit-share setup, 6,348 products per
message, about 0.8 GB in malicious mode — 28 % of a message's bytes.

A ladder step costs 11 products in projective coordinates. Affine coordinates
do not improve the ladder itself: a division costs two products in MPC (mask,
open, multiply), an affine x-only step needs two divisions, and the total comes
to about 12. The saving comes from avoiding the ladder.

## Construction

The ephemeral scalar only has to be uniform and unknown to each party. Share it
additively, `k = kA + kB`, each summand known to one party (as in the TLS
handshake's split agreement). Hold R as a shared affine point.

Per conversation, once:

1. Lift R from its Montgomery u-coordinate to a full point: one masked square
   root (open `a·r²` for a random shared r, take the public root, divide by r)
   and one division; a handful of products.

Per message:

2. **Public key.** `K_A = kA·B` and `K_B = kB·B` are published with
   commit-then-open; the ephemeral public key is `K_A + K_B`, computed in the
   clear.
3. **Mask.** Each party picks a fresh scalar `mA`, `mB` and inputs the point
   `M_A = mA·B`, `M_B = mB·B` privately. The engines compute `R + M_A + M_B`
   (two affine additions) and open it to both parties. Party A sees
   `R + M_B` shifted by a point it knows, and `M_B` is uniform and unknown to
   it, so R stays hidden; symmetrically for B.
4. **Local multiplications.** With `Z = R + M_A + M_B` now known to both, A
   computes `U_A = kA·Z` and `C_A = (kA·mA)·B + mA·K_B`; B computes
   `U_B = kB·Z` and `C_B = (kB·mB)·B + mB·K_A`. Each inputs its two points
   privately.
5. **Combine.** `k·R = U_A + U_B − C_A − C_B`, because
   `C_A + C_B = (kA + kB)·(mA + mB)·B = k·(M_A + M_B)`. Three affine additions
   in the engines; the result's u-coordinate goes to the key derivation as
   today.

Cost: about five affine point additions (a division and two or three products
each) plus on-curve checks of the six input points — on the order of 50 field
products per message instead of 6,348. The ephemeral scalar remains fresh and
independent for every message, so the Signal server sees nothing it does not
see today.

## What a deviating party can do (sketch, to be reviewed)

- **Learn R from step 3?** It sees `R + M_other`, uniform and independent of R.
- **Wrong `U`, `C`, `K` or `M`.** The agreement becomes `k·R + Δ` for an offset
  the deviating party influences. The envelope is then encrypted under keys
  the recipient cannot derive: the message is undeliverable, which either
  party can already cause.
- **Test a guess R′ for the recipient using the opened envelope?** That needs
  `k·R′ (+Δ)`, i.e. the other party's `k_other·R′`, from the public
  `K_other = k_other·B` and R′: a computational Diffie–Hellman problem. This is
  the same assumption under which the opened envelope hides the recipient from
  the Signal server.
- **Choose `K_A` after seeing `K_B`** (to know the joint scalar): prevented by
  commit-then-open.

Open points: a careful simulation argument for the malicious case, including
the interaction between a chosen `M` and the opened `Z`; whether inputs must be
proved to lie in the prime-order subgroup rather than only on the curve; and
the long-term agreement `id·R`, which stays on the ladder (once per
conversation) unless identity keys are provisioned as additive shares.

## Other ladder optimisations considered

- Masked inversion for the final division: already implemented
  (`x25519_fast.h`).
- Conditional swap: the ladder already uses XOR-of-adjacent-bits swap bits and
  two selection products per step, not four.
- Restructuring a step to fewer communication rounds: reduces latency on a
  WAN (the ladder is about a thousand rounds deep), not the number of
  products, so it does not change the byte counts. Worth doing when latency is
  measured.
