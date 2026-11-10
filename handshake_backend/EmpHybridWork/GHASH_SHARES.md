# Proposal: AES-GCM tags from local GHASH shares

Status: **implemented** for request sealing (`signal-request-ctr`) and for
opening application records (`tls-open-application-ctr`); other seals (upgrade
request, pongs, control records, the private-receive profile) still compute the
tag in the engines. Kernels in `TlsMpc/HybridKernels.lean`, local arithmetic in
`gcm_shares.h`, security theorems in `TlsMpc/GhashShares.lean`. Both security
modes pass end to end against the fixture server (whose TLS stack verifies the
tags) with the libsignal recipient. Even powers are obtained by squaring
shares locally, which relies on commutativity of the field multiplication
(assumed, `GhashShares.Laws`). Measured: request seal 1.41 M → 0.32 M ANDs,
response record opens 0.29 M → 0.12 M, plus ≈ 0.55 M once per traffic key.
The remainder of this note is the design as reviewed.

## Why

Sealing or opening a TLS record in the engines costs about 22 k AND gates per
16-byte block: about 5 k for AES and about 16.4 k for one GF(2^128)
multiplication of the running GHASH value by the secret key H (128 × 128 ANDs,
`TlsMpc/Ghash.lean`). The tag is therefore about three quarters of every record:
≈ 1.05 M of the 1.41 M gates for a 1,260-byte request, on every message.

GHASH is linear in the powers of H once the ciphertext is public, and TLS
ciphertext is public by definition. The standard two-party-TLS technique
(DECO, TLSNotary) uses this: give each party an XOR share of every needed
power of H, let each party evaluate its half of the tag polynomial locally,
and combine the halves inside the engines.

## Construction

For one traffic key K (one direction, until the next KeyUpdate):

1. **Shares of H.** The engines compute H = AES_K(0^128) and open H ⊕ r to
   party B only, where r is a private random input of party A. A holds
   H_A = r, B holds H_B = H ⊕ r.
2. **Shares of the powers H^1 … H^n** (n = number of 16-byte blocks of the
   largest record, plus AAD and length blocks).
   - Squaring is linear over GF(2): (H_A ⊕ H_B)^2 = H_A^2 ⊕ H_B^2, so every
     even power's shares come from local squarings.
   - Each odd power H^(2k+1) = H^(2k) · H needs one multiplication of two
     shared field elements. It is done in the engines (one GF(2^128)
     multiplication, ≈ 16.4 k ANDs) and re-shared the same way as H. About n/2
     multiplications, **once per key**, computed lazily up to the largest
     record size actually used.
3. **Sealing a record.** The engines compute the ciphertext C = P ⊕ AES-CTR
   keystream and the pad E = AES_K(J0). C is opened (it is the public
   output). Each party X computes locally
   T_X = Σ_i block_i · H_X^(m+1−i) over the AAD, ciphertext and length
   blocks, and supplies T_X as a private 128-bit input. The engines open
   tag = T_A ⊕ T_B ⊕ E.
4. **Opening a record.** C and the received tag are public. Each party
   supplies T_X as above; the engines compute T_A ⊕ T_B ⊕ E, compare it with
   the received tag, and use the resulting private acceptance bit to gate the
   release of the decrypted content exactly as today.

## What a deviating party can do

Let A* deviate; B is honest (the other case is symmetric).

- **Wrong T_A while sealing.** The opened value is tag ⊕ δ for a δ that A*
  knows. The true tag is a public value in an honest run, so nothing is
  learned; the server rejects the record. This is denial of service, which
  either party already has.
- **Wrong T_A while opening.** For the genuine record any δ ≠ 0 causes
  rejection. For a forged record (C*, tag*) the check passes only if
  T_A' = tag* ⊕ E ⊕ T_B(C*). T_B(C*) depends on B's shares and E is a fresh
  AES output per record, both unknown to A*, so each attempt succeeds with
  probability 2^-128, and a failed check ends the session. One bit (accept or
  reject) is revealed per attempt, as it is today.
- **Wrong shares of the powers.** The shares are produced by the engines
  (malicious-secure) and delivered through authenticated directed openings, so
  a party cannot obtain or induce inconsistent shares; it can only lie about
  T_X, which is covered above.
- **Reuse.** The same power shares are used for every record under K. Each tag
  is masked by its own pad E, as in GCM itself; the opened tags are genuine GCM
  tags on ciphertexts both parties already see.

Not covered by this argument and to be checked in review: the exact
abort/ordering rules (C must be fixed before either T_X is supplied; a failed
tag check must be terminal), and nonce uniqueness, which the Lean application
policy already enforces through sequence reservation.

## Cost estimate

| | now | with local shares |
|---|---:|---:|
| Per record of b blocks | ≈ 22 k · b ANDs | ≈ 5 k · b + one AES + a 128-bit compare |
| Request seal (≈ 1,260 bytes) | 1.41 M | ≈ 0.4 M |
| One-time per key, records up to 1.3 KB | — | ≈ 41 multiplications ≈ 0.7 M ANDs |

## What would be built

- Lean kernels: H sharing, shared-element multiplication with re-sharing,
  CTR-only seal returning the private pad, tag combine, tag check.
- A directed (one-party) authenticated opening in the runtime session layer.
- Local GF(2^128) arithmetic on a party's own shares and public blocks, in the
  worker (like the local curve arithmetic of the split key agreement).
- Every seal/open kernel switched to the CTR-plus-check form.

The linear step (a party evaluating its half of the tag polynomial on public
blocks) happens outside the engines and therefore outside the Lean kernel
theorems; the theorem to state is that T_A ⊕ T_B equals GHASH_H of the blocks
whenever the shares XOR to the powers of H.
