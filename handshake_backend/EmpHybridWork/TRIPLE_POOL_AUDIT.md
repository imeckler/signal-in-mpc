# Triple generation (`TriplePool`): source-to-figure comparison

Status 2026-11-09 (revised after review discussion). A reading of `emp-ag2pc/backend/triple_pool.h` at `a245ca0f…` against the leaky-AND and preprocessing figures (Figures 5.3–5.5 in the thesis copy, `.deps/two-party-comparison/xiao-thesis.txt`; the eprint 2018/578 PDF was not retrievable). It records where the stock code departs from the figures and what candidate v3 does instead. It is **not** a security proof and does not change `secure_hybrid_backend: false`.

## Stock code versus the figures

| # | Figure | Stock code | Candidate v3 |
|---|---|---|---|
| 1 | Each leaky AND ends with its own equality test (5.4 step 5) | One digest over all layers, tested after all layers were combined | Each layer tested before it is combined |
| 2 | "secure coin-flipping" for the bucketing randomness (5.5 step 6) | Value derived by hashing the channel transcripts | Commit/open joint coin drawn after the layer passed its checks |
| 3 | A random permutation of the sacrifice triples | A cyclic shift of each layer | Cyclic shift kept, with the bound below |
| 4 | `d := Open(...)` when merging (5.5 step 6b) | Raw share bits, no MAC check | Authenticated open |
| 5 | Merging updates the wire's mask (5.5 step 6c) | Layer 0 is the leaky AND of the gate's own masks λ_α, λ_β; masks are kept; a further raw-bit exchange corrects the product share | Function-independent form: layer 0 is a fresh random triple; the masks meet the finished triple only through authenticated Beaver openings |
| 6 | Authenticated bits come from a completed functionality | COT consistency check deferred past leaky-AND and garbling messages | Checked after every mint, before use |
| 7 | — | Bucket size from `max(n,1024)` while the layer length is the actual count | Bucket size from the actual layer length |
| 8 | — | Hash-tweak seed is a fixed constant on every call | Distinct seed per call |

Why row 5 was changed rather than argued: in the stock construction the sacrifices cancel algebraically (c_k ⊕ d_k·a_k = a_k·λ_β, so the final product share equals layer 0's). The x-query that the leaky-AND functionality permits (Figure 5.3) therefore lands on λ_α itself, a mask that stays in use while Λ_α is public. Combined with row 4, a misreported correction bit shifts the product share by λ_β. Both were judged unacceptable for malicious security.

## Candidate v3 construction

For n AND gates, with L = n and bucket size B:

1. Mint B layers of L random authenticated triples-to-be (a, b, r). For each layer: COT check, leaky AND (Figure 5.4), per-layer equality test.
2. For layers k = 1…B−1: draw a joint coin, shift the layer by r_k = coin mod L, authenticated-open d = b₀ ⊕ b_k, then X ⊕= a_k, Z ⊕= c_k ⊕ d·a_k. Y = b₀ throughout.
3. Authenticated-open e = λ_α ⊕ X and f = λ_β ⊕ Y; set σ = Z ⊕ e·Y ⊕ f·X ⊕ e·f.

Bucket bound used (my derivation, for review). Each shift is uniform on L values and is fixed only after that layer's messages are complete. If the adversary places t_k x-queries in layer k, each passes with probability 1/2 independently of the shifts, and a given bucket is fully queried only if every layer's shifted position was queried. A union bound over layer-0 queries gives

`Pr[all queries pass ∧ some bucket fully queried] ≤ t₀·2^(−t₀) · ∏_{k≥1} t_k·2^(−t_k)/L ≤ ½ · (2L)^(−(B−1))`.

The code takes the smallest B with `max(1, log2 L)·(B−1) > 40`, which makes this at most 2^(−40−B). This counts x-queries only; the Δ-guessing part of the Figure 5.3 query is not in this bound.

Cost on the imported smoke graphs, total bytes versus the input-repair-only tree: AES-256 +16%, SHA-256 +7%, plus one coin round and one extra opening per layer.

## Evidence and what it does not show

`check_validation.py` now includes a false share in a triple-generation opening, rejected by the MAC check. AES-256 and SHA-256 outputs still match OpenSSL/hashlib through the new Beaver step, which exercises the σ formula. No test covers a cheating party inside the leaky AND itself.

## Still open

1. The bound above, and whether cyclic shifts need anything beyond it.
2. The equality test, joint coin and openings are hash-based in the random-oracle model; digests are now tagged with purpose, sender and a lockstep counter.
3. Statistical 40 and the whole-lifetime count of buckets and openings.
4. SoftSpoken⟨4⟩ malicious-mode internals in emp-ot were not read.
