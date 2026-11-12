# Kyber-1024 / ML-KEM-1024 encapsulation to a private key

Status 2026-11-11: Lean definitions, kernels, theorems and a kernel check exist and pass, and the
kernels run in the worker when a contact's device gets a new session (section 8). Measured: **12,521,696 AND gates** for the variant PQXDH uses
(11,988,128 for FIPS 203), in twelve kernel runs of at most 1.4M each, against about 190–210M for
`establish-kem`. Nothing is opened.

Files: `TlsMpc/Signal/MlKemFast.lean` (definitions), `TlsMpc/MlKemFastKernels.lean` (kernels, `find`),
`TlsMpc/MlKemFastProofs.lean` (theorems), `EmitKemKernel.lean` (emitter `kem_kernel_emitter`),
`check_kem_kernels.py` (check), `kem-kernels-report.json` (its result).

## 0. Which function

The task description says ML-KEM-1024 (FIPS 203). **libsignal's PQXDH does not use FIPS 203.** A Kyber
prekey has key type 8 and libsignal calls `libcrux_ml_kem::kyber1024::encapsulate`
(`.deps/libsignal-v0.106.1/rust/protocol/src/kem/kyber1024.rs`): round-3 Kyber, which hashes the
randomness first (`m = H(randomness)`) and derives the secret as `SHAKE256(K ‖ H(c))`. FIPS 203 is key
type 10 (`mlkem1024.rs`, behind a feature). `establish-kem` passes `kyber := true` for the same reason.

So every kernel that differs takes a `VARIANT`: `kyber` (what must be used today) or `mlkem`. Both are
implemented, counted and checked. They differ by 14 Keccak permutations.

One deliberate difference from libsignal: the kernels apply the modulus check of FIPS 203 §7.2 in
both variants (a key with an encoded coefficient ≥ q is rejected). libcrux's `kyber1024::encapsulate`
does not check and would reduce such a coefficient. A key libsignal generated never has one.

## 1. Where the 190M went

`establish-kem` was never lowered. The count below multiplies measured single operations of the
existing definitions (lowered alone, `.deps/agent-kem/emitter/Probe.lean`) by how often encapsulation
uses them.

| Existing operation (32-bit words) | AND gates each | Uses | Total |
|---|---|---|---|
| `mulMod` of two secrets (32-bit multiply, `umod 3329`) | 5,615 | 10,240 | 57.5M |
| `mulMod` by a public constant | 2,234 | 8,064 NTT + 2,304 scaling + 2,560 in products | 28.9M |
| `addMod` / `subMod` (an addition and a `umod`) | 2,173 / 2,236 | 16,128 NTT + 5,120 in products + 5,120 sums + 1,536 errors + 2,304 CBD | 66.3M |
| `compress` (a 32-bit division) | 2,119 | 1,280 | 2.7M |
| Sampler: 448 candidates, each compared and selected into 256 slots of 64-bit words | 3.0M per entry | 16 | 48.2M |
| Keccak-f[1600] | 38,400 | 100 | 3.8M |
| | | | **about 207M** |

So: three quarters is the generic remainder after every coefficient operation (about 2,100 gates each
time, 53,000 times), one quarter is the quadratic sampler. Keccak, the only part that cannot shrink, is
under 2%.

Levers from the task description, as they turned out:

* *12-bit arithmetic with Barrett reduction*: yes, this is the design (section 2). 45× on additions,
  12× on products, 18× on constant multiplications.
* *Matrix expansion under MPC*: 64 permutations (2.46M) cannot be avoided; the selection is a
  compaction network, 78,841 gates per entry instead of 3.0M.
* *Keccak*: the existing circuit (`Signal.Keccak`) is reused unchanged; 100 permutations for `kyber`
  (12 for H(ek), 1 for H(m), 1 for G, 9 for the noise, 64 for the matrix, 12 for H(c), 1 for the KDF),
  86 for `mlkem`. The lowering drops the unused permutation after the last squeezed block.
* *NTT is linear*: true, but in a Boolean circuit a multiplication by a public constant modulo q still
  costs 67–144 gates, so the nine transforms are 1.76M. Free only with shares modulo q (a third engine).
* *Secret × secret*: 10,240 products, 447 gates each (276 for the 12×12 product, the rest Barrett).
  With the additions around them this is the largest part of the new circuit (5.4M, 43%).
* *Field engine*: no. A field product is one MASCOT triple, about 79 KB of traffic
  (`CONVERSION_COST_LEVERS.md`), and every value entering or leaving the field costs a 765-gate modular
  addition plus a prepared mask. A 12×12 Boolean product is 276 AND gates. Packing does not help: one
  field product of two packed polynomials gives a convolution, not the 10,240 separate products.

## 2. Design

A coefficient is a 12-bit word that is always in 0..3328 (as in the specification, only narrower), so
the polynomial layer has the specification's shape operation for operation and can be compared with it
coefficient by coefficient.

| Operation | Circuit | AND gates |
|---|---|---|
| `addMod` | 13-bit sum; add 2^14 − q; select by the sign | 44 |
| `subMod` | 13-bit difference by one addition (`~(~x + y)`); add q under the borrow | 23 |
| `mulConst c` (public c: every NTT root, 3303, the 128 base-multiplication constants) | quotient `x·⌊c·2^12/q⌋ >> 12` (the constant is public), remainder on 13 bits, one conditional subtraction | 67–144 |
| `mulMod` | twelve rows of `x AND y_i`, added; Barrett with `((v >> 9)·5039) >> 15`; remainder on 13 bits | 447 |
| `compress 11`, `compress 5` | `(x·161271 + 131032) >> 18`, `(x·315 + 16384) >> 15` (exact for x < q) | 179, 63 |
| below q | carry of `x + 767` | about 12 (not measured alone) |

Adders are the bit-vector compiler's, which the lowering turns into one AND per bit; multiplications by
constants are the compiler's shift-and-add with the constant folded.

**Sampling.** The 672 squeezed bytes are 448 candidates of 12 bits (the candidates of FIPS 203's
`SampleNTT` are exactly consecutive 12-bit groups of the little-endian bit stream). Each candidate gets
a validity bit (below q) and a 9-bit distance: the number of rejected candidates before it. Nine stages
follow; in stage s every valid cell whose distance has bit s set moves 2^s places to the left. After
them the i-th accepted candidate is in place i. The entry is accepted exactly when place 255 holds a
valid cell; otherwise all 256 coefficients are zero and the status byte is 0. Order is preserved and
two cells never meet: for accepted candidates at p < p′ the distances satisfy d′ − d ≤ p′ − p − 1, and
reducing both modulo 2^s cannot increase their difference.

**Budget and failure probability.** Four SHAKE128 blocks, the specification's budget
(`MlKem.encapsulate … 224`). A candidate is accepted with probability 3329/4096. The probability
that 448 uniform candidates contain fewer than 256 accepted ones is 2^−105.2 (exact binomial tail,
`.deps/agent-kem/scratch/search.py sampling`); for the 16 entries of one key at most 2^−101.2. With
three blocks it would be 2^−6.9 per entry (unusable); a fifth block gives 2^−261 and would cost 16
permutations and a larger network (about 0.8M gates). The seed is chosen by the key's owner, but
finding a seed that fails takes about 2^101 SHAKE evaluations. If it happens the kernels reject:
`okROW` is 0, `kem-finish` gives status 0 and a zero ciphertext and secret (`finish_rejects`), and the
establishment fails like a bad signature. They never output a wrong or biased matrix. A real client
would have accepted such a key; this is the one known way the result can differ from libsignal's for
a well-formed key.

## 3. Kernel sequence

`find` takes the names below. Inputs and outputs are bound by name; every output is PRIVATE. `ROW` is
0..3.

| # | Kernel | Inputs | Outputs | AND gates |
|---|---|---|---|---|
| 1 | `kem-hash VARIANT` | `kyberPrekey` (1568), `entropyA`, `entropyB` (32, one from each party) | `message`, `kbar`, `coins` (32 each), `keyValid` (1) | 554,303 (`mlkem` 517,247) |
| 2 | `kem-ntt` | `coins` | `rhat` (1536) | 870,474 |
| 3 | `kem-matrix ROW` ×4 | `kyberPrekey` | `rowROW` (1536), `okROW` (1) | 920,545 each |
| 4 | `kem-u ROW` ×4 | `rowROW`, `rhat`, `coins` | `uROW` (352) | 1,384,764 each |
| 5 | `kem-v` | `kyberPrekey`, `rhat`, `coins`, `message` | `v` (160) | 1,366,332 |
| 6 | `kem-finish VARIANT` | `u0`..`u3`, `v`, `kbar`, `ok0`..`ok3`, `keyValid` | `kemStatus` (1), `kemCiphertext` (1568), `kemSecret` (32) | 509,351 (`mlkem` 12,839) |
| | **Total** | | | **12,521,696** (`mlkem` 11,988,128) |

Steps 2 and 3 are independent; 4 needs both; 5 needs 1 and 2. Polynomials travel between kernels as
384 bytes (12 bits per coefficient). The three outputs of step 6 have the names and meaning of
`establish-kem`'s and go to `establish-session`, which opens the single status byte of the whole
establishment. **The KEM sequence opens nothing**: not the ciphertext (it travels inside the encrypted
PreKeySignalMessage), not a validity flag. A malformed key, a failed sample and a bad signature are
indistinguishable to the nodes.

Where the gates are (`kyber`): Keccak 3.84M (31%); base multiplications and their sums 5.4M (43%); the
nine transforms 1.76M (14%); sampling networks 1.26M (10%); compression, noise, key check, gating 0.3M.
Lowering a kernel takes 3–7 s and at most 1.2 GB. At 0.75 s per million gates the sequence is about
9.4 s of engine time per device.

Not done, in order of expected gain: adding the four products of a row before reducing (about −1.5M);
Karatsuba for the degree-one products (about −1M); a five-term signed form of 5039 and of the roots
(about −0.4M). Each would break the operation-for-operation correspondence that the refinement
theorems use, so they were left out; 12.5M is half the target.

## 4. What is proved (`TlsMpc/MlKemFastProofs.lean`)

All with `propext`, `Quot.sound`, `Classical.choice` only; no `sorry`, `native_decide`, `bv_decide`.

* `compiled_correct`: every kernel's exported bits are its Lean definition's.
* `kemHash_spec` … `kemFinish_spec`, `kemSample_spec`: each kernel's output fields are the stage
  function on VALUES applied to the input fields' values.
* Arithmetic on values equals the natural-number formula: `addValue_toNat`, `subValue_toNat` (inputs
  below q); `mulValue_toNat` (ALL 12-bit inputs: the Barrett bound is `barrett_nat`, the multiplier is
  identified with the library's `BitVec.mulRec`); `mulConstValue_toNat` (every constant below q, all
  12-bit inputs: `shoup_nat`); `compress11_toNat`, `compress5_toNat`, `ltQValue_eq`, `cbd_coefficient`
  (kernel computations over all 4,096 or 16 inputs).
* Refinement to the existing specification on 32-bit words, for polynomials with coefficients below q:
  `forward_refines`, `inverse_refines`, `baseMultiply_refines`, `add_refines`, `dot_refines` (the result
  zero-extended is `MlKemNtt.forward` / `inverse` / `baseMultiply`, `MlKemPke.add` / `dot` of the
  zero-extended inputs, and is again below q), `wide_compress11`, `wide_compress5`.
* `finish_rejects`, `finish_accepts`.
* `sample_small`: the compaction network on all 64 acceptance patterns of six candidates.

**Proved since (2026-11-12), in `TlsMpc/KernelSpecs/KemSample.lean`, `KemEncoding.lean`,
`KemCompose.lean`** (restated in `TlsMpc/Security.lean` section 2e):

1. *The compaction network at the size used*: `KemSample.compact_spec` (the stage invariant) and
   `sample_eq` / `sample_448` (`MlKemFast.sample 256` on 448 candidates is the specification's
   rejection sampling), with `run_refines` / `entry_refines` for the matrix entries.
2. *The encodings*: `KemEncoding.decode12_refines`, `encode_refines`, `cbd_refines`, `noise_refines`,
   `messagePoly_refines` (the bit-list regroupings equal the specification's word encodings).
3. *The composition*: `KemCompose.kernels_compose` (the six kernels, wired by name as the worker
   wires them, compute `pipeline`) and `pipeline_valid_accept` / `pipeline_valid_reject` /
   `pipeline_invalid`: on a valid key (`KeyValid`) the outputs are the reference
   `MlKem.encapsulate` (`specEnc`), zero when its sampling exhausts the budget; zero on an invalid key.

**Still not proved**, exactly:

- that the reference `MlKem.encapsulate` is Kyber-1024: `scripts/check_lean_signal_mlkem.py`
  compares it with libcrux on test vectors;
- the failure probability of section 2 (2⁻¹⁰⁵): a calculation, not a Lean theorem;
- the worker's name binding between the kernels (the `h*` hypotheses of `kernels_compose`):
  trusted C++.

The check (section 5) still compares on values and on gates.

## 5. The check (`check_kem_kernels.py`)

    python3 scripts/guarded.py 10 1500 python3 handshake_backend/EmpHybridWork/check_kem_kernels.py

About 150 s, 1.9 GB. Result on 2026-11-11: all pass (`kem-kernels-report.json`).

* A plain-Python reference (key generation, encapsulation, decapsulation, both variants) is first
  validated: equal to the pinned libcrux 0.0.10 on six key pairs (the oracle binary of
  `scripts/check_lean_signal_mlkem.py`); round trip under libsignal's two test key pairs
  (`rust/protocol/src/kem/test-data`); equal to the `cryptography` 50 package's ML-KEM-1024 key
  generation from a seed, which then decapsulates the reference's ciphertext. No known-answer file
  with ciphertexts exists on disk; libcrux itself is the known answer.
* The whole sequence, both variants, three keys each (two generated, one libsignal's test key):
  EVERY output field of every kernel against the reference, the final ciphertext and secret also
  directly against libcrux, libsignal's private key decapsulating the kernels' ciphertext, and (ML-KEM)
  the `cryptography` package decapsulating it.
* The existing Lean specification and the value instances of the stages, run by
  `kem_kernel_emitter reference` / `stages`, give the same ciphertext and secret.
* Four malformed keys per variant (coefficient 0, 256, 511, 1023 set to q, q+1, 4000, 4095): `keyValid`
  0, status 0, ciphertext and secret all zero. Six failed statuses fed to `kem-finish` (including bytes
  1, 0x7f, 0xfe): the same.
* 22 streams through `kem-sample` (the sampler alone): none accepted, all accepted, 255 and 256
  accepted, accepted ones only at the end, the values q−1 and q alternating, random: 8 rejected with
  zeros, 14 equal to the filtered stream.
* From the layout files: no kernel has an opened output.

Not covered: the engines (the gate lists are evaluated in Python), and a real sampling failure of a
SHAKE128 stream (none can be found; `kem-sample` and the failed-status cases stand in).

## 6. Development helpers (not part of the product)

`.deps/agent-kem/`: `build.py` (guarded `lake -q build`, errors only), `lean.py`, `emit.py` (one
kernel), `scratch/search.py` (Barrett and compression constants, the binomial tail),
`emitter/Probe.lean` (single-operation gate counts).

## 7. Constraints kept

`kemNtt`, `kemV`, `kemSample` take a `Unit` and `find` has `compiler.extract_closed false`, so nothing
is built at program start. `establish-kem` was never lowered or built. Largest kernel 1.38M gates.

## 8. What to change elsewhere

**Done on 2026-11-11** (the live binding of `MULTI_DEVICE.md`, section 7): `MlKemFastKernel.find` is
registered in both emitters, `establish-kem` is no longer offered by `EstablishKernel.find`, and the
worker runs the twelve kernels (variant `kyber`) in steps 2–7 of `bundleEstablish`
(`service_kernels.h`). Measured in the engines: 12.52M AND gates per device, about 0.4 s in
semi-honest and 4–6 s in malicious mode. Two libsignal devices decapsulated the result and decrypted
the messages built on it. `check_kem_kernels.py` still uses `kem_kernel_emitter`. The list as it
was written:

**Emitters** (`EmitFlatKernel.lean`, `EmitHybridKdf.lean`), one import and one alternative each:

    import TlsMpc.MlKemFastKernels
    ... <|> ReceiveKernel.find rest <|> MlKemFastKernel.find rest

After that `kem_kernel_emitter` is only needed for its `reference` / `stages` commands, and
`check_kem_kernels.py`'s `kernel()` can call `circuit_cache.py` like the other checks.

**`TlsMpc/EstablishKernels.lean`**: step 7 of the header becomes the six steps above. Remove
`| ["establish-kem"] => some (establishKem ())` from `find` so that nobody lowers 200M gates by
accident; keep `establishKem` as a definition if wanted (it is the specification's kernel). No change
to `establish-session`: it already takes `kemStatus`, `kemCiphertext`, `kemSecret`.

**`MULTI_DEVICE.md`**: section 6's table row and "ML-KEM encapsulation" alternatives (this is
alternative 2, measured); section 3 step 8.

**Worker** (`service_kernels.h`, `tls_worker_v3.cpp`), inside `bundle_establish` per device:

1. Each party supplies 32 fresh private bytes (`entropyA`, `entropyB`).
2. Run `kem-hash kyber`, `kem-ntt`, `kem-matrix 0..3`, `kem-u 0..3`, `kem-v`, `kem-finish kyber`,
   keeping every output as private wires under its name and feeding later kernels by name.
   `kyberPrekey` is `bundle-device`'s output of that name (1568 bytes, without the type byte 8).
3. Pass `kemStatus`, `kemCiphertext`, `kemSecret` to `establish-session`; drop the rest.
4. Open nothing. Twelve circuits per device, six distinct apart from the row number; all are cached
   by `circuit_cache.py` after the first device.

If a contact ever publishes an ML-KEM-1024 prekey (type 10), use `mlkem` for it; the type byte is
part of the bundle and would then have to select the variant privately or be accepted as public.
