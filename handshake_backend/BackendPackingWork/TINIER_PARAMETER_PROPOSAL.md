# Isolated parameterization proposal, not an enabled protocol

The pinned implementation rejects statistical parameters above 40. That guard
remains intact. `tinier_parameter_bounds.py` records public integer arithmetic
for a possible extension of the existing shuffle/sacrifice/combine construction;
it does not establish full Tinier128 security or measured performance.

Use L final triples, correctness buckets T, leakage-combining buckets U, and
C opened checks. Trim the authenticated raw prefix to exactly M=T*U*L+C before
any challenge/permutation. Let N=U*L. With C>=T, the FLNW Theorem 5.3 bound is
N/binom(M,T), maximized at T bad triples; all other nonzero bad counts either
fail bucket homogeneity or have no larger probability. The script independently
enumerates 3,696 small divisible distributions as an arithmetic regression, not
as a proof replacing the theorem. FKOS Lemma 10 requires the strict condition
U > (s-1)/log2(L)+1; the script tests L**(U-1)>2**127 for s=128.

Current TinyPrep/ShuffleSacrifice uses the SAME bucket size for both phases,
so its conservative extension corresponds to T=U. Separate T/U curves are
explicitly unimplemented: they require separate sizes/ownership and exact
intermediate counts in triple_sacrifice and triple_combine, plus review that
the primary theorem assumptions still match the resulting code. At L=64 the
same-size proposal has T=U=C=23 and M=33,879 (529.36 raw/output). Separating
T=C=12 and U=23 gives M=17,676 (276.19 raw/output). At L=2^20 the respective
expansions are about 64 and 56 raw/output. Neither demonstrates a throughput win.

Source mapping: TinyPrep generates/authenticates raw batches in 64-lane units;
minimum_n_inputs_with_combining currently requests B squared times outputs plus
C. The generation overshoot cannot simply be ignored in the divisible theorem.
A candidate must trim BEFORE randomness, retaining authentic ownership and
wiping discarded secret storage. ShuffleSacrifice's open checks and homogeneous
bucket tests precede its independent combine shuffle. MAC_Check_Base::CheckFor
opens and checks EVERY residual, then checks authentication; it does not insert
a separate probabilistic linear-residual test. Its current rejection prints the
failing value, which must be removed in the caught-failure candidate.

Security accounting still required before implementation/promotion:

* Confirm actual permutation sampling and challenge independence against each
  theorem's fixed-adversarial-input assumptions, including selective failures.
* Bind the OT/authentication implementation and input path to the primary
  assumptions; long GF128 authentication alone does not repair 40-bit sacrifice.
* State correctness and leakage terms separately, plus authentication constants
  (including the FKOS bad-authentication factor), computational OT assumptions,
  input checks, and all per-phase/batch union terms. Configured 128 does not mean
  an entire deployment has failure probability at most 2^-128 for any query count.
* Test adversarial distributions, overshoot/trimming, failed checks, consumption,
  repeated epochs, and caught-failure cleanup before any application lowering.
* Measure raw generation, authentication/MAC/OT/input traffic, online traffic,
  consumed versus generated/discarded batches, CPU and memory. A packed online
  serializer ratio is not a total protocol cost comparison with CCD.

Primary sources: [FLNW17, section 5](https://eprint.iacr.org/2016/944.pdf) and
[FKOS15, appendix F](https://eprint.iacr.org/2015/901.pdf). Exact runtime source
hashes are in tinier-security-feasibility.json; the upstream pin is
113c4e47dd94bca9ecab029d2f0abe649bea5c52. No new mechanism security proof is claimed.
