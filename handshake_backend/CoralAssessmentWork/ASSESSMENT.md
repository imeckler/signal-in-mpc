# Coral: bounded repair decision

The released artifact is **not an available malicious five-party backend**. Do not benchmark it under that label. The published packed protocol remains a concrete engineering route; this inspection does not establish that route impossible or find a flaw in the paper. No native candidate, tamper acceptance, or performance result is claimed here.

## Reproducible boundary

Paper: Huang et al., *Coral: Maliciously Secure Computation Framework for Packed and Mixed Circuits*, CCS 2024, https://eprint.iacr.org/2024/1372.pdf. The indexed full text was inspected (Figures 6–8 and 20, Theorems 4–5); direct PDF download returned403. No raw PDF hash is claimed. Figure6 requires both authentication checks before returning converted values; Figure7 checks the sacrificed encoding pairs; Figure8 uses authenticated quintuples. Appendix conversion functionality must also be instantiated, not assumed from a packed register type.

Author code: https://github.com/AntCPLab/OpenCoral/tree/9da23b7dca5ab8638428c91b65ebd405a65a046e (ccs-artifact). `source-report.json` records31 selected exact Git blobs and all submodule revisions from the pinned recursive tree. `check_source.py` verifies downloaded bytes against those blob identities and records source anchors. It is a provenance check, **not a malicious-security test**. No vendor tree is committed.

The stock mapping packs14 Boolean lanes into GF(2^42), with a225-bit multiplication-friendly encoding. Its field/MAC/check domain is not the current GF128 baseline. A40-ish statistical profile, computational OT/PRG assumptions, and explicit per-phase error accumulation would need to be reported separately; no S128 claim follows from128-bit OT blocks. Production n5/t2/S128 remains unchanged.

## Reachable blockers and repairs

| Entry point / exact pinned source | Observed behavior | Reuse / missing work |
|---|---|---|
| `RmfeShare::MC` → `GC/RmfeMC.h:48–71` | `Check` verifies bookkeeping then deletes pending values/MACs without an authentication equation. `exchange:28–45` opens with unchecked broadcast. | Existing MP-SPDZ `MAC_Check_<U>::Check` has joint randomness, committed MAC residual opening and failure propagation. Porting that algorithm is plausible, but must validate this fork's types, key generation, equivocation handling and error bound. Merely calling the current Check adds no authentication. |
| `RmfeSharePrep::set_protocol` → `tinyot2rmfe`; `buffer_triples:99–130` → TinyOT triples → converter | `TinyOT/tinyotprep.cpp:20–35` constructs peer `1-my_num`, then Alice/Bob Fpre. | This is an actual two-party dependency, not a party-count option. Replace it with an actively authenticated n-party Boolean triple source, or implement another published packed-quintuple construction in full. |
| `Protocols/RmfeShareConverter.hpp:67–69` and `GC/RmfeSharePrep.hpp:149–150,344–345` | Only input contributions from parties0/1 are combined. | Generalize sums to all parties **and** supply a valid n-party source sharing/authentication model. A loop edit alone does not supply that model or its conversion proof. |
| `GC/RmfeMultiplier.hpp:23,98–115` | Auth-FOLE uses `passive=true`, passed as `malicious=false` to Ferret. | The dependency offers an active Ferret option. Whether surrounding sacrifice authenticates this particular passive path must be mapped; switching a boolean alone does not prove the resulting FOLE/MAC protocol. Audit baseOT, correlation checks, input authentication and retained key binding. |
| `RmfeShareConverter::convert:95–105` | Compares decoded consistency then calls source/destination Check; destination Check is currently empty. | Preserve both checks, mask privacy, sacrifice randomness, challenge order and delayed release. Test inconsistent conversion with otherwise valid MACs, not just a MAC flip. |
| `buffer_crypto2022_quintuples` alternate benchmark branch | Contains cost-mock calls and non-aborting failure comments. | Not a secure fallback. Excluded from candidate route. |

The alternate fake-preprocessing PRNG is conditional; this assessment does **not** claim every normal preprocessing PRNG is public. Likewise, passive FOLE is an unresolved composition obligation, not an accusation that the published proof uses passive security incorrectly.

## Decision frontier

A bounded repair of released code is **not established**: fixing the missing MAC equation still leaves a two-party authenticated preprocessing architecture. Implementing the full published multiparty construction is substantial but specified engineering, not evidence that efficient t2 compact computation is cryptographically unavailable.

The most direct t2 implementation route is:

1. Instantiate the paper's authenticated n-party Boolean preprocessing (or an already supported malicious n-party source with a proved sharing adapter), active RMFE-field MAC/input functionality, and Figures6–8 exactly. Reuse checked MP-SPDZ MAC/check primitives and a supported malicious OT implementation; keep the42-bit statistical profile explicit initially.
2. Implement published packed arithmetic/Boolean conversion with Fp25519, including canonical bit/word semantics, all-party contribution, conversion sacrifice and **both** source/destination authentication barriers. Coral's SPDZ2k converter is not automatically an Fp25519 converter. No local linear map of existing Shamir evaluations implements this change of sharing domain.
3. Only then run tiny n5 tests: honest mixed arithmetic/packedAND equality; bad input/MAC; corrupt quintuple; inconsistent but authenticated conversion; two coordinated corrupt contributions; abort before output; repeated-use/nonreuse and teardown. Reject all outputs on any uncertain check. Timing comes after these gates.

An alternative using existing n5/t2 malicious field MPC to realize packed preprocessing could avoid importing the two-party TinyOT stack. However, replacing authenticated additive shares by Shamir shares and generating normal pairs changes the realization of the ideal functionality. This requires a concrete composition/parameter mapping and cost model; no such realization is claimed here. In particular, applying the GF2-linear RMFE projection independently to GF42 Shamir evaluations is not valid in general.

Available fallback remains the tested n5/t2/GF128 CCD hybrid (high bytes). The measured compact3PC control is explicitly t1/configured40, an optional topology/security tradeoff rather than a replacement satisfying t2. DEN22's released core-only benchmark and unchecked Coral artifact are not secure t2 alternatives. There is currently no validated compact t2 drop-in in the inspected code.

Next decision is whether to fund the multiparty Coral implementation above, or explicitly choose the weaker3PC tradeoff. No heavy build of the released artifact is warranted before that architecture is resolved. Cache improvements already demonstrated actual producer reuse but do not fix its~2.18GB/message payload.
