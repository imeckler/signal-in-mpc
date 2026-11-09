# Boolean backend selection checkpoint

Status: source/configuration audit, not backend promotion. Production remains five parties, threshold two, malicious abort, configured statistical128. No party processes or private data are used by the guard fixture.

## What the current hybrid actually does

`StrongShamirShare` combines Fp25519 arithmetic with `MaliciousCcdSecret<gf2n_long>`. Boolean registers have packed lanes, but each Boolean share is a full GF128 evaluation. Measured online payload is128 bytes per logical AND per party on the current topology. It is a functional hybrid, not compact-bit network sharing. The paired eight-text comparison is preserved in `../BatchThroughputWork/comparison-report.json`; batching barely changes bytes/message.

`GC/CcdPrep.h` delegates to malicious arithmetic triple generation. `MaliciousRepPrep.hpp::sacrifice` samples one public field challenge for the batch, opens masked differences, and checks the resulting zero relations. Both triple generation and sacrifice call `check_field_size`. Merely reducing `gf2n_long` to `gf2n_short` would violate that construction's configured-security guard. `SpdzWise.hpp::zero_check` also checks the underlying field size; selecting SY does not by itself supply a small-value/extension-check binary backend.

`check_guard.py` executes the actual pinned implementation's public field initialization, codec and guard. GF8/S128 and GF40/S128 reject; GF128/S128 accepts. GF40/S40 accepts only as an explicitly labeled benchmark control. Short fields serialize as8 bytes, so GF8 is not a one-byte codec and neither is a bit-packed wire protocol. These are configuration tests, not tests of preprocessing/authentication security.

The upstream source revision is113c4e47dd94bca9ecab029d2f0abe649bea5c52 (v0.4.4), established by the authoritative archive verification recorded in BackendPackingWork. The extracted dependency directory has no independent git repository; parent-repository HEAD is not its revision. Exact inspected runtime hashes are in guard-report.json.

## Primary benchmark and revision boundaries

* [LN17 conference paper](https://acmccs.github.io/papers/p259-lindellA.pdf), SHA256 `37aaf3cc088a67fb5757c0b6af5f13fff02976716df73bec16d1518405585da1`: Sec7/Table1 is one million arithmetic multiplications, depth20,61-bit prime,statistical40,1ms Azure. Its five-party threshold-two PRSS_GRR_open result is1890ms. Sec7 explicitly excludes its small-field framework from the implementation. This is not a Boolean/Signal throughput measurement.
* [Official LN17 revision metadata](https://eprint.iacr.org/2017/816) reports a2026-01-13 revision correcting a small-field protocol error. The corrected PDF and archive versions endpoint returned403 in this environment. The conference PDF is not being represented as that corrected body. No parameter derivation is accepted from the old small-field text.
* [CHI2018 author slides](https://crypto.iacr.org/2018/slides/28799.pdf), SHA256 `f3ac3b852f9fa67f6144a8a78750c63196a801f458823799348fae526ee41bf0`: downloaded and visually inspected PDF pages15 and18. Page18 keeps the random multiplier private and replaces the per-gate extra multiplications with a sum-of-products check. This supports investigation of separate value/check domains; slides do not establish the complete128-bit parameterization, composition, or executable conversion path.
* [Official CRYPTO2018 paper archive](https://www.iacr.org/archive/crypto2018/10993138/10993138.pdf) and [2018/570 PDF](https://eprint.iacr.org/2018/570.pdf) returned403. Indexed primary text is available, but no fetched-body hash or full-body review is claimed.
* [2023 journal version](https://link.springer.com/article/10.1007/s00145-023-09453-7) is a distinct later publication. Its abstract/metadata are accessible; full PDF is subscription-blocked here. The2018 slides are not a substitute for its proof.
* [Field Extension in Secret-Shared Form](https://eprint.iacr.org/2019/386) is an additional published route separating value and verification fields. It is not implemented or security-reviewed for this runtime by this checkpoint.

## Supported-code selection matrix

| Candidate | Five-party/two-corrupt boundary | Present evidence / missing requirement |
|---|---|---|
| Current malicious CCD GF128 | Current functional profile | Exact source and native interoperability passes; expensive per-bit wire cost |
| Stock CCD GF8/GF40 with S128 | Rejected | Actual guard regression; no guard deletion permitted |
| Small-field LN17/CHI extension verification | Published honest-majority family | Corrected/full proof, exact parameters, supported implementation, checked Fp conversion and failure/epoch ownership not yet established |
| Stock SY Shamir | Arbitrary honest majority arithmetic | Same-field zero-check guard; not a compact-bit replacement via configuration |
| Tiny/Tinier | Arbitrary-party dishonest majority can cover n5 | Prior BackendPackingWork records sacrifice40 cap, full128 MAC truncation, unsupported current KOS security path and unfavorable raw-COT floor. No supported128 promotion |
| Malicious Shamir BMR | n5 candidate previously measured | Prior matched tiny result had about14.6x CCD payload; no throughput-win claim |
| Malicious Rep3/PS binary | Three parties/one corrupt | Compact binary option only under an explicitly different trust model; not n5/t2 |
| Rep4 binary | Four-party profile | Not the requested n5/t2 profile |

[Official mixed-domain documentation](https://mp-spdz.readthedocs.io/en/latest/non-linear.html) pairs malicious Shamir with extension-field CCD and MASCOT with Tinier. It does not claim that arbitrary binary backends can be exchanged while preserving the existing daBit bridge. Live documentation is supplemental; pinned code controls the actual candidate.

## Decision and seven-party alternative

No supported compact Boolean n5/t2/S128 replacement has been established in the pinned runtime. Do not switch the current backend. This is a statement about inspected available code, not an impossibility result.

The seven-party/two-corruption option deserves a separate source audit: [DEN22 author implementation](https://github.com/anderspkd/ccs-DEN22) contains core experiments for “Fast Fully Secure Multi-Party Computation Over Any Ring with Two-Thirds Honest Majority”. Seven parties satisfy t<n/3 for t=2 without reducing the corruption count. This is a research implementation outside MP-SPDZ, not a selectable current backend or a completed application/runtime. Its actual ring/Boolean representation, arbitrary-n coverage, verification parameters, mixed Fp25519 conversion, lifecycle and measured costs remain to be checked before any candidate build. The pinned Rep4 implementation explicitly asserts four parties and is not a seven-party shortcut. ATLAS in the pinned code is semi-honest, so it is not an alternative malicious backend.

The matrix's concrete cost/security details are supplemented here:

| Available implementation | Value/wire domain | Statistical-check status | Mixed-conversion status | Cost / required work |
|---|---|---|---|---|
| Current StrongShamirShare + malicious CCD | Fp25519 + GF128 evaluations,16B binary element | Configured128, single-challenge guarded sacrifice | Existing checked daBits |128B/AND online measured; production-compatible baseline |
| Stock malicious CCD gf2n_short | GF8/40 values,8B element | S128 guard rejects | Existing family but rejected security config | Not a candidate without replacing verification |
| Stock SY Shamir | Underlying field values plus MAC | Same-field zero-check guard | Binary companion remains CCD | Could improve arithmetic dot-products; does not fix compact Boolean traffic |
| Tinier | Authenticated bits with MAC/COT state | Stock sacrifice<=40; prior128 gaps documented | MASCOT pairing exists,128 path unvalidated | Prior raw-COT floor unfavorable; do not build/promote |
| Existing malicious Shamir BMR | Garbled labels + arithmetic preprocessing | Prior measured candidate, not a new compact-share proof | Separate bridge/lifecycle required |~14.6x tiny CCD traffic; no advantage shown |
| Rep3/PS binary | Bit-packed replicated shares | Family-specific cut/check parameters require explicit audit | Existing Rep3 pairing, not StrongShamir n5 | Only n3/t1; optional trust-model change |
| DEN22 core experiments | Ring representation not yet inspected | Paper family t<n/3; exact code/check parameters unverified | No existing Fp25519 integration established | Seven-node/two-corrupt research option; audit before implementation |

## Next executable work

1. Add isolated depth20 arithmetic and Boolean controls with exact equal-work counts, first on the existing128 runtime. Optional61-bit/S40 historical controls must be separate binaries/profiles and never application defaults. Record total/online/preprocessing bytes, generated versus consumed resources where available, and setup versus repeated calls.
2. Resolve the corrected small-field source and locate a supported implementation before proposing a protocol replacement. Map input checks, multiplication verification, openings, authentication, union terms, cross-domain conversion and epoch/failure state together. Statistical128 does not imply a lifetime-wide bound independent of invocation count.
3. Independently cache immutable prepared public programs to eliminate measured repeated loads. Cache complete pinned code/config identity only; retain no secret processor, preprocessing, protocol or I/O state. This can save CPU/load time but cannot remove gigabytes of protocol traffic.

No more full application baseline is warranted until one of these changes has actionable evidence. All prior measured reports remain historical receipts.

## DEN22 bounded implementation result

The author repository at immutable commit `57d7bed3895975f78b215226d851156aea1826c8` is **rejected as a secure replacement**, without compiling or running parties. `den22-report.json` pins the downloaded archive and every source file; `audit_den22.py` checks the exact inspected markers. This is an engineering completeness result about that code, not a criticism or disproof of the published protocol.

`check.h` declares but omits check-randomness setup and transcript agreement; generates coefficients with a default-zero-seeded PRG; substitutes zero for the required hashes; and receives/discards reconstruction values without checking them. `exp_mult.cc` uses fake public inputs and never calls the check protocol. `exp_check.cc` measures incomplete check components. Default values are61-bit prime elements serialized in8bytes, not a Boolean packed implementation. The code uses t=(n−1)/3, hence7nodes/t2, but the experiment does not establish complete malicious security, output validation or statistical128.

For7/t2 a local replicated share contains15 elements (120bytes). The multiplication-only Send loops move10field elements/group/gate including two self sends, or8external elements=64bytes/group/gate. This is source-derived incomplete-component traffic, **not secure full-protocol throughput**; it omits correlation setup, input, complete verification, output and framing. No performance advantage is accepted from this number. There is no existing checked Fp25519 bridge or lifecycle ownership integration.

A published full small-field protocol plus missing engineering is distinct from cryptographic uncertainty: a future implementation must first bind the corrected theorem and exact parameters, then supply all missing protocol stages and tests. Absence of a supported stock5PC/t2 backend is not an impossibility result. Optional3PC/t1 comparisons may inform an explicit trust/performance choice, while production remains5PC/t2.
