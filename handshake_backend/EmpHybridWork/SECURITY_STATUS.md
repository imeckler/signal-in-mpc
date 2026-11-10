# EMP hybrid candidate: blocked security acceptance

The pinned unaudited EMP rewrite (`a245ca0f67abaf2d48c711e3c050ce961e60ad29`) is not an accepted private/malicious backend. All earlier EMP/hybrid reports in this work area are functional or fault-control evidence only. They do not establish input confidentiality, secure conversion, or secure full-application throughput. No native curve execution has been performed.

`input-boundary-report.json` reproduces three concrete failures without disabling checks:

- The existing input phase transmits raw private input bits and opens both input-mask shares. The observer recognizes the other party's random 256-bit input using only a public digest; no input bytes are logged.
- Bob can change the unauthenticated PUBLIC output forwarded to Alice; both processes exit normally with different outputs.
- Bob can report a false masked AND output while retaining its actual local value; the honest Alice accepts a wrong one-AND output despite the existing validation. Fresh independent padding ANDs satisfy the legitimate chunk-size requirement.

These findings concern this exact implementation and API. They are not claims that the published authenticated-garbling protocol is insecure.

## Isolated input repair

`prepare_input_fix.py` verifies the frozen linear-mask overlay and creates separate diagnostic and input-repair trees. The repair opens only the non-owner's authenticated mask share to the input owner, then exchanges masked inputs. It validates bit encodings before indexing. This follows the owner-only input boundary in Figure 3 of Katz–Ranellucci–Rosulek–Wang, *Optimizing Authenticated Garbling for Faster Secure Two-Party Computation* ([2018/578](https://eprint.iacr.org/2018/578)); the eprint lists a revision notice concerning earlier roundtrip complexity.

All eight diagnostic/rejection assertions pass. Imported AES and SHA controls also pass with the input repair. A masked packet differing from the fixture input is a regression check, not a proof of confidentiality. PUBLIC and ALICE openings are unconditionally rejected in this repair profile. B-only functional outputs remain available for component investigation, not security acceptance.

## Required next decision

The full active masked-wire validation, its ordering/privacy argument, and authenticated output functionality must be mapped to an exact supported protocol and implemented before accepting conversions or native curves. An input-only patch cannot repair the complete backend. Candidate routes are completion against the exact revised KRRW protocol or reuse of a supported historical authenticated output/validation engine after its own source/security audit. A reciprocal MAC formula alone is not a reviewed protocol composition.

The EMP↔MASCOT value algebra, pool bookkeeping, and roundtrip vectors remain useful tests, but their cryptographic guarantees depended on the invalid EMP black-box assumption. Statistical40/computational128 configuration does not cure this issue. No production, threshold, or statistical-security setting has changed.

## Reproduction

Build the `emp-input-boundary-probe` and `modern-worker` CMake targets separately with each generated tree, as recorded in `.deps/two-party-comparison/input-fix-build-source.json`, then run:

```
python3 handshake_backend/EmpHybridWork/check_input_boundary.py
```

The committed report binds exact source, binaries and logs. Its explicit acceptance fields are `diagnostics_completed: true` and `secure_hybrid_backend: false`. Every direct child is waited/reaped by the runner. This is not an erasure/crash-cleanup claim. Generated vendor trees, binaries and random fixture inputs are not committed.
