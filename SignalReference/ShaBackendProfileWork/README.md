# Explicit executable SHA profiles

`reference` preserves the original nested-add expressions by default. `gate-efficient`
selects proved carry-save sum4/sum5; `latency` additionally selects the proved
parallel-prefix final adder. Neither selection changes the concrete SHA function.
The five audited profile/compiler endpoints use only foundation axioms (axioms.txt).
The existing actual-source Sha256Round, ShaCompact, and ShaCompactEquivalence bridges
were separately rebuilt; no generated Rust/Aeneas modules changed.

Run `python3 SignalReference/ShaBackendProfileWork/check.py` and `check_prepare.py`.
The public component export uses ORIGINAL compress/HMAC/HKDF/private-HMAC callers,
not the isolated alternative compression implementation. All 102 cases across12
profile/operation combinations agree, including hashlib/HMAC and partial private
lengths. Block AND depths3212→838; HMAC/HKDF9549→2505; private HMAC9552→2508.
These are public exported-graph levels, not measured WAN latency/native throughput.
No full-service/native profile pass is claimed by this receipt.

Actual service entry point:

```
python3 signal_backend/VariableServiceWork/prepare.py 260 80 0 0 --sha-profile latency
```

This creates a distinct immutable `sha-latency` closure, copies compiler/adapter
sources, pins profile metadata and Boolean/field product hashes, and preserves
existing/failed candidates. The actual compiler checks the complete JSON profile;
legacy untagged artifacts are accepted only as reference. Explicit export caching
requires exact transitive Lean-source and product identity. The public metadata
routing check reads both file boundaries because Lean sorts sha_profile after nodes.

Generic Ops audit: all current consumers are listed with source hashes in
ops-consumers.json. SHA compression and ring-buffer ShaCompact both dispatch nary
sums; private hashing/HMAC and TLS HKDF forward the selected Ops. Service prepare
forwards Ops through private Signal/SPQR, sealed sender and relay assembly. Fixed
symbolic instantiations in other exporters and theorem statements retain their
reference behavior; selection is explicitly scoped to this exporter, not a global
switch. Existing generated artifacts remain historical receipts. Compiler/Hom
selection endpoint composes to ORIGINAL concrete service semantics.

This checkpoint does not include Base64 countV2 production integration; its
normalized-buffer composition proof remains pending. Previous mixed commit aacda3d
included the parser owner's validated files and was retained without rewriting.
