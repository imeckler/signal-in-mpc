# Balanced base64 length-count candidate

The versioned PrivateBase64CountV2 kernel balances the SAME masked sixteen-bit
additions used by PrivateBase64.count. The original producer/imports/artifact
remain unchanged. There is no division approximation, opened length, or secret
branch. Fuel is public and logarithmic; insufficient fuel still finishes with
an equivalent sequential fold.

Kernel-checked `Concrete.count_equiv` covers arbitrary canonical mask-bit lists,
arbitrary public index lists and every sixteen-bit initial total. Its proof uses
exact modulo65536 addition, so overflow, duplicate/reordered indices, remainder
comparisons and publicLength's sixteen-bit wrapping are preserved. `count_map`
provides the symbolic/concrete Hom boundary. Ten audited endpoints use only
propext/Classical.choice/Quot.sound, with no new axioms/native reflection.

Public numeric checks pass133,840 cases across eight group counts and fixed/
private initial-state modes, including every sixteen-bit length for192 groups
and overflow totals65534/65535. Representative lowering uses the unchanged
malicious CCD compiler/security128 configuration; no native MPC run is claimed.

|192 groups, zero initial total|Existing|Balanced|
|---|---:|---:|
|Executed ANDs/compiled bit triples|4371|2530|
|AND depth/compiled VM rounds|28|23|
|Executed local XORs|4238|2402|
|Maximum local XOR depth|192|14|

This retracts the hypothesis that this counter caused the full service's114,049
AND levels: most sequential increment dependence is local XOR. The42% local
AND reduction is about0.03% of the whole service's6,738,497 logical ANDs, with
only five levels saved here. No end-to-end speed/throughput claim or expensive
full-service rebuild is justified by these numbers alone.

Kernel composition is now complete: `make_canonical`/`resize_canonical` prove
normalization produces canonical masks even for malformed Buffer inputs.
`normalized_count_equiv` and `encode_correct` prove the entire versioned encoder
equals the original for arbitrary concrete Buffers; `encode_map` preserves the
compiler/Hom boundary. Production imports remain unchanged pending coordinated
integration and dependent receipts. This proof does not claim a meaningful
end-to-end performance improvement.

Reproduce with `lake build TlsMpc.Signal.PrivateBase64CountV2`, kernel Checks.lean,
`python3 .../check.py`, then `python3 .../compile.py` in a fresh compile stage.
The latter intentionally refuses to overwrite existing closures. Generated
artifacts/bytecode remain under .deps; receipts contain hashes and supported scope.
