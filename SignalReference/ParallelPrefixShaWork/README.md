# Parallel-prefix SHA final-adder candidate

The isolated Sklansky-style prefix scan combines affine Boolean carry functions
in a balanced tree. The final adder extracts32 one-bit flags, computes all prefix
carries, then packs sum flags. Packing uses only additions with disjoint known
bit positions; its exported/compiled AND cost must still be measured. Original
Sha256/default producer imports and frozen native artifacts are unchanged.

Kernel-checked arbitrary-word exact modulo2^32 addition follows from associative
carry-function composition, a generic prefix-scan theorem, and standard BitVec
carry/get-bit facts. No SAT/native decision oracle or new axiom is used. Hom,
wrapped concrete Ops equality, arbitrary-state compression equivalence and the
numeric compiler endpoint compose with the carry-save candidate. Seven audited
endpoints use only propext/Classical.choice/Quot.sound.

Bounded public numeric and actual compiler checks now pass526 cases, including
three actual hashlib vectors and arbitrary-state block comparisons. Singleton
packing fix is active in the fresh compiler closures. No native MPC/application
run or production integration occurred at this checkpoint.

|Component|Original AND/VM rounds|Prefix AND/VM rounds|
|---|---:|---:|
|Two-word final adder|91 /61|151 /6|
|Complete arbitrary-state block|59759 /3212|70777 /838|

The complete-block path combines proved carry-save nary sums and prefix binary
adders. It uses18.4% more logical ANDs than original, with73.9% fewer dependency
levels/compiled VM rounds. This is a measured circuit/compiler trade, not a WAN
throughput estimate. Original carry-only retains the gate-efficient51945AND /
3212round point. Production selection must bind the profile in metadata and
propagate it through actual private HMAC/HKDF/service exporters.

Commit aacda3d also includes12 independently validated parser-owned ContiguousPut
files due a shared-index race; those files were not authored/staged by this worker.
History is preserved by team agreement. Subsequent index mutations use the
shared fcntl lock and git commit --only with explicit owned paths.
