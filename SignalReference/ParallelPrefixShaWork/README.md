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

Proof checkpoint only: export43926 is pending, so no depth/AND/performance gain is
claimed here. Complete-block and final-adder cost comparison will choose whether
the extra gates are worthwhile for a supported profile. No native MPC/application
run or production integration occurred.
