# Carry-save SHA sums, isolated candidate

Sha256CarrySave replaces the five-operand round sum and four-operand schedule sum
with three-to-two carry-save reductions followed by a final carry-propagating
addition. Doubling the carry word uses the existing add primitive; its exported
cost must be measured rather than presumed free. Original Sha256 and all
producer imports/artifacts remain unchanged.

Kernel-checked natural-number identity is proved by binary strong induction,
then lifted to exact modulo2^32 arithmetic. It uses no SAT/native decision oracle
or new axiom. Full schedule, round, arbitrary-state/block compression equivalence,
Hom preservation and the numeric compiler endpoint are checked. Nine audited
endpoints use only propext/Classical.choice/Quot.sound.

Component export and compiled-cost checks are in progress. No depth reduction,
AND budget, native MPC or end-to-end performance improvement is claimed at this
proof checkpoint. The final carry-propagating addition is included in complete
sum/round/block measurements and will also be distinguished from the carry-save
pair itself. Production integration requires reviewed gains and dependent evidence.

Reproduce: lake build TlsMpc.Sha256CarrySave, then run Checks.lean through lake env
lean. Export.lean emits public legacy/carry component artifacts under explicit
profile selection; no share, secret-length or release API is introduced.
