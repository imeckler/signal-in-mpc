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

Component export and compiled-cost checks now pass;1046 public numeric cases include three actual hashlib vectors and arbitrary-state differential cases. No native MPC or end-to-end performance improvement is claimed. The final carry-propagating addition is included in complete
sum/round/block measurements and will also be distinguished from the carry-save
pair itself. Production integration requires reviewed gains and dependent evidence.

Reproduce: lake build TlsMpc.Sha256CarrySave, then run Checks.lean through lake env
lean. Export.lean emits public legacy/carry component artifacts under explicit
profile selection; no share, secret-length or release API is introduced.


## Complete-block measurements and singleton packing

|Arbitrary-state one-block compression|Original|Carry-save|
|---|---:|---:|
|Optimized logical ANDs|59759|51945|
|Compiled triples with singleton fix|59759|51945|
|Compiled VM rounds|3212|3212|
|Local XORs|55549|63195|

The final carry propagation is included. Carry-save saves13.1% of logical ANDs,
but measured depth and VM rounds do not improve: the earlier predicted latency
benefit is withdrawn. SHA ripple chains overlap by bit, and other dependencies
remain. A parallel-prefix final-adder candidate is next; its extra ANDs must be
measured against complete-block depth, not inferred from a word microcase.

The carry-save pair costs62 ANDs at depth1; doubling carry words costs0 ANDs.
Five-term totals cost364→272 logical ANDs, depth61→60. Before the adapter fix,
56 singleton batches widened to default40-bit sbits and wasted2184 triples,
so the carry five-term component compiled to2456 rather than272. The new public
singleton pack shortcut removes this. Complete blocks each lose one39-triple
padding overhead. Old and fresh compiler closures/receipts remain separate.

The adapter's192 public width/output/consumption checks cover1/2/3/39/40/41/63/
64/65/127/128/129 lanes and inversion masks; the existing13348 packed/scalar
regression evaluations also pass. No protocol/security parameter or producer
SHA default changed. Full-service rebuild and production SHA integration remain
pending the measured combined trade-off and reviewed dependent evidence.
