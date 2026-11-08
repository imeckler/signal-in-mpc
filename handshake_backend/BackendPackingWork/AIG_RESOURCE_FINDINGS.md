# Immutable nonempty-service circuit resources

The existing260/80 service Boolean artifact has25,315,873 nodes. Existing adapter
XOR recovery and reachability already reduce its25,310,216 raw AND nodes to
6,738,497 executed ANDs and6,578,452 local XORs, leaving11,993,272 nodes unreachable.
These are different quantities: dead/raw nodes burden export/loading but do not
consume triples in the optimized adapter.

The optimized DAG has114,049 AND dependency levels. The compiler receipt reports
at most6,769,205 bit triples,122,243 VM rounds,20,404 integer multiplications and
1,787 integer daBits for the entire mixed function. Circuit depth, actual compiled
VM rounds, and measured network rounds/traffic must remain distinct. This scan
introduces no WAN throughput or per-level RTT assumption.

Fixed-DAG grouping already has one AND group per dependency level. Its64-lane
packing uses173,314 AND batches (60.75% occupancy); local XOR uses1,027,737 batches
(10.00%). Packing improves VM/register work; it does not pack independent GF128
share transmissions into one network bit. Changing lane width cannot remove
the114,049 dependent AND levels or the logical triple demand.

Priority is therefore source-level serial-dependency and gate-count attribution,
while preserving existing XOR recovery. SHA/HMAC/KDF and ripple additions are
hypotheses supported by other module counts, not attribution from this flattened
artifact. A concrete owned candidate is PrivateBase64.count: its sequential
16-bit masked additions can be replaced by a balanced sum while preserving
modulo65536 semantics, arbitrary remainder behavior and public-length wrapping.
It will remain isolated until a total concrete-equivalence proof and exported/
compiled comparisons pass. Crypto owns the producer; its original modules and
compiled artifact remain unchanged.

The bounded-memory scanner is a public diagnostic, not an execution/validation
replacement. One hundred generated DAGs match existing aig.statistics and
packing plans exactly. The real artifact checksum matches the pinned compiler
receipt; scan runtime9.58s and peak679.7MiB. The initial time(1) wrapper could not
query kern.clockrate under the sandbox; a fresh subprocess/resource run then
completed with exit0 and recorded authoritative counters. No application/MPC
run was repeated. See service-aig-resources.json and aig-resource-scan-checks.json.
