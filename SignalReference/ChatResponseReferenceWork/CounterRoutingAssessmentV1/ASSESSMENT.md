# Bounded counter/routing assessment

This is resource attribution only. No additional parser optimization, native
benchmark, production change or whole-parser count/depth improvement is claimed.
The proved/measured stack32 byte candidate remains40,529 ANDs/depth275; its mixed
admit/feed compiler relation and admission1,043AND/depth25 are unchanged.

Exact standalone exported helper counts:

| Helper | Executed AND | AND depth |
| --- | ---: | ---: |
| uint64 decrement,64-bit output |124|124|
| modulo13 decrement,13 effective output bits padded to16 |22|22|
| full64≤full64 |253|127|
| full64≤public-width13 private bound, existing subtract comparator |151|76|
| high51-zero guard plus low13 comparator, same input widths |100|26|
| unchanged Core UTF8 byte-state step |983|136|

The decrement rows have different arithmetic/observation domains. They do not
establish a parser replacement. The guarded comparator is an unproved prototype
here: it retains an explicit high-bit rejection guard, and must be proved equal
to the existing comparator for every64-bit left operand and every13-bit right
operand before use. No sampled test or assumed equality discharges that gap.
Graphs are compiled from the recorded source; artifact/compiler/backend hashes
and honest memory bounds appear in micro-profile-audit.json. All jobs terminal.

Read-only exact attribution of the frozen whole byte graph finds:

| Output cone | Maximum AND depth | Exclusive output AND nodes |
| --- | ---: | ---: |
| group stack |26|17,804|
| budget |134|192|
| response remaining |136|384|
| skip |137|637|
| UTF/header |144|579|
| slot/queue state |275|468|
| event masks |273|88|

The full validity cone reaches272; slot/queue updates add3. Stack writes remain
the largest gate target, but do not explain critical depth. Fanin/exclusive
counts are not additive: these are output-pruning cones, not removable costs in
the stateful implementation. The complete cone table is in output-cones.json.

Next depth opportunity is bounded comparison, rather than simple unrolling.
Current Core computes available length by64-bit decrement, then compares a full
untrusted decoded length to it through another subtract chain. Live bounded
contiguous parsing permits capacity4096 (13bits), but malformed lengths must
still reject their high bits. Proof obligations are actual reachable bounds,
all error/underflow paths, exact continuation/carry and the chosen internal
state encoding. Existing rejected-state stack bisimulation does not establish
counter compression; no failed counter record may be silently discarded.
Status/type fields are explicitly low32 writes in Core and may offer a simpler
permanent-zero invariant; a new whole-feed proof/profile would still be needed.

Opaque bytes still route through generic parsing/UTF/header circuitry. Simply
skipping a privately selected branch would not preserve privacy or remove its
oblivious mux cost. A smaller source-preserving opportunity is replacing UTF8
range-membership chains with exact byte-class bit predicates. The unchanged
UTF helper itself has136 depth, so it can become a bottleneck even after counter
work. Finite all256-byte class equalities and an exact full-state step/feed proof
would preserve malformed/truncated UTF8, full valid Unicode and header behavior;
no ASCII-only or success-only restriction is proposed. None is implemented here.

Recommendation: retain the proved stack candidate, finish the actual response
schema/HTTP/correlation source composition now, then consider bounded comparator
and exact UTF class replacement with new resource measurements and feed proofs.
No further export/native jobs are required for this assessment.
