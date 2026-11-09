# Compact admission and mixed exported feedback

New candidate runAdmit has592-byte input and582-byte output. It expands only the
same omitted group-tag high halves, calls unchanged actual Mux.runAdmit and
compacts the state. Input suffix is the private slot index, BE64 opaque ID and
computed validity byte. No payload or validity content is assumed canonical.

AdmissionCodec proves the exact992-byte original input expansion. AdmissionStep
proves the endpoint equals the encoded actual Mux.admit state, including all
original duplicate/free-slot/range/computed-validity checks and mutation behavior.
It uses the actual slot/state serialization proofs. CompiledAdmission proves
Hom and all-assignment exported AIG correctness, with no new correctness axiom.
AdmissionCarry proves exact582-byte carry plus10 fresh private payload bytes.

MixedFeed proves equality of all compact output bytes throughout arbitrary
interleavings of byte processing and admission from initialization, including
failed admission, malformed keys, partial/invalid schema input, sticky rejection,
reset, pending slot eligibility/consumption, queues, headers and event flags.
Byte outputs remain585 bytes; admissions output582 bytes; feedback takes the
first582 in either case. The endpoint operation schedule is public; all fields,
IDs, data, private length/boundary controls and validity are circuit inputs.
CompiledMixedFeed proves every exported bit after every arbitrary mixed prefix
agrees with the corresponding original Mux operation. The exact input and carry
laws connect that pointwise compiler result to the complete mixed trace.

Existing byte profile/checkpoint is unchanged:40,529 executed ANDs, depth275,
versus65,825/depth275. Admission exact gate/depth measurement is a separate next
step coordinated with TLS. No native benchmark, runtime promotion or shared
Core/Mux/Word64 change is included. This closes candidate process/admit/feed
circuit equivalence to the current Core/Mux; full pinned Rust schema/HTTP/
correlation refinement and its documented std/content/static-push boundaries
remain separate and open. It asserts no full ChatConnection scheduling/security
or successful-retry equivalence.

The first unfactored typed admission expansion check was interrupted through its
original PTY23043 (terminal1); a generic payload factoring removed the expensive
conversion. Only final separate-output checks are accepted. No live old writer
or competing object output is required by this receipt.
