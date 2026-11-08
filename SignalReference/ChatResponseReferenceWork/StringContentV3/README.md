Candidate actual String content bridge. The generated computational declarations
are mechanically replayed from PartialMonoCandidate/GeneratedProst; no body is
corrected by hand. Replay changes import/namespace names, uses the identical
wire discriminant mapping with a unique instance name, and omits the unused
ill-typed Drop dictionary. Its actual standalone clear body remains present.

Generated/FunsExternal is a scoped executable model: String is Vec<u8> content,
UTF8 is the proved executable grammar, bounded allocation is the accepted Vec
model, mutable forwarding uses the grounded typed loan projection, and the
contiguous put call invokes the generated/proved guarded copier. Unsupported
receiver types fail closed. Arbitrary Buf and unsafe memory are outside scope.
The UTF8 error payload is unobserved by String merge and represented by Unit;
the actual InvalidString constructor and error/suffix effects remain explicit.

ControlReference proves exact String control over the actual byte merger,
including all Result outcomes. It also proves total clear and owned-error
observation, retaining the suffix even under that observation. This is not full
merge-state equality. CopierReference proves exact contiguous replacement,
including old-value clearing and the private Take inner suffix; its internal
limit carrier is restored as in the actual generated adapter.

The whole String wire theorem still needs composition of the byte merger with
the existing actual varint theorem and underflow/cast bounds. Schema, validation,
streaming and compiler response composition remain open. No source agreement
with std's optimized unsafe UTF8 body is claimed. check.py records the affected
kernel closure and explicit boundaries. Historical copier receipt is unchanged;
its files landed in mixed commit aacda3d during a shared-index race.
