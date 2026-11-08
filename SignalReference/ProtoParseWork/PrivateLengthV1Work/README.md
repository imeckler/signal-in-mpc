# Private-length SignalMessage parser V1

This candidate adds a versioned parser without changing the accepted public-
length parser. `TlsMpc.Signal.PrivateProtoParseV1.parse` takes the entire wire
capacity, two shared BE16 actual-length bytes, and an upstream validity byte.
The target capacity is 256; the proved domain is every actual length n at most
the public capacity, with capacity at most 512. Length n is a logical parameter
of the refinement theorem, never a public production loop bound.

The wire is version || protobuf body || MAC8. MAC authentication remains
external. Status masks are canonical 0/255; an upstream byte other than 255
rejects. Field offsets remain body-relative: wire offset = body offset + 1.
Zero-based fields 0/3/4/5 are ratchet/ciphertext/PQ/addresses. Scalar metadata in
`state` retains the decoded u64; use its low 32 bits for native uint32 counters.
The 90-byte released output already truncates those counters correctly.

`Parsed` exposes state, wireLength, bodyLength, valid and released metadata.
`parseCore` returns valid :: metadata. `Parsed.map`, `parse_map`,
`parseCore_map` and `compiled_parseCore_correct` are available after importing
`TlsMpc.Signal.PrivateProtoParseV1Proofs`. Its `compiledBit` is an explicit
wrapper around the existing AIG compiler/evaluator, used to factor dependent
vector types; it is not an alternate interpreter.

Bytes at/past the secret body end are replaced by continuation-only 0x80 before
decoder-table construction. They cannot finish truncated varints or contribute
payload. Payload bounds, failure cursors and the contiguous fast-path guard use
the private end. Scan slots past that end stutter. The fixed public stack is
related by an explicit zero extension to the accepted parser's shorter stack;
unaddressable tail writes are disabled. Metadata reads have the same private
end, retain the original cursor on rejection, and cannot authorize a wrapping
addition.

Theorems, including every malformed/duplicate/unknown/group outcome:

- `Scan.parseBody_take`: exact body state, fields, cursor and group depth;
  only an unaddressable zero stack tail extends the representation.
- `Scan.padding_noninterference` and `Wire.padding_noninterference`:
  capacity padding cannot affect state/production output respectively.
- `Read.read_take`: exact status/cursor/data for every shared read cursor,
  including out-of-bounds candidates, with no field-validity premise.
- `Wire.parseCore_take`: complete BE16 framing, version/body/MAC positioning,
  acceptance and released metadata equal the accepted parser on `take n` when
  upstream is 255. `core_projection` retains arbitrary upstream validity.
- `ActualBody.actual_private_body`: the accepted actual Rust default-merge
  theorem instantiated on the private prefix, with trace and exact suffix.
- `CompiledActual.compiled_actual_private_parser`: compiled production output
  plus raw private state linked to the actual Rust observation. It retains
  error constructors/parameters, mutated Options, and EOF-vs-active status via
  the unchanged `ParserObservation`. `upstream_rejection` proves all-zero
  output for rejected upstream validity.

All printed endpoints use only propext, Classical.choice and Quot.sound.
No primitive/parser correctness or termination axiom is added; no success-only
restriction is used. The inherited source/model boundary remains explicit:
actual extracted Message::merge.default with the actual generated dispatcher,
an explicit six-None initial record, recursion budget 100, contiguous bounded
slice, and modeled successful bounded allocation/content operations. Diagnostic
stack text alone is quotiented by the accepted observation. This is not a new
claim about Message::decode/Default wrappers, MAC authentication, the complete
receive transition, or Signal session security.

`audit.py` performs one isolated source-hash-bound check of the new proof
closure, verifies the inherited accepted source/object receipt, and rejects any
non-foundational printed axiom. Build/vendor trees and logs are excluded. The
initial receipts are historical checkpoint evidence; the final proof report
binds the completed source snapshot. Independent root review remains separate.
A large interpreted fixture run hit its explicit 120-second limit and produced
no correctness result; the universal proofs do not rely on it. Native capacity-
256 receive integration validation is owned by the crypto worker.
