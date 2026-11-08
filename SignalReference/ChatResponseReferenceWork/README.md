# Chat response reference candidate

This work targets the pinned libsignal v0.106.1 ChatConnection protobuf response,
using the net build's `bytes::Bytes` generator option. It does **not** yet prove
the complete streaming response parser or the transport/correlation wrapper.
The accepted bounded SignalMessage result is independent and unchanged.

Proved components:

- `Uint64Reference`: actual Prost uint64 merge against the accepted bounded
  contiguous decoder, including overflow, wire errors, unchanged prior value on
  error, full-width success and exact suffix.
- `Utf8Spec` / `Utf8Machine`: TLS's existing byte machine agrees with an
  executable Unicode byte grammar for arbitrary byte lists, including malformed
  and truncated inputs. The transition proof reduces in Lean's kernel.
- `StatusReference`: actual http StatusCode constructor, access and success
  predicate, plus actual checked u32 narrowing, with all rejection outcomes.
- `ValidationReference`: actual envelope validation control flow, including
  unknown/default/out-of-enum types and absent/conflicting payloads. The input
  is an explicitly already decoded schema record. This is not parser validity.
- `SliceMetadataReference`: typed shared-byte-slice metadata lowering agrees
  with the slice length. Negative regression rejects u16 slices and raw pointers.

`replay_validation.py` copies the two private validation enums and the exact
suffix of pinned `decode_and_validate`. Its sole computational boundary change
replaces the decoding statement with a decoded-record parameter. The receipt
records original/suffix/output hashes. It does not call the private net API.
The generated implementations are translated without manual body corrections.

Models are executable definitions, not correctness axioms: immutable Bytes is
its byte contents under successful bounded allocation; generic Option/Result
and Range forward their supplied dictionaries; the selected scalar checked cast
uses Aeneas's existing model. NonZero retains scalar contents and its modeled
constructor checks zero at the U16 instantiation. Arbitrary external NonZero
values and niche layout are not claimed valid. Error payloads retain the actual
extracted Prost error type. Allocation/refcounts/layout are outside observation.

Translator candidates remain explicit: envelope replay/dispatch uses the
existing FnItem candidate; status uses this directory's naming-only candidate
(duplicate trait-parent field disambiguation and monomorphized variable naming).
Neither candidate is silently promoted to the pinned release. Receipts record
binary/LLBC/generated hashes. `TranslatorCandidate/build.py` checks that all
other translator source files remain unchanged.

Open obligations:

1. Actual generated schema/default/submessage merge, `bytes::Bytes` primitive
   composition, duplicates and complete bounded scan versus TLS streaming state.
2. Actual Prost string error mutation: default Charon drops omit DropGuard.clear;
   precise-drop extraction retains it, but Aeneas function analysis currently
   fails on the resulting destructor/constructor dependencies. No complete
   string mutation theorem uses the drop-omitting extraction.
3. Rust's optimized std UTF8 validator body uses raw read-only slice pointers
   and word loads beyond the typed metadata lowering. The grammar/machine proof
   does not discharge this std-body bridge.
4. HTTP header parsing/Unicode trim and complete schema validation composition;
   response ID presence and private pending-request correlation; private-length
   and compiler endpoint composition. Transport frame state is a separate stage.

Reproduction uses `extract.py PROFILE`, `translate.py PROFILE`, and `check.py`
with modules explicitly listed. Metadata additionally runs
`lower_slice_metadata.py PROFILE` and `translate.py PROFILE --lowered`.
Artifacts, vendor trees, binaries, build products and logs are excluded. A
separate absolute `CHAT_RESPONSE_OUTPUT_ROOT` avoids competing `.olean` writes.
The bounded component audit receipt lists precisely checked modules and hashes;
it is not an acceptance receipt for the complete response parser.
