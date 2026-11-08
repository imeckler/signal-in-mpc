# Owned API observation and queued translation boundary

The actual pinned `prost::Message::decode` (message.rs105–111) creates a local
record and local buffer, then `Self::merge(...).map(|_| message)`. Its input in
private net `decode_and_validate` is an immutable `&[u8]`. A returned Err does
not expose the partially mutated record or advanced local slice.

`DropObservation.lean` proves the actual translated U8 DropGuard destructor
clears contents, preserves any error and separate input suffix, and cannot
introduce another failure under the explicit U8 Vec content model. Only the
owned Result projection erases this mutation. It does not assert full native
string merge-state refinement or the complete native owned API theorem.

The latter still requires a trustworthy translation bridge:

- Generic actual Message::decode translates, but its call to merge with a
  mutable buffer destructures a triple while the generic Message dictionary's
  merge method returns a pair. `OwnedDecodeCore.lean` / `OwnedDecodeReference.lean`
  are unaccepted local drafts and are not imported by any proved module.
- Monomorphizing the actual WebSocketMessage::decode(&[u8]) call reaches an
  opaque Message::merge::<WebSocketMessage, &mut &[u8]> nested-reference signature
  failure. No generated Lean body has been manually repaired.
- A source-preserving typed LLBC specialization/inlining pass or isolated
  signature fix with a minimal regression remains queued. Source-owned API
  agreement is not inferred from the standalone erasure lemma.

The separate retain-Destruct translator candidate removes the previous missing
function-analysis errors by preserving actual destructor metadata. It then
reaches unsupported mutable-borrow Copy operations (actual DropGuard field) and
bottom/conditional cleanup joins in scalar regressions. It is not an accepted
complete drop translation. Its build/regression receipts preserve this failure.

Response work is paused here only because root prioritized the private-length
SignalMessage parser for the actual receive/DH path. The earlier component
receipt is bound to commit833ecfd; its historical scripts/source hashes are not
silently rewritten to match later experimental extraction profiles.

## Owned shared-slice transfer candidate

`check_owned_transfer.py` reproduces the new `owned_transferred` profile. It
mechanically replays the pinned Prost decode body with generic `M: Message +
Default` and `B: Buf`, transferring the local buffer into the same merge rather
than taking `&mut` of that local. The claimed specialization domain is only the
actual generated WebSocketMessage and contiguous immutable shared slice. It is
not a general Buf/Drop transformation. The native check compares 66,408 original
and replayed outcomes (1,723 complete records; 64,685 exact Debug errors).

The generated wrapper now has the correct pair return ABI and kernel-checks
unchanged. `OwnedTransferredReference.decode_normal_form` and `decode_error`
preserve outer failure/divergence and the exact owned error while erasing only
the partial message on Err. Merge remains an explicit dictionary operation;
there is no assumed merge/default correctness declaration in FunsExternal.
The unused generated external template is evidence, not an imported axiom.
The tiny Result.map model follows the native match and closure behavior.

This resolves the wrapper translation obstruction, not response refinement.
The source-preserving specialization remains an explicit translation boundary;
full schema/streaming composition and the actual std UTF8 raw-pointer body are
still open. Scoped String/Vec content and DecodeContext models retain the
successful bounded-allocation boundary. No full mutable merge-state claim is
made by an owned-error observation theorem.

The subsequent `owned_driver` profile includes the actual generic Prost
`Message::merge` body and uses the same scoped loop translator as the accepted
Signal parser. `OwnedDriverReference.key_total` connects its contiguous key
operation to the proved decoder with exact error and suffix, plus strict input
progress on success. `decode_actual_merge` installs that extracted default loop
under the owned wrapper. This does not supply a chat-schema dispatcher totality
premise or prove streaming agreement. The independent audit records this scope.
