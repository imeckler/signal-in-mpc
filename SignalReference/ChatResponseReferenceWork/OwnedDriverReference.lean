import ChatResponseReferenceWork.GeneratedOwnedDriver.Funs
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std Result
namespace ChatResponseOwnedDriver
open ActualChatResponseOwned_driver
/-- Concrete contiguous input, with no synthetic tail reads. -/
def sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  {remaining := LibSignalReference.Candidate.ProstSkipBuf.remaining,
   chunk := LibSignalReference.Candidate.ProstSkipBuf.chunk,
   advance := LibSignalReference.Candidate.ProstSkipBuf.advance,
   has_remaining := fun bytes => .ok (0 < bytes.length)}
theorem slice_adapter : toSkipBuf sliceBuf =
    LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl
/-- Total actual key dependency, including rejection and exact suffix. Successful
keys consume at least one byte, furnishing the driver induction measure. -/
theorem key_total (before : Slice U8) :
    ∃ result after,
      LoopSupportSkip.encoding.decode_key
        LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (result,after) ∧
      prost.encoding.decode_key sliceBuf before = .ok
        ((match result with
          | .Ok (tag,wire) => .Ok (tag,wireFromSkip wire)
          | .Err error => .Err (SignalMessageIntegration.skipError error)),after) ∧
      after.length ≤ before.length ∧
      (∀ pair, result = .Ok pair → after.length < before.length) := by
  obtain ⟨result,after,hkey,hle,hstrict⟩ := FullParserV3.key_total before
  refine ⟨result,after,hkey,?_,hle,hstrict⟩
  unfold prost.encoding.decode_key
  rw [slice_adapter,hkey]
  rfl
/-- Install the extracted default merge, keeping actual dispatch and every
unrelated trait operation explicit. No field correctness is assumed here. -/
noncomputable def withDefaultMerge {M : Type} (mi : prost.message.Message M) :
    prost.message.Message M :=
  {mi with merge := prost.message.Message.merge.default mi}
/-- Owned wrapper connected to the actual extracted merge loop. This structural
identity includes key/field errors and outer failures; total chat-schema
termination/refinement is a separate obligation. -/
theorem decode_actual_merge {M B : Type} (mi : prost.message.Message M)
    (di : core.default.Default M) (bi : bytes.buf.buf_impl.Buf B) (buf : B) :
    owned_slice_replay.decode_buffer (withDefaultMerge mi) di bi buf = (do
      let initial ← di.default
      let (r, final) ← prost.message.Message.merge.default mi bi initial buf
      match r with
      | .Ok _ => .ok (.Ok final)
      | .Err error => .ok (.Err error)) := by
  unfold owned_slice_replay.decode_buffer withDefaultMerge
  cases hd : di.default <;> try rfl
  rename_i initial
  simp only [bind_tc_ok]
  cases hm : prost.message.Message.merge.default mi bi initial buf <;> try rfl
  rename_i pair
  rcases pair with ⟨r, final⟩
  simp only [bind_tc_ok]
  cases r <;> rfl
#print axioms key_total
#print axioms decode_actual_merge
end ChatResponseOwnedDriver
