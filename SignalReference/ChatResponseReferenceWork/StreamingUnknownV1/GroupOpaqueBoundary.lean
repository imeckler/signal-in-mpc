import ChatResponseReferenceWork.StreamingUnknownV1.GroupBoundaryRejection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- An actual opaque payload consuming exactly the private child still requires
its group end. Every byte value is covered; the final real payload byte rejects
without borrowing parent/capacity tail to close the group. -/
theorem group_opaque_at_child_end_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before : Slice U8) (remaining : Nat) (bounded : remaining ≤ 4096) (positive : 0 < remaining)
    (physical : remaining ≤ before.length) (modes : state.modes = lane 3)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (skip : state.skip = BitVec.ofNat 64 remaining)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  let payload := (contents before).take remaining
  have contentLength : (contents before).length = before.length := by simp only [contents,List.length_map]
  have payloadLength : payload.length = remaining := by simp only [payload,List.length_take,contentLength,Nat.min_eq_left physical]
  have nonempty : payload ≠ [] := by intro empty; have h := congrArg List.length empty; simp only [payloadLength,List.length_nil] at h; omega
  let leading := payload.dropLast
  let byte := payload.getLast nonempty
  have payloadSplit : leading++[byte] = payload := List.dropLast_concat_getLast nonempty
  have leadingLength : leading.length+1 = remaining := by
    have result := congrArg List.length payloadSplit
    simpa only [List.length_append,List.length_cons,List.length_nil,payloadLength] using result
  have mode := opaque_prefix_inside state leading remaining (by omega) (by omega) modes skip
  have scopeResult := opaque_scope_prefix state leading remaining remaining bounded positive (by omega) (by omega) modes skip inner counter
  have currentInner : (feed state leading).inner = 255 := by
    have result := scopeResult.2.1
    rw [if_neg (by omega : leading.length ≠ remaining)] at result
    exact result
  have currentCounter : (feed state leading).responseRemaining = BitVec.ofNat 64 1 := by
    rw [scopeResult.1]
    congr 1
    omega
  have nextNotTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state.depth 0 = 0 := by
    rw [opaque_depth_step _ byte mode.1,scopeResult.2.2]
    exact notTop
  have rejected := core_close_active_group_reject (feed state leading) byte currentInner currentCounter nextNotTop
  have span : contents before = leading++byte::((contents before).drop remaining) := by
    calc
      contents before = payload++((contents before).drop remaining) := (List.take_append_drop remaining (contents before)).symm
      _ = leading++byte::((contents before).drop remaining) := by rw [←payloadSplit]; simp only [List.append_assoc,List.singleton_append]
  rw [span]
  apply finish_invalid_sticky
  simp only [feed,List.foldl_append,List.foldl_cons]
  exact feed_invalid_sticky _ _ rejected

#print axioms group_opaque_at_child_end_reject
end ChatResponseReference.StreamingUnknownV1
