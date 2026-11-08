import SkipPlanWork.Stack
import SkipTranslatorWork.SkipGroup

namespace LibSignalReference.Candidate.ProstSkipPlan
open TlsMpc TlsMpc.Signal Aeneas Aeneas.Std LoopSupportSkip
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 500000

theorem depth_predecessor (depth : BitVec 64) (hd : 0 < depth.toNat) :
    depth - 1 = BitVec.ofNat 64 (depth.toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by change 1 ≤ depth.toNat; omega)]
  simp only [BitVec.toNat_ofNat]
  have hb := depth.isLt
  rw [Nat.mod_eq_of_lt (by omega : depth.toNat - 1 < 2^64)]
  rfl

theorem lookup_current_group (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hd : 0 < state.depth.toNat) (hb : state.depth.toNat ≤ state.stack.length)
    (hs : state.stack.length ≤ 100) :
    ProtoParse.lookupWord Word64.concrete ByteAuth.concrete (state.depth - 1) 0 state.stack =
      state.stack[state.depth.toNat - 1]'(by omega) := by
  rw [depth_predecessor _ hd]
  simpa only [Nat.zero_add] using
    lookup_stack_get state.stack 0 (state.depth.toNat - 1) (by omega) (by omega)

/-- Closing-group acceptance matches the actual Rust loop body, using an ordinary
stack-content invariant rather than assuming equality of the two decisions. -/
theorem actual_end_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag inner : U32) (ctx : encoding.DecodeContext)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 4)
    (hd : 0 < state.depth.toNat) (hb : state.depth.toNat ≤ state.stack.length)
    (hs : state.stack.length ≤ 100)
    (hinner : (key.value >>> 3).toNat = inner.val)
    (hstack : (state.stack[state.depth.toNat - 1]'(by omega)).toNat = tag.val)
    (hdecode : encoding.decode_key sliceBuf before = .ok (.Ok (inner,.EndGroup),after)) :
    encoding.skip_field_loop.body sliceBuf tag ctx before =
      .ok (.done (if (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255
        then (.Ok (),after) else (.Err (decodeError .UnexpectedEndGroupTag),after))) := by
  have hn : state.depth ≠ 0 := by intro h; rw [h] at hd; contradiction
  rw [group_end_after _ _ _ _ _ hdecode,
    end_in_group _ _ _ _ hkey hvalue htag hkind hn,
    lookup_current_group _ hd hb hs]
  have he : (key.value >>> 3 = state.stack[state.depth.toNat - 1]'(by omega)) ↔ inner = tag := by
    constructor
    · intro h
      apply UScalar.eq_of_val_eq
      have hv := congrArg BitVec.toNat h
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      have hv := congrArg UScalar.val h
      omega
  simp only [he,groupClose]
  by_cases h : inner = tag <;> simp [h]

#print axioms depth_predecessor
#print axioms lookup_current_group
#print axioms actual_end_plan
end LibSignalReference.Candidate.ProstSkipPlan
