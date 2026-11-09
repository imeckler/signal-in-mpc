import ChatResponseReferenceWork.StreamingUnknownV1.GroupStackWrite
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Actual Core group-start terminal writes its decoded source tag at the old
depth. This describes computation even on a rejected state; validity is proved
separately, so malformed inputs do not disappear from the observation. -/
theorem native_group_push_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,.StartGroup)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack =
      TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 255 state.depth (BitVec.ofNat 64 tag.val) state.stack := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  have kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const 3 := by
    rw [decoded]; exact native_key_kind native tag .StartGroup accepted
  have newTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]; exact native_key_tag native tag .StartGroup accepted
  change TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
        (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3))
    state.depth (Word64.concrete.shift (coreDecoded state byte) 3) state.stack = _
  rw [modes,ended,kind,newTag]
  rfl

/-- Actual push preserves every older active slot and installs exactly the new
source group tag. Future matching ends therefore read a witnessed parent tag. -/
theorem native_group_push_slot (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (depth slot : Nat)
    (shape : state.stack.length = 100) (bound : depth < 100) (slotBound : slot < 100)
    (depthEq : state.depth = BitVec.ofNat 64 depth) (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,.StartGroup)) :
    ((TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack)[slot]'(by
      simpa only [native_group_push_stack state byte native tag modes terminal decoded accepted,TlsChatResponse.writeStack,List.length_map,List.length_zipIdx,shape] using slotBound) =
      if depth = slot then BitVec.ofNat 64 tag.val else state.stack[slot]'(by omega) := by
  simpa only [native_group_push_stack state byte native tag modes terminal decoded accepted,depthEq] using
    group_stack_write_slot state.stack depth slot (BitVec.ofNat 64 tag.val) (by omega) bound (by omega)

#print axioms native_group_push_stack
#print axioms native_group_push_slot
end ChatResponseReference.StreamingUnknownV1
