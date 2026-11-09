import ChatResponseReferenceWork.StreamingV1.PrefixContext
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000

theorem native_tag_equality (tag : U32) (number : Nat) (small : number < 2^64) :
    TlsChatResponse.weq Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 tag.val) number =
      if tag.val = number then 255 else 0 := by
  unfold TlsChatResponse.weq
  rw [word_eq_value]
  have tagSmall : tag.val < 2^64 := by have bound := tag.bv.isLt; change tag.val < 2^32 at bound; omega
  have equal : BitVec.ofNat 64 tag.val = BitVec.ofNat 64 number ↔ tag.val = number := by
    constructor
    · intro bits
      have numeric := congrArg BitVec.toNat bits
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt tagSmall,Nat.mod_eq_of_lt small] using numeric
    · intro same; rw [same]
  simpa only [Word64.concrete,equal]


/-- Actual Core field-kind installation matches the native response schema.
The old list shape is explicit because the implementation uses zipWith select. -/
theorem key_field_recognition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (tag : U32) (inside : Bool)
    (modes : state.modes = lane 0) (depth : state.depth = 0)
    (inner : state.inner = if inside then 255 else 0) (kindShape : state.kinds.length = 4)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (newTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds =
      if inside then [0,if tag.val = 4 then 255 else 0,if tag.val = 3 then 255 else 0,if tag.val = 5 then 255 else 0]
      else [if tag.val = 3 then 255 else 0,0,0,0] := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    [ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
      (ByteAuth.concrete.and (ByteAuth.concrete.not state.inner)
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) 3)),
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
      (ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) 4)),
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
      (ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) 3)),
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
      (ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) 5))]
    state.kinds = _
  rw [modes,ended,depth,inner,newTag]
  have done : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0) 255 = 255 := rfl
  rw [done,choose_accept_exact _ _ (by simpa only [List.length_cons,List.length_nil] using kindShape.symm)]
  have top : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 0 0 = 255 := rfl
  have hot (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  rw [top,hot,hot,hot,hot,native_tag_equality tag 3 (by decide),
    native_tag_equality tag 4 (by decide),native_tag_equality tag 5 (by decide)]
  by_cases three : tag.val = 3 <;> by_cases four : tag.val = 4 <;> by_cases five : tag.val = 5 <;>
    cases inside <;> simp [three,four,five,ByteAuth.concrete]

theorem key_kinds_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (shape : state.kinds.length = 4) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds.length = 4 := by
  change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ [_,_,_,_] state.kinds).length = 4
  simp only [TlsWebSocketUpgrade.choose,List.length_zipWith,List.length_cons,List.length_nil,shape]
  rfl

theorem feed_kinds_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (shape : state.kinds.length = 4) :
    (feed state bytes).kinds.length = 4 := by
  induction bytes generalizing state with
  | nil => exact shape
  | cons byte rest ih => exact ih _ (key_kinds_shape state byte shape)

#print axioms native_tag_equality
#print axioms key_field_recognition
#print axioms key_kinds_shape
#print axioms feed_kinds_shape
end ChatResponseReference.StreamingV1
