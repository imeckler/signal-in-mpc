import ChatResponseReferenceWork.StreamingV1.ScalarUpdate
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000

private theorem native_tag_eq (tag : U32) (number : Nat) (small : number < 2^64) :
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

/-- The actual key terminal installs exactly the native dispatcher scalar-tag
classification: outer enum1; inner ID1/status2. Schema state validity is not a
premise. Native accepted key projection supplies newTag at composition sites. -/
theorem key_scalar_recognition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (tag : U32) (inside : Bool)
    (modes : state.modes = lane 0) (depth : state.depth = 0)
    (inner : state.inner = if inside then 255 else 0)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (newTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.scalarKnown =
      if (if inside then tag.val = 1 ∨ tag.val = 2 else tag.val = 1) then 255 else 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    (ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
      (TlsInner.select ByteAuth.concrete state.inner
        (TlsChatResponse.wmember Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) [1,2])
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) 1))) state.scalarKnown = _
  rw [modes,ended,depth,inner,newTag]
  have done : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0) 255 = 255 := rfl
  have top : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 0 0 = 255 := rfl
  have hot (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  rw [done,top,TlsInner.select_accept,hot]
  unfold TlsChatResponse.wmember
  simp only [List.map_cons,List.map_nil,TlsWebSocketUpgrade.any,List.foldl_cons,List.foldl_nil]
  rw [native_tag_eq tag 1 (by decide),native_tag_eq tag 2 (by decide)]
  by_cases one : tag.val = 1 <;> by_cases two : tag.val = 2 <;> cases inside <;>
    simp [one,two,TlsInner.select,TlsWebSocketUpgrade.either,ByteAuth.concrete]

#print axioms key_scalar_recognition
end ChatResponseReference.StreamingV1
