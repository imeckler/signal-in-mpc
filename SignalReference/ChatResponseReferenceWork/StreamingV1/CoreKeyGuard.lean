import ChatResponseReferenceWork.StreamingV1.KeyGuard
import ChatResponseReferenceWork.StreamingV1.RejectionClosure
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem core_common_key_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (invalid : commonKey (coreDecoded state byte) = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  let decoded := coreDecoded state byte
  have common : ByteAuth.concrete.and (Word64.concrete.ule decoded (Word64.concrete.const 4294967295))
      (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
        (Word64.concrete.shift decoded 3) 0))
        (Word64.concrete.ule (Word64.concrete.band decoded (Word64.concrete.const 7)) (Word64.concrete.const 5))) = 0 := by
    have hot (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
    simpa only [commonKey,LibSignalReference.Candidate.ProstSkipKey.keyFields,hot,decoded,TlsChatResponse.weq] using invalid
  have bad (rest : BitVec 8) :
      ByteAuth.concrete.and (Word64.concrete.ule decoded (Word64.concrete.const 4294967295))
      (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
        (Word64.concrete.shift decoded 3) 0))
        (ByteAuth.concrete.and (Word64.concrete.ule (Word64.concrete.band decoded (Word64.concrete.const 7))
          (Word64.concrete.const 5)) rest)) = 0 := by
    change _ &&& (_ &&& (_ &&& rest)) = 0
    change _ &&& (_ &&& _) = 0 at common
    have product := congrArg (fun x : BitVec 8 => x &&& rest) common
    have zero : (0 : BitVec 8) &&& rest = 0 := BitVec.zero_and
    rw [zero] at product
    simpa only [BitVec.and_assoc] using product
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.budget 0))
        (ByteAuth.concrete.and _
          (ByteAuth.concrete.and
            (ByteAuth.concrete.not (ByteAuth.concrete.and
              (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
                (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
              (ByteAuth.concrete.not (ByteAuth.concrete.and
                (Word64.concrete.ule decoded (Word64.concrete.const 4294967295))
                (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
                  (Word64.concrete.shift decoded 3) 0))
                  (ByteAuth.concrete.and (Word64.concrete.ule (Word64.concrete.band decoded (Word64.concrete.const 7))
                    (Word64.concrete.const 5)) _)))))) _))))) = 0
  rw [bad,modes,ended]
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have hot : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0) 255 = 255 := rfl
  have andHot : ByteAuth.concrete.and 255 255 = 255 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  rw [notZero,hot,andHot,notHot]
  simp only [zeroAnd,andZero]

open Aeneas Aeneas.Std LibSignalReference.Candidate.ProstSkipKey
/-- All native key-validation error constructors force actual Core rejection. -/
theorem native_key_failure_core (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (native : U64) (error : LoopSupportSkip.error.DecodeError)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (value : native.bv = coreDecoded state byte)
    (rejected : keyResult native = .Err error) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  apply core_common_key_reject state byte modes terminal
  rw [←value]
  exact native_key_rejected_common native error rejected

/-- Native key validation failure remains rejected after arbitrary remaining
bytes and finalization; error contents/cursor remain in the native key bridge. -/
theorem native_key_failure_tail (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (tail : List (BitVec 8)) (native : U64) (error : LoopSupportSkip.error.DecodeError)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (value : native.bv = coreDecoded state byte)
    (rejected : keyResult native = .Err error) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (byte::tail))).valid = 0 := by
  apply finish_invalid_sticky
  exact feed_invalid_sticky _ tail (native_key_failure_core state byte native error modes terminal value rejected)

#print axioms core_common_key_reject
#print axioms native_key_failure_core
#print axioms native_key_failure_tail
end ChatResponseReference.StreamingV1
