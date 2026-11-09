import ChatResponseReferenceWork.StreamingUnknownV1.GroupRecognition
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def eraseGroupDepth (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) := {state with depth := 0}

/-- Non-key bytes before the private child boundary do not inspect group depth.
Only this proof-local depth projection is erased; errors, fields, event bits,
stack, counters and byte consumption remain exactly equal. -/
theorem nonkey_depth_projection (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (role : Nat) (nonkey : role = 1 ∨ role = 2 ∨ role = 3)
    (modes : state.modes = lane role) (kindShape : state.kinds.length = 4)
    (notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0) :
    TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (eraseGroupDepth state) byte =
      {TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte with
        state := eraseGroupDepth (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state} := by
  have laneOne : lane 1 = [0,255,0,0] := rfl
  have laneTwo : lane 2 = [0,0,255,0] := rfl
  have laneThree : lane 3 = [0,0,0,255] := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have weqZero : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 0 0 = 255 := rfl
  have rejectKinds (a b c d : BitVec 8) : TlsWebSocketUpgrade.choose ByteAuth.concrete 0 [a,b,c,d] state.kinds = state.kinds :=
    choose_reject_exact _ _ (by simpa only [List.length_cons,List.length_nil] using kindShape.symm)
  have writeZero (index tag : BitVec 64) : TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 0 index tag state.stack = state.stack := by
    simp only [TlsChatResponse.writeStack,zeroAnd,Word64.select_reject]
    exact List.zipIdx_map_fst 0 state.stack
  rcases nonkey with same | same | same <;> subst role <;>
    simp only [TlsChatResponse.step,eraseGroupDepth,modes,laneOne,laneTwo,laneThree,TlsWebSocketUpgrade.get,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,notClosing,
      zeroAnd,andZero,hotAnd,notZero,Word64.select_reject,TlsInner.select_reject,weqZero,rejectKinds,writeZero]

#print axioms nonkey_depth_projection
end ChatResponseReference.StreamingUnknownV1
