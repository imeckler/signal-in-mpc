import TlsMpc.TlsChatResponse
namespace ChatResponseReference.Streaming
open TlsMpc Signal

/-- Once rejected, arbitrary subsequent input cannot restore validity. This
holds independently of schema invariants or the word operations. -/
theorem step_rejection_sticky {W : Type}
    (d : VarintDecode.Spqr.Ops (BitVec 8) W) (o : Word64.Ops (BitVec 8) W)
    (state : TlsChatResponse.State (BitVec 8) W) (byte : BitVec 8)
    (rejected : state.valid = 0) :
    (TlsChatResponse.step d o ByteAuth.concrete state byte).state.valid = 0 := by
  simp [TlsChatResponse.step, ByteAuth.concrete, rejected]

theorem finish_rejection_sticky {W : Type} (o : Word64.Ops (BitVec 8) W)
    (state : TlsChatResponse.State (BitVec 8) W) (rejected : state.valid = 0) :
    (TlsChatResponse.finish o ByteAuth.concrete state).valid = 0 ∧
    (TlsChatResponse.finish o ByteAuth.concrete state).successful = 0 := by
  simp [TlsChatResponse.finish, ByteAuth.concrete, rejected]

#print axioms step_rejection_sticky
#print axioms finish_rejection_sticky
end ChatResponseReference.Streaming
