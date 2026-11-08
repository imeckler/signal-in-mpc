import ProtoParseWork.FullParserV3Work.KnownSuccess
import ProtoParseWork.FullParserV3Work.FieldProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

def ScalarTag (tag : U32) : Prop := tag = 2#u32 ∨ tag = 3#u32
def BytesTag (tag : U32) : Prop := tag = 1#u32 ∨ tag = 4#u32 ∨ tag = 5#u32 ∨ tag = 6#u32

def setScalar (tag : U32) (value : U32) (m : proto.wire.SignalMessage) : proto.wire.SignalMessage :=
  {m with counter := if tag.val = 2 then some value else m.counter, previous_counter := if tag.val = 3 then some value else m.previous_counter}

def setBytes (tag : U32) (value : alloc.vec.Vec U8) (m : proto.wire.SignalMessage) : proto.wire.SignalMessage :=
  {m with ratchet_key := if tag.val = 1 then some value else m.ratchet_key, ciphertext := if tag.val = 4 then some value else m.ciphertext, pq_ratchet := if tag.val = 5 then some value else m.pq_ratchet, addresses := if tag.val = 6 then some value else m.addresses}

theorem scalar_replace_view (body : Slice U8) (tag : U32) (raw : U64) (stop : BitVec 64)
    (message : proto.wire.SignalMessage) (ht : ScalarTag tag) :
    replaceMessage body (BitVec.ofNat 64 tag.val) ⟨255,stop,raw.bv⟩ message =
      setScalar tag (UScalar.cast .U32 raw) message := by
  rcases ht with rfl | rfl
  all_goals simp [replaceMessage,setScalar]
  all_goals exact scalar_view_value raw stop

theorem bytes_replace_view (body : Slice U8) (tag : U32) (raw : U64) (offset : Nat)
    (message : proto.wire.SignalMessage) (ht : BytesTag tag) (ho : offset < 2^64) :
    replaceMessage body (BitVec.ofNat 64 tag.val) ⟨255,BitVec.ofNat 64 offset,raw.bv⟩ message =
      setBytes tag (LibSignalReference.Candidate.ProstVecAdapter.fromSlice
        (ProstBytesCandidate.ContentModel.take (ProstBytesCandidate.ContentModel.drop body offset) raw.val)) message := by
  rcases ht with rfl | rfl | rfl | rfl
  all_goals simp [replaceMessage,setBytes]
  all_goals exact bytes_view_value body offset ho raw

#print axioms scalar_replace_view
#print axioms bytes_replace_view
end FullParserV3
