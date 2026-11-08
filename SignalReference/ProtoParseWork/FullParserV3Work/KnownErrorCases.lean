import ProtoParseWork.FullParserV3Work.KnownDispatchError
import ProtoParseWork.FullParserV3Work.WrongWirePrimitive
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 3000000

/-- Exhaustive actual known-field failures, retaining constructor parameters,
precise suffixes and successful length-prefix values on underflow. -/
inductive KnownErrorCase (error : prost.error.DecodeError) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8) : Prop where
  | scalarWrong (ht : ScalarTag tag) (hw : wire ≠ .Varint) (ha : after = before)
      (he : error = fieldError (LibSignalReference.Candidate.ProstField.decodeError
        (.UnexpectedWireType (toFieldWire wire) .Varint))) : KnownErrorCase error tag wire before after
  | bytesWrong (ht : BytesTag tag) (hw : wire ≠ .LengthDelimited) (ha : after = before)
      (he : error = LibSignalReference.Candidate.ProstBytes.decodeError
        (.UnexpectedWireType (toBytesWire wire) .LengthDelimited)) : KnownErrorCase error tag wire before after
  | scalarPayload (ht : ScalarTag tag) (hw : wire = .Varint)
      (he : error = fieldError (LibSignalReference.Candidate.ProstField.decodeError .InvalidVarint))
      (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err invalidError,after)) :
      KnownErrorCase error tag wire before after
  | bytesPayload (ht : BytesTag tag) (hw : wire = .LengthDelimited)
      (he : error = LibSignalReference.Candidate.ProstBytes.decodeError .InvalidVarint)
      (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err invalidError,after)) :
      KnownErrorCase error tag wire before after
  | bytesUnderflow (ht : BytesTag tag) (hw : wire = .LengthDelimited)
      (he : error = LibSignalReference.Candidate.ProstBytes.decodeError .BufferUnderflow) (raw : U64)
      (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok raw,after))
      (hn : after.length < raw.val) : KnownErrorCase error tag wire before after

theorem known_error_cases {error tag wire before after ctx}
    (origin : KnownErrorOrigin error tag wire before after ctx) : KnownErrorCase error tag wire before after := by
  cases origin with
  | scalar ht old value hd =>
    by_cases hw : wire = .Varint
    · subst wire
      obtain ⟨he,_,hp⟩ := scalar_payload_error old value before after ctx error hd
      exact .scalarPayload ht rfl he hp
    · rw [scalar_wrong_wire_actual wire old before ctx hw] at hd
      have he := Result.ok.inj hd
      exact .scalarWrong ht hw (congrArg (fun x => x.2.2) he).symm
        (core.result.Result.Err.inj (congrArg Prod.fst he)).symm
  | bytes ht old value hd =>
    by_cases hw : wire = .LengthDelimited
    · subst wire
      obtain ⟨_,cases⟩ := bytes_payload_error old value before after ctx error hd
      rcases cases with ⟨he,hp⟩ | ⟨he,raw,hp,hn⟩
      · exact .bytesPayload ht rfl he hp
      · exact .bytesUnderflow ht rfl he raw hp hn
    · rw [bytes_wrong_wire_actual wire old before ctx hw] at hd
      have he := Result.ok.inj hd
      exact .bytesWrong ht hw (congrArg (fun x => x.2.2) he).symm
        (core.result.Result.Err.inj (congrArg Prod.fst he)).symm

theorem actual_known_error_cases (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : prost.error.DecodeError) (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag wire before ctx = .ok (.Err error,next,after)) :
    KnownErrorCase error tag wire before after ∧ next = initializeMessage (BitVec.ofNat 64 tag.val) message :=
  ⟨known_error_cases (known_dispatch_error_origin message next tag wire before after ctx error ht hb hm),
    known_error_initialization message next tag wire before after ctx error ht hb hm⟩

#print axioms known_error_cases
#print axioms actual_known_error_cases
end FullParserV3
