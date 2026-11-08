import ProtoParseWork.FullParserV3Work.MessageReplacement
import ProtoParseWork.FullParserV3Work.DispatcherMutation
import ProtoParseWork.FullParserV3Work.ScalarPayloadError
import ProtoParseWork.FullParserV3Work.BytesPayloadError
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 3000000

/-- Actual source merger call responsible for a generated known-field error.
The complete message mutation is separately retained by known_error_initialization. -/
inductive KnownErrorOrigin (error : prost.error.DecodeError) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) : Prop where
  | scalar (ht : ScalarTag tag) (old value : U32)
      (hd : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx = .ok (.Err error,value,after)) :
      KnownErrorOrigin error tag wire before after ctx
  | bytes (ht : BytesTag tag) (old value : alloc.vec.Vec U8)
      (hd : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter DispatcherIntegration.sliceBuf
        wire old before ctx = .ok (.Err error,value,after)) : KnownErrorOrigin error tag wire before after ctx

theorem known_dispatch_error_origin (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : prost.error.DecodeError) (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag wire before ctx = .ok (.Err error,next,after)) :
    KnownErrorOrigin error tag wire before after ctx := by
  by_cases h1 : tag = 1#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.ratchet_key.getD (alloc.vec.Vec.new U8)) before ctx
    rw [ratchet_key_dispatch,hr] at hm
    simp only [bind_tc_ok] at hm
    have he := Result.ok.inj hm
    have hs := congrArg Prod.fst he
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have herr : e = error := core.result.Result.Err.inj hs
      have ha : remaining = after := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      rw [herr,ha] at hr
      exact KnownErrorOrigin.bytes (Or.inl rfl) _ value hr
  by_cases h2 : tag = 2#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := uint32_merge_total wire (message.counter.getD 0#u32) before ctx
    rw [counter_dispatch,hr] at hm
    simp only [bind_tc_ok] at hm
    have he := Result.ok.inj hm
    have hs := congrArg Prod.fst he
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have herr : e = error := core.result.Result.Err.inj hs
      have ha : remaining = after := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      rw [herr,ha] at hr
      exact KnownErrorOrigin.scalar (Or.inl rfl) _ value hr
  by_cases h3 : tag = 3#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := uint32_merge_total wire (message.previous_counter.getD 0#u32) before ctx
    rw [previous_counter_dispatch,hr] at hm
    simp only [bind_tc_ok] at hm
    have he := Result.ok.inj hm
    have hs := congrArg Prod.fst he
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have herr : e = error := core.result.Result.Err.inj hs
      have ha : remaining = after := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      rw [herr,ha] at hr
      exact KnownErrorOrigin.scalar (Or.inr rfl) _ value hr
  by_cases h4 : tag = 4#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.ciphertext.getD (alloc.vec.Vec.new U8)) before ctx
    rw [ciphertext_dispatch,hr] at hm
    simp only [bind_tc_ok] at hm
    have he := Result.ok.inj hm
    have hs := congrArg Prod.fst he
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have herr : e = error := core.result.Result.Err.inj hs
      have ha : remaining = after := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      rw [herr,ha] at hr
      exact KnownErrorOrigin.bytes (Or.inr (Or.inl rfl)) _ value hr
  by_cases h5 : tag = 5#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.pq_ratchet.getD (alloc.vec.Vec.new U8)) before ctx
    rw [pq_ratchet_dispatch,hr] at hm
    simp only [bind_tc_ok] at hm
    have he := Result.ok.inj hm
    have hs := congrArg Prod.fst he
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have herr : e = error := core.result.Result.Err.inj hs
      have ha : remaining = after := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      rw [herr,ha] at hr
      exact KnownErrorOrigin.bytes (Or.inr (Or.inr (Or.inl rfl))) _ value hr
  by_cases h6 : tag = 6#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.addresses.getD (alloc.vec.Vec.new U8)) before ctx
    rw [addresses_dispatch,hr] at hm
    simp only [bind_tc_ok] at hm
    have he := Result.ok.inj hm
    have hs := congrArg Prod.fst he
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have herr : e = error := core.result.Result.Err.inj hs
      have ha : remaining = after := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      rw [herr,ha] at hr
      exact KnownErrorOrigin.bytes (Or.inr (Or.inr (Or.inr rfl))) _ value hr
  have hv : tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 := by omega
  rcases hv with h | h | h | h | h | h
  · exact False.elim (h1 (UScalar.eq_of_val_eq h))
  · exact False.elim (h2 (UScalar.eq_of_val_eq h))
  · exact False.elim (h3 (UScalar.eq_of_val_eq h))
  · exact False.elim (h4 (UScalar.eq_of_val_eq h))
  · exact False.elim (h5 (UScalar.eq_of_val_eq h))
  · exact False.elim (h6 (UScalar.eq_of_val_eq h))

#print axioms known_dispatch_error_origin
end FullParserV3
