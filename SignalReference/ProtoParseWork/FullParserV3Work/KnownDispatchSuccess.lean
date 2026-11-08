import ProtoParseWork.FullParserV3Work.MessageReplacement
import ProtoParseWork.FullParserV3Work.DriverTrace
open Aeneas Aeneas.Std Result
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

/-- Exact successful actual generated-field observations, retaining the complete
message update and suffix as well as wire/decoder parameters. -/
inductive KnownSuccessResult (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8) : Prop where
  | scalar (ht : ScalarTag tag) (hw : wire = .Varint) (raw : U64)
      (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok raw,after))
      (hm : next = setScalar tag (UScalar.cast .U32 raw) message) : KnownSuccessResult message next tag wire before after
  | bytes (ht : BytesTag tag) (hw : wire = .LengthDelimited) (raw : U64) (remaining : Slice U8)
      (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok raw,remaining))
      (hn : raw.val ≤ remaining.length) (ha : after = drop remaining raw.val)
      (hm : next = setBytes tag (LibSignalReference.Candidate.ProstVecAdapter.fromSlice
        (ProstBytesCandidate.ContentModel.take remaining raw.val)) message) : KnownSuccessResult message next tag wire before after

theorem known_dispatch_success (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      DispatcherIntegration.sliceBuf message tag wire before ctx = .ok (.Ok (),next,after)) :
    KnownSuccessResult message next tag wire before after := by
  by_cases h1 : tag = 1#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.ratchet_key.getD (alloc.vec.Vec.new U8)) before ctx
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 1#u32 wire before ctx =
        .ok (r,{message with ratchet_key := some value},remaining) := by
      rw [ratchet_key_dispatch,hr]
      rfl
    have he := Result.ok.inj (hf.symm.trans hm)
    have hs := congrArg Prod.fst he
    change r = .Ok () at hs
    cases r with
    | Err e => cases hs
    | Ok u =>
      cases u
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      have ha := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      change remaining = after at ha
      change {message with ratchet_key := some value} = next at hn
      obtain ⟨hw,raw,rest,hd,hfit,hvalue,hafter⟩ := bytes_success_value wire (message.ratchet_key.getD (alloc.vec.Vec.new U8)) value before remaining ctx hr
      apply KnownSuccessResult.bytes (Or.inl rfl) hw raw rest hd hfit
      · rw [← ha]; exact hafter
      · rw [← hn,hvalue]
        simp [setBytes]
  by_cases h2 : tag = 2#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := uint32_merge_total wire (message.counter.getD 0#u32) before ctx
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 2#u32 wire before ctx =
        .ok (r,{message with counter := some value},remaining) := by
      rw [counter_dispatch,hr]
      rfl
    have he := Result.ok.inj (hf.symm.trans hm)
    have hs := congrArg Prod.fst he
    change r = .Ok () at hs
    cases r with
    | Err e => cases hs
    | Ok u =>
      cases u
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      have ha := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      change remaining = after at ha
      change {message with counter := some value} = next at hn
      obtain ⟨hw,raw,hd,hvalue⟩ := uint32_success_value wire (message.counter.getD 0#u32) value before remaining ctx hr
      apply KnownSuccessResult.scalar (Or.inl rfl) hw raw
      · simpa only [ha] using hd
      · rw [← hn,hvalue]
        simp [setScalar]
  by_cases h3 : tag = 3#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := uint32_merge_total wire (message.previous_counter.getD 0#u32) before ctx
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 3#u32 wire before ctx =
        .ok (r,{message with previous_counter := some value},remaining) := by
      rw [previous_counter_dispatch,hr]
      rfl
    have he := Result.ok.inj (hf.symm.trans hm)
    have hs := congrArg Prod.fst he
    change r = .Ok () at hs
    cases r with
    | Err e => cases hs
    | Ok u =>
      cases u
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      have ha := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      change remaining = after at ha
      change {message with previous_counter := some value} = next at hn
      obtain ⟨hw,raw,hd,hvalue⟩ := uint32_success_value wire (message.previous_counter.getD 0#u32) value before remaining ctx hr
      apply KnownSuccessResult.scalar (Or.inr rfl) hw raw
      · simpa only [ha] using hd
      · rw [← hn,hvalue]
        simp [setScalar]
  by_cases h4 : tag = 4#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.ciphertext.getD (alloc.vec.Vec.new U8)) before ctx
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 4#u32 wire before ctx =
        .ok (r,{message with ciphertext := some value},remaining) := by
      rw [ciphertext_dispatch,hr]
      rfl
    have he := Result.ok.inj (hf.symm.trans hm)
    have hs := congrArg Prod.fst he
    change r = .Ok () at hs
    cases r with
    | Err e => cases hs
    | Ok u =>
      cases u
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      have ha := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      change remaining = after at ha
      change {message with ciphertext := some value} = next at hn
      obtain ⟨hw,raw,rest,hd,hfit,hvalue,hafter⟩ := bytes_success_value wire (message.ciphertext.getD (alloc.vec.Vec.new U8)) value before remaining ctx hr
      apply KnownSuccessResult.bytes (Or.inr (Or.inl rfl)) hw raw rest hd hfit
      · rw [← ha]; exact hafter
      · rw [← hn,hvalue]
        simp [setBytes]
  by_cases h5 : tag = 5#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.pq_ratchet.getD (alloc.vec.Vec.new U8)) before ctx
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 5#u32 wire before ctx =
        .ok (r,{message with pq_ratchet := some value},remaining) := by
      rw [pq_ratchet_dispatch,hr]
      rfl
    have he := Result.ok.inj (hf.symm.trans hm)
    have hs := congrArg Prod.fst he
    change r = .Ok () at hs
    cases r with
    | Err e => cases hs
    | Ok u =>
      cases u
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      have ha := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      change remaining = after at ha
      change {message with pq_ratchet := some value} = next at hn
      obtain ⟨hw,raw,rest,hd,hfit,hvalue,hafter⟩ := bytes_success_value wire (message.pq_ratchet.getD (alloc.vec.Vec.new U8)) value before remaining ctx hr
      apply KnownSuccessResult.bytes (Or.inr (Or.inr (Or.inl rfl))) hw raw rest hd hfit
      · rw [← ha]; exact hafter
      · rw [← hn,hvalue]
        simp [setBytes]
  by_cases h6 : tag = 6#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.addresses.getD (alloc.vec.Vec.new U8)) before ctx
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 6#u32 wire before ctx =
        .ok (r,{message with addresses := some value},remaining) := by
      rw [addresses_dispatch,hr]
      rfl
    have he := Result.ok.inj (hf.symm.trans hm)
    have hs := congrArg Prod.fst he
    change r = .Ok () at hs
    cases r with
    | Err e => cases hs
    | Ok u =>
      cases u
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      have ha := congrArg (fun x : Status × Message × Slice U8 => x.2.2) he
      change remaining = after at ha
      change {message with addresses := some value} = next at hn
      obtain ⟨hw,raw,rest,hd,hfit,hvalue,hafter⟩ := bytes_success_value wire (message.addresses.getD (alloc.vec.Vec.new U8)) value before remaining ctx hr
      apply KnownSuccessResult.bytes (Or.inr (Or.inr (Or.inr rfl))) hw raw rest hd hfit
      · rw [← ha]; exact hafter
      · rw [← hn,hvalue]
        simp [setBytes]
  have hv : tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 := by omega
  rcases hv with h | h | h | h | h | h
  · exact False.elim (h1 (UScalar.eq_of_val_eq h))
  · exact False.elim (h2 (UScalar.eq_of_val_eq h))
  · exact False.elim (h3 (UScalar.eq_of_val_eq h))
  · exact False.elim (h4 (UScalar.eq_of_val_eq h))
  · exact False.elim (h5 (UScalar.eq_of_val_eq h))
  · exact False.elim (h6 (UScalar.eq_of_val_eq h))

#print axioms known_dispatch_success
end FullParserV3
