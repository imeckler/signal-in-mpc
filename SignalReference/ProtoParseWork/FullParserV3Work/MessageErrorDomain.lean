import ProtoParseWork.FullParserV3Work.KnownErrorDomain
import ProtoParseWork.FullParserV3Work.DriverTrace
open Aeneas Aeneas.Std Result
open SignalMessageIntegration DispatcherIntegration
namespace FullParserV3.Observed
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem unknown_status_represented (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (status : Status) (htag : 6 < tag.val)
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      DispatcherIntegration.sliceBuf message tag wire before ctx = ok (status,next,after)) : SignalRepresented status := by
  obtain ⟨result,hsem,hskip,_⟩ := skip_field_total (toSkipWire wire) tag ctx.recurse_count before
  rcases result with ⟨r,remaining⟩
  have hs := skip_errors_represented hsem
  rw [unknown_dispatch _ _ _ _ _ _ htag] at hm
  unfold prost.encoding.skip_field at hm
  rw [skip_slice_adapter,hskip] at hm
  cases r with
  | Ok u => cases u; cases hm; exact ⟨⟨0,0⟩,rfl⟩
  | Err e => cases hm; exact hs

theorem message_status_represented (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (status : Status) (ht : 0 < tag.val)
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      DispatcherIntegration.sliceBuf message tag wire before ctx = ok (status,next,after)) : SignalRepresented status := by
  by_cases h1 : tag = 1#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.ratchet_key.getD (alloc.vec.Vec.new U8)) before ctx
    have hs := bytes_status_represented wire (message.ratchet_key.getD (alloc.vec.Vec.new U8)) value before remaining ctx r hr
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 1#u32 wire before ctx =
        ok (r,{message with ratchet_key := some value},remaining) := by
      rw [ratchet_key_dispatch,hr]
      rfl
    have he := congrArg (fun x : Status × Message × Slice U8 => x.1) (Result.ok.inj (hf.symm.trans hm))
    change r = status at he
    rw [←he]
    exact hs
  by_cases h2 : tag = 2#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := uint32_merge_total wire (message.counter.getD 0#u32) before ctx
    have hs := uint32_status_represented wire (message.counter.getD 0#u32) value before remaining ctx r hr
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 2#u32 wire before ctx =
        ok (r,{message with counter := some value},remaining) := by
      rw [counter_dispatch,hr]
      rfl
    have he := congrArg (fun x : Status × Message × Slice U8 => x.1) (Result.ok.inj (hf.symm.trans hm))
    change r = status at he
    rw [←he]
    exact hs
  by_cases h3 : tag = 3#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := uint32_merge_total wire (message.previous_counter.getD 0#u32) before ctx
    have hs := uint32_status_represented wire (message.previous_counter.getD 0#u32) value before remaining ctx r hr
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 3#u32 wire before ctx =
        ok (r,{message with previous_counter := some value},remaining) := by
      rw [previous_counter_dispatch,hr]
      rfl
    have he := congrArg (fun x : Status × Message × Slice U8 => x.1) (Result.ok.inj (hf.symm.trans hm))
    change r = status at he
    rw [←he]
    exact hs
  by_cases h4 : tag = 4#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.ciphertext.getD (alloc.vec.Vec.new U8)) before ctx
    have hs := bytes_status_represented wire (message.ciphertext.getD (alloc.vec.Vec.new U8)) value before remaining ctx r hr
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 4#u32 wire before ctx =
        ok (r,{message with ciphertext := some value},remaining) := by
      rw [ciphertext_dispatch,hr]
      rfl
    have he := congrArg (fun x : Status × Message × Slice U8 => x.1) (Result.ok.inj (hf.symm.trans hm))
    change r = status at he
    rw [←he]
    exact hs
  by_cases h5 : tag = 5#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.pq_ratchet.getD (alloc.vec.Vec.new U8)) before ctx
    have hs := bytes_status_represented wire (message.pq_ratchet.getD (alloc.vec.Vec.new U8)) value before remaining ctx r hr
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 5#u32 wire before ctx =
        ok (r,{message with pq_ratchet := some value},remaining) := by
      rw [pq_ratchet_dispatch,hr]
      rfl
    have he := congrArg (fun x : Status × Message × Slice U8 => x.1) (Result.ok.inj (hf.symm.trans hm))
    change r = status at he
    rw [←he]
    exact hs
  by_cases h6 : tag = 6#u32
  · subst tag
    obtain ⟨r,value,remaining,hr,_⟩ := bytes_merge_total wire (message.addresses.getD (alloc.vec.Vec.new U8)) before ctx
    have hs := bytes_status_represented wire (message.addresses.getD (alloc.vec.Vec.new U8)) value before remaining ctx r hr
    have hf : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf message 6#u32 wire before ctx =
        ok (r,{message with addresses := some value},remaining) := by
      rw [addresses_dispatch,hr]
      rfl
    have he := congrArg (fun x : Status × Message × Slice U8 => x.1) (Result.ok.inj (hf.symm.trans hm))
    change r = status at he
    rw [←he]
    exact hs
  have htag : 6 < tag.val := by
    by_contra hn
    have hv : tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 := by omega
    rcases hv with h | h | h | h | h | h
    · apply h1; apply UScalar.eq_of_val_eq; change tag.val = 1; exact h
    · apply h2; apply UScalar.eq_of_val_eq; change tag.val = 2; exact h
    · apply h3; apply UScalar.eq_of_val_eq; change tag.val = 3; exact h
    · apply h4; apply UScalar.eq_of_val_eq; change tag.val = 4; exact h
    · apply h5; apply UScalar.eq_of_val_eq; change tag.val = 5; exact h
    · apply h6; apply UScalar.eq_of_val_eq; change tag.val = 6; exact h
  exact unknown_status_represented message next tag wire before after ctx status htag hm


#print axioms message_status_represented
end FullParserV3.Observed
