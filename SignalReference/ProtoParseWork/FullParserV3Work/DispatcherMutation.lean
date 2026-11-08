import ProtoParseWork.FullParserV3Work.FieldProjection
import ProtoParseWork.FullParserV3Work.ErrorMutation
import ProtoParseWork.FullParserV3Work.DriverTrace
open Aeneas Aeneas.Std Result
namespace FullParserV3
open DispatcherIntegration SignalMessageIntegration
set_option maxHeartbeats 2000000

/-- On every known-field failure the actual generated dispatcher mutates all
six fields exactly by get-or-insert; existing values and unrelated fields remain
in the observed record. No failed record is replaced with success. -/
theorem known_error_initialization (message next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : prost.error.DecodeError)
    (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      DispatcherIntegration.sliceBuf message tag wire before ctx = .ok (.Err error,next,after)) :
    next = initializeMessage (BitVec.ofNat 64 tag.val) message := by
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
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have hv := bytes_error_value wire (message.ratchet_key.getD (alloc.vec.Vec.new U8)) value before remaining ctx e hr
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      change {message with ratchet_key := some value} = next at hn
      rw [← hn,hv]
      simp [initializeMessage]
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
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have hv := uint32_error_value wire (message.counter.getD 0#u32) value before remaining ctx e hr
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      change {message with counter := some value} = next at hn
      rw [← hn,hv]
      simp [initializeMessage]
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
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have hv := uint32_error_value wire (message.previous_counter.getD 0#u32) value before remaining ctx e hr
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      change {message with previous_counter := some value} = next at hn
      rw [← hn,hv]
      simp [initializeMessage]
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
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have hv := bytes_error_value wire (message.ciphertext.getD (alloc.vec.Vec.new U8)) value before remaining ctx e hr
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      change {message with ciphertext := some value} = next at hn
      rw [← hn,hv]
      simp [initializeMessage]
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
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have hv := bytes_error_value wire (message.pq_ratchet.getD (alloc.vec.Vec.new U8)) value before remaining ctx e hr
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      change {message with pq_ratchet := some value} = next at hn
      rw [← hn,hv]
      simp [initializeMessage]
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
    change r = .Err error at hs
    cases r with
    | Ok u => cases hs
    | Err e =>
      have hv := bytes_error_value wire (message.addresses.getD (alloc.vec.Vec.new U8)) value before remaining ctx e hr
      have hn := congrArg (fun x : Status × Message × Slice U8 => x.2.1) he
      change {message with addresses := some value} = next at hn
      rw [← hn,hv]
      simp [initializeMessage]
  have hv : tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 := by omega
  rcases hv with h | h | h | h | h | h
  · exact False.elim (h1 (UScalar.eq_of_val_eq h))
  · exact False.elim (h2 (UScalar.eq_of_val_eq h))
  · exact False.elim (h3 (UScalar.eq_of_val_eq h))
  · exact False.elim (h4 (UScalar.eq_of_val_eq h))
  · exact False.elim (h5 (UScalar.eq_of_val_eq h))
  · exact False.elim (h6 (UScalar.eq_of_val_eq h))

#print axioms known_error_initialization
end FullParserV3
