import ProtoParseWork.FullParserV3Work.KnownTotality
open Aeneas Aeneas.Std Result
open SignalMessageIntegration DispatcherIntegration
namespace FullParserV3
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Total actual generated dispatch for every decoded nonzero tag, every wire
kind and recursion budget. All state and suffix outputs remain observable. -/
theorem message_field_total (m : proto.wire.SignalMessage) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) (ht : 0 < tag.val) :
    ∃ status value after,
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf m tag wire before ctx = ok (status,value,after) ∧
      after.length ≤ before.length := by
  by_cases h1 : tag = 1#u32
  · subst tag
    obtain ⟨status,value,after,hm,hle⟩ := bytes_merge_total wire (m.ratchet_key.getD (alloc.vec.Vec.new U8)) before ctx
    refine ⟨status,{m with ratchet_key := some value},after,?_,hle⟩
    rw [ratchet_key_dispatch,hm]
    rfl
  by_cases h2 : tag = 2#u32
  · subst tag
    obtain ⟨status,value,after,hm,hle⟩ := uint32_merge_total wire (m.counter.getD 0#u32) before ctx
    refine ⟨status,{m with counter := some value},after,?_,hle⟩
    rw [counter_dispatch,hm]
    rfl
  by_cases h3 : tag = 3#u32
  · subst tag
    obtain ⟨status,value,after,hm,hle⟩ := uint32_merge_total wire (m.previous_counter.getD 0#u32) before ctx
    refine ⟨status,{m with previous_counter := some value},after,?_,hle⟩
    rw [previous_counter_dispatch,hm]
    rfl
  by_cases h4 : tag = 4#u32
  · subst tag
    obtain ⟨status,value,after,hm,hle⟩ := bytes_merge_total wire (m.ciphertext.getD (alloc.vec.Vec.new U8)) before ctx
    refine ⟨status,{m with ciphertext := some value},after,?_,hle⟩
    rw [ciphertext_dispatch,hm]
    rfl
  by_cases h5 : tag = 5#u32
  · subst tag
    obtain ⟨status,value,after,hm,hle⟩ := bytes_merge_total wire (m.pq_ratchet.getD (alloc.vec.Vec.new U8)) before ctx
    refine ⟨status,{m with pq_ratchet := some value},after,?_,hle⟩
    rw [pq_ratchet_dispatch,hm]
    rfl
  by_cases h6 : tag = 6#u32
  · subst tag
    obtain ⟨status,value,after,hm,hle⟩ := bytes_merge_total wire (m.addresses.getD (alloc.vec.Vec.new U8)) before ctx
    refine ⟨status,{m with addresses := some value},after,?_,hle⟩
    rw [addresses_dispatch,hm]
    rfl
  have htag : 6 < tag.val := by
    by_contra hn
    have hvals : tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 := by omega
    rcases hvals with h | h | h | h | h | h
    · apply h1
      apply UScalar.eq_of_val_eq
      change tag.val = 1
      exact h
    · apply h2
      apply UScalar.eq_of_val_eq
      change tag.val = 2
      exact h
    · apply h3
      apply UScalar.eq_of_val_eq
      change tag.val = 3
      exact h
    · apply h4
      apply UScalar.eq_of_val_eq
      change tag.val = 4
      exact h
    · apply h5
      apply UScalar.eq_of_val_eq
      change tag.val = 5
      exact h
    · apply h6
      apply UScalar.eq_of_val_eq
      change tag.val = 6
      exact h
  obtain ⟨status,after,hm,hle⟩ := unknown_dispatch_total m tag wire before ctx htag
  exact ⟨status,m,after,hm,hle⟩

#print axioms message_field_total
end FullParserV3
