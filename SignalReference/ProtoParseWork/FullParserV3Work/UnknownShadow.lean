import ProtoParseWork.FullParserV3Work.KnownMessageScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open _root_.Std.Tactic.BVDecide
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey ParserErrorStateV2
set_option maxHeartbeats 3000000

private theorem select_same (mask : BitVec 8) (value : BitVec 64) :
    Word64.concrete.select mask value value = value := by
  change ((BitVec.replicate 8 mask &&& value) ^^^ (~~~BitVec.replicate 8 mask &&& value)) = value
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases (BitVec.replicate 8 mask).getLsbD i <;> cases value.getLsbD i <;> rfl

theorem initialize_unknown_any (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (enabled : BitVec 8) (hl : fields.length ≤ 6) (ht : 6 < tag.toNat) :
    ProtoParse.initializeFields Word64.concrete ByteAuth.concrete enabled tag fields = fields := by
  apply List.ext_getElem
  · simp only [ProtoParse.initializeFields,List.length_map,List.length_zipIdx]
  · intro i h1 h2
    have hn : tag ≠ Word64.concrete.const (i+1) := by
      intro he
      have hv := congrArg BitVec.toNat he
      change tag.toNat = (BitVec.ofNat 64 (i+1)).toNat at hv
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hv
      omega
    have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
    simp only [ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,word_eq_value,if_neg hn,hz]
    exact select_zero _ _

theorem write_unknown_any (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (enabled : BitVec 8) (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (hl : fields.length ≤ 6) (ht : 6 < tag.toNat) :
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete enabled tag payload fields = fields := by
  apply List.ext_getElem
  · simp only [ProtoParse.writeFields,List.length_map,List.length_zipIdx]
  · intro i h1 h2
    have hn : tag ≠ Word64.concrete.const (i+1) := by
      intro he
      have hv := congrArg BitVec.toNat he
      change tag.toNat = (BitVec.ofNat 64 (i+1)).toNat at hv
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hv
      omega
    have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
    simp only [ProtoParse.writeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,word_eq_value,if_neg hn,hz]
    exact select_zero _ _

/-- A proof-only depth-one shadow reuses actual nested leaf refinements for
unknown top-level non-group fields. It changes no production implementation. -/
theorem plan_unknown_shadow (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hd : state.depth = 0) (ht : 6 < (key.value >>> 3).toNat) (h4 : key.value &&& 7 ≠ 4) :
    ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state =
    ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload {state with depth := 1} := by
  have hu : Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6) = 0 := by
    rw [Word64.ule_value]; exact if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)
  have he : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 4) = 0 := by
    rw [word_eq_value]; exact if_neg h4
  simp only [ProtoParse.planWithCursor,ProtoParse.plan,hu,he,hd]
  simp [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte]

theorem plan_valid_tag (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : (keyFields Word64.concrete ByteAuth.concrete key).ok = 255) :
    (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state).tag = key.value >>> 3 := by
  change Word64.concrete.select (keyFields Word64.concrete ByteAuth.concrete key).ok (key.value >>> 3) 0 = _
  rw [hk]
  exact Word64.select_accept _ _

theorem unknown_step_shadow (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hd : state.depth = 0) (hl : state.fields.length ≤ 6)
    (ht : 6 < ((rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value >>> 3).toNat)
    (h3 : (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value &&& 7 ≠ 3)
    (h4 : (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value &&& 7 ≠ 4)
    (hk : (keyFields Word64.concrete ByteAuth.concrete (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩)).ok = 255) :
    let result := ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position
    let shadow := ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows {state with depth := 1} position
    result.ok = shadow.ok ∧ result.next = shadow.next ∧ result.depth = 0 ∧
      result.fields = state.fields ∧ result.stack = state.stack := by
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[capacity-1]?.getD ⟨0,BitVec.ofNat 64 (capacity-1),0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state
  let ps := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload {state with depth := 1}
  have he : p = ps := plan_unknown_shadow capacity position lastClear key payload state hd ht h4
  have htag : 6 < p.tag.toNat := by rw [plan_valid_tag _ _ _ _ _ _ hk]; exact ht
  have hkind : p.kind = key.value &&& 7 := rfl
  have hs3 : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 3) = 0 := by
    rw [word_eq_value]; exact if_neg h3
  have hs4 : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 4) = 0 := by
    rw [word_eq_value]; exact if_neg h4
  change (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).ok =
      (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position ps {state with depth := 1}).ok ∧
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).next =
      (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position ps {state with depth := 1}).next ∧
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).depth = 0 ∧
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields = state.fields ∧
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).stack = state.stack
  refine ⟨?_,?_,?_,?_,apply_nonstart_stack position p state h3⟩
  · rw [he]; rfl
  · rw [he]; rfl
  · simp only [ProtoParse.applyPlan,hs3,hs4,Word64.select_reject,select_same,hd]
  · dsimp only [ProtoParse.applyPlan]
    rw [initialize_unknown_any _ _ _ hl htag]
    exact write_unknown_any _ _ _ _ hl htag

#print axioms unknown_step_shadow

#print axioms initialize_unknown_any
#print axioms write_unknown_any
#print axioms plan_unknown_shadow
end FullParserV3
