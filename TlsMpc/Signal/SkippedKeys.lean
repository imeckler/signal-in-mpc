import TlsMpc.Signal.Unpad

/-! Bounded newest-first skipped seed store. Keys, counters, valid flags, seeds,
lookup result, and authentication mask remain shared. Capacity and fixed field
sizes are public. A candidate removal compacts later slots and pads an empty
slot; commit requires authentication255 and a lookup hit. This is a seed32
component, not full Rust session storage or legacy expanded message keys. -/
namespace TlsMpc.Signal.SkippedKeys
open Std.Tactic.BVDecide

abbrev Bytes (B : Type) (n : Nat) := Fin n → B

structure Slot (B : Type) where
  valid : B
  key : Bytes B 32
  counter : Bytes B 4
  seed : Bytes B 32

def Slot.map (f : B → B') (s : Slot B) : Slot B' :=
  ⟨f s.valid, f ∘ s.key, f ∘ s.counter, f ∘ s.seed⟩

def empty (a : ByteAuth.Ops B) : Slot B :=
  ⟨a.const 0, fun _ => a.const 0, fun _ => a.const 0, fun _ => a.const 0⟩

def chooseBytes (a : ByteAuth.Ops B) (mask : B) (yes no : Bytes B n) : Bytes B n :=
  fun i => Unpad.chooseByte a mask (yes i) (no i)

def chooseSlot (a : ByteAuth.Ops B) (mask : B) (yes no : Slot B) : Slot B :=
  ⟨Unpad.chooseByte a mask yes.valid no.valid,
    chooseBytes a mask yes.key no.key, chooseBytes a mask yes.counter no.counter,
    chooseBytes a mask yes.seed no.seed⟩

def chooseSlots (a : ByteAuth.Ops B) (mask : B) (yes no : List (Slot B)) : List (Slot B) :=
  List.zipWith (chooseSlot a mask) yes no

def matchMask (a : ByteAuth.Ops B) (key : Bytes B 32) (counter : Bytes B 4) (slot : Slot B) : B :=
  a.and (ByteAuth.eqMask a slot.valid (a.const 255))
    (a.and (ByteAuth.equalMask a (List.ofFn slot.key) (List.ofFn key))
      (ByteAuth.equalMask a (List.ofFn slot.counter) (List.ofFn counter)))

structure Candidate (B : Type) where
  found : B
  seed : Bytes B 32
  slots : List (Slot B)

def Candidate.map (f : B → B') (r : Candidate B) : Candidate B' :=
  ⟨f r.found, f ∘ r.seed, r.slots.map (Slot.map f)⟩

def lookupCore (a : ByteAuth.Ops B) (key : Bytes B 32) (counter : Bytes B 4) :
    List (Slot B) → Candidate B
  | [] => ⟨a.const 0, fun _ => a.const 0, []⟩
  | slot :: rest =>
      let tail := lookupCore a key counter rest
      let hit := matchMask a key counter slot
      ⟨Unpad.chooseByte a hit (a.const 255) tail.found,
       chooseBytes a hit slot.seed tail.seed,
       chooseSlots a hit (rest ++ [empty a]) (slot :: tail.slots)⟩

/-- Use with a candidate obtained from lookupCore on old. The exported consume
operation enforces this shape relation; arbitrary caller-built candidates do not. -/
def commit (a : ByteAuth.Ops B) (authentication : B) (candidate : Candidate B) (old : List (Slot B)) : Candidate B :=
  let accepted := a.and (ByteAuth.eqMask a authentication (a.const 255)) candidate.found
  ⟨accepted, fun i => a.and accepted (candidate.seed i),
    chooseSlots a accepted candidate.slots old⟩

def consume (a : ByteAuth.Ops B) (authentication : B) (key : Bytes B 32)
    (counter : Bytes B 4) (slots : List (Slot B)) : Candidate B :=
  commit a authentication (lookupCore a key counter slots) slots

/-- Fixed-capacity insertion, including capacity0. New valid flag is255. -/
def insertFront (a : ByteAuth.Ops B) (key : Bytes B 32) (counter : Bytes B 4)
    (seed : Bytes B 32) (slots : List (Slot B)) : List (Slot B) :=
  (Slot.mk (a.const 255) key counter seed :: slots).take slots.length

def slotBytes (slot : Slot B) : List B :=
  slot.valid :: (List.ofFn slot.key ++ List.ofFn slot.counter ++ List.ofFn slot.seed)

def storeBytes (slots : List (Slot B)) : List B := slots.flatMap slotBytes

def candidateBytes (r : Candidate B) : List B := r.found :: (List.ofFn r.seed ++ storeBytes r.slots)

def lookupBytes (a : ByteAuth.Ops B) (key : Bytes B 32) (counter : Bytes B 4) (slots : List (Slot B)) : List B :=
  candidateBytes (lookupCore a key counter slots)

def consumeBytes (a : ByteAuth.Ops B) (authentication : B) (key : Bytes B 32)
    (counter : Bytes B 4) (slots : List (Slot B)) : List B :=
  candidateBytes (consume a authentication key counter slots)

theorem chooseSlot_accept (yes no : Slot (BitVec 8)) : chooseSlot ByteAuth.concrete 255 yes no = yes := by
  unfold chooseSlot chooseBytes
  simp only [Unpad.chooseByte_accept]

theorem chooseSlot_reject (yes no : Slot (BitVec 8)) : chooseSlot ByteAuth.concrete 0 yes no = no := by
  unfold chooseSlot chooseBytes
  simp only [Unpad.chooseByte_reject]

theorem chooseSlots_accept (yes no : List (Slot (BitVec 8))) (h : yes.length = no.length) :
    chooseSlots ByteAuth.concrete 255 yes no = yes := by
  induction yes generalizing no with
  | nil => rfl
  | cons y ys ih =>
      cases no with
      | nil => simp at h
      | cons n ns => simp only [chooseSlots, List.zipWith_cons_cons, chooseSlot_accept]
                     rw [← chooseSlots, ih ns (by simpa using h)]

theorem chooseSlots_reject (yes no : List (Slot (BitVec 8))) (h : yes.length = no.length) :
    chooseSlots ByteAuth.concrete 0 yes no = no := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all [chooseSlots]
  | cons y ys ih =>
      cases no with
      | nil => rfl
      | cons n ns => simp only [chooseSlots, List.zipWith_cons_cons, chooseSlot_reject]
                     rw [← chooseSlots, ih ns (by simpa using h)]

theorem lookup_length (a : ByteAuth.Ops B) (key : Bytes B 32) (counter : Bytes B 4) (slots : List (Slot B)) :
    (lookupCore a key counter slots).slots.length = slots.length := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => simp [lookupCore, chooseSlots, ih]

theorem insert_length (a : ByteAuth.Ops B) (key : Bytes B 32) (counter : Bytes B 4)
    (seed : Bytes B 32) (slots : List (Slot B)) :
    (insertFront a key counter seed slots).length = slots.length := by simp [insertFront]

def Matches (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4) (slot : Slot (BitVec 8)) : Prop :=
  slot.valid = 255 ∧ List.ofFn slot.key = List.ofFn key ∧ List.ofFn slot.counter = List.ofFn counter

instance (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4) (slot : Slot (BitVec 8)) :
    Decidable (Matches key counter slot) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem matchMask_value (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4) (slot : Slot (BitVec 8)) :
    matchMask ByteAuth.concrete key counter slot = if Matches key counter slot then 255 else 0 := by
  have hc : ByteAuth.concrete.const 255 = (255 : BitVec 8) := rfl
  simp only [matchMask, hc, ByteAuth.eqMask_value, ByteAuth.equalMask_value, Matches]
  by_cases hv : slot.valid = 255 <;>
    by_cases hk : List.ofFn slot.key = List.ofFn key <;>
      by_cases hn : List.ofFn slot.counter = List.ofFn counter <;>
        simp only [hv,hk,hn,if_true,if_false,true_and,false_and,and_false] <;> rfl

/-- First matching valid slot wins, including duplicates. Removal shifts all
later physical slots left and appends an all-zero slot; misses preserve state. -/
def lookupSpec (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4) :
    List (Slot (BitVec 8)) → Candidate (BitVec 8)
  | [] => ⟨0, fun _ => 0, []⟩
  | slot :: rest =>
      if Matches key counter slot then ⟨255, slot.seed, rest ++ [empty ByteAuth.concrete]⟩
      else let tail := lookupSpec key counter rest
           ⟨tail.found, tail.seed, slot :: tail.slots⟩

theorem lookup_spec (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4) (slots : List (Slot (BitVec 8))) :
    lookupCore ByteAuth.concrete key counter slots = lookupSpec key counter slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      have hl : (rest ++ [empty ByteAuth.concrete]).length =
          (slot :: (lookupCore ByteAuth.concrete key counter rest).slots).length := by simp [lookup_length]
      simp only [lookupCore, lookupSpec, matchMask_value]
      split
      · rw [chooseSlots_accept _ _ hl]
        unfold chooseBytes
        simp only [Unpad.chooseByte_accept]
        rfl
      · rw [chooseSlots_reject _ _ hl]
        unfold chooseBytes
        simp only [Unpad.chooseByte_reject, ih]

theorem failed_auth_preserves (authentication : BitVec 8) (key : Bytes (BitVec 8) 32)
    (counter : Bytes (BitVec 8) 4) (slots : List (Slot (BitVec 8))) (h : authentication ≠ 255) :
    consume ByteAuth.concrete authentication key counter slots = ⟨0, fun _ => 0, slots⟩ := by
  have ha : ByteAuth.eqMask ByteAuth.concrete authentication (ByteAuth.concrete.const 255) = 0 := by
    change ByteAuth.eqMask ByteAuth.concrete authentication 255 = 0
    rw [ByteAuth.eqMask_value, if_neg h]
  simp only [consume, commit, ha]
  have andzero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [andzero]
  rw [chooseSlots_reject _ _ (lookup_length _ _ _ _)]

theorem commit_hit (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4)
    (slots : List (Slot (BitVec 8))) (h : (lookupCore ByteAuth.concrete key counter slots).found = 255) :
    consume ByteAuth.concrete 255 key counter slots = lookupCore ByteAuth.concrete key counter slots := by
  have ha : ByteAuth.eqMask ByteAuth.concrete 255 (ByteAuth.concrete.const 255) = 255 := by
    change ByteAuth.eqMask ByteAuth.concrete 255 255 = 255
    simp [ByteAuth.eqMask_value]
  simp only [consume, commit, ha, h]
  have andones (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  simp only [andones]
  rw [chooseSlots_accept _ _ (lookup_length _ _ _ _)]
  rw [← h]

theorem first_match_wins (key : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4)
    (slot : Slot (BitVec 8)) (rest : List (Slot (BitVec 8))) (h : Matches key counter slot) :
    lookupCore ByteAuth.concrete key counter (slot :: rest) =
      ⟨255, slot.seed, rest ++ [empty ByteAuth.concrete]⟩ := by
  rw [lookup_spec]
  simp only [lookupSpec, if_pos h]

theorem failed_lookup_preserves (authentication : BitVec 8) (key : Bytes (BitVec 8) 32)
    (counter : Bytes (BitVec 8) 4) (slots : List (Slot (BitVec 8)))
    (h : (lookupCore ByteAuth.concrete key counter slots).found = 0) :
    consume ByteAuth.concrete authentication key counter slots = ⟨0, fun _ => 0, slots⟩ := by
  have andzero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have zeroand (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [consume, commit, h, andzero, zeroand]
  rw [chooseSlots_reject _ _ (lookup_length _ _ _ _)]

theorem consume_length (a : ByteAuth.Ops B) (authentication : B) (key : Bytes B 32)
    (counter : Bytes B 4) (slots : List (Slot B)) :
    (consume a authentication key counter slots).slots.length = slots.length := by
  simp [consume, commit, chooseSlots, lookup_length]

theorem slotBytes_length (slot : Slot B) : (slotBytes slot).length = 69 := by
  simp [slotBytes]

theorem storeBytes_length (slots : List (Slot B)) : (storeBytes slots).length = 69 * slots.length := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => simp [storeBytes, slotBytes_length] at *; omega

theorem consumeBytes_length (a : ByteAuth.Ops B) (authentication : B) (key : Bytes B 32)
    (counter : Bytes B 4) (slots : List (Slot B)) :
    (consumeBytes a authentication key counter slots).length = 33 + 69 * slots.length := by
  simp [consumeBytes, candidateBytes, storeBytes_length, consume_length]; omega

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem empty_map : (empty a).map f = empty b := by simp [empty, Slot.map, Function.comp_def, h.const]

theorem chooseBytes_map (mask : B) (yes no : Bytes B n) :
    f ∘ chooseBytes a mask yes no = chooseBytes b (f mask) (f ∘ yes) (f ∘ no) := by
  funext i
  exact Unpad.chooseByte_map h mask (yes i) (no i)

theorem chooseSlot_map (mask : B) (yes no : Slot B) :
    (chooseSlot a mask yes no).map f = chooseSlot b (f mask) (yes.map f) (no.map f) := by
  unfold Slot.map chooseSlot chooseBytes
  simp only [Function.comp_def, Unpad.chooseByte_map h]

theorem chooseSlots_map (mask : B) (yes no : List (Slot B)) :
    (chooseSlots a mask yes no).map (Slot.map f) =
      chooseSlots b (f mask) (yes.map (Slot.map f)) (no.map (Slot.map f)) := by
  induction yes generalizing no with
  | nil => rfl
  | cons y ys ih => cases no <;> simp [chooseSlots, chooseSlot_map h]

theorem matchMask_map (key : Bytes B 32) (counter : Bytes B 4) (slot : Slot B) :
    f (matchMask a key counter slot) = matchMask b (f ∘ key) (f ∘ counter) (slot.map f) := by
  simp [matchMask, h.and, h.const, ByteAuth.eqMask_map h, ByteAuth.equalMask_map h,
    Slot.map, Function.comp_def]

theorem lookup_map (key : Bytes B 32) (counter : Bytes B 4) (slots : List (Slot B)) :
    (lookupCore a key counter slots).map f =
      lookupCore b (f ∘ key) (f ∘ counter) (slots.map (Slot.map f)) := by
  induction slots with
  | nil => simp [lookupCore, Candidate.map, Function.comp_def, h.const]
  | cons slot rest ih =>
      have hf := congrArg Candidate.found ih
      have hs := congrArg Candidate.seed ih
      have ht := congrArg Candidate.slots ih
      simp only [Candidate.map] at hf hs ht
      simp only [lookupCore, List.map_cons, Candidate.map, Unpad.chooseByte_map h,
        h.const, chooseSlots_map h, chooseBytes_map h, matchMask_map h,
        List.map_append, empty_map h, List.map_nil, hf, hs, ht]
      rfl

theorem commit_map (authentication : B) (candidate : Candidate B) (old : List (Slot B)) :
    (commit a authentication candidate old).map f =
      commit b (f authentication) (candidate.map f) (old.map (Slot.map f)) := by
  simp [commit, Candidate.map, Function.comp_def, h.and, h.const,
    ByteAuth.eqMask_map h, chooseSlots_map h]

theorem consume_map (authentication : B) (key : Bytes B 32) (counter : Bytes B 4) (slots : List (Slot B)) :
    (consume a authentication key counter slots).map f =
      consume b (f authentication) (f ∘ key) (f ∘ counter) (slots.map (Slot.map f)) := by
  simp only [consume, commit_map h, lookup_map h]

theorem insert_map (key : Bytes B 32) (counter : Bytes B 4) (seed : Bytes B 32) (slots : List (Slot B)) :
    (insertFront a key counter seed slots).map (Slot.map f) =
      insertFront b (f ∘ key) (f ∘ counter) (f ∘ seed) (slots.map (Slot.map f)) := by
  simp [insertFront, Slot.map, List.map_take, h.const]
end Refinement

theorem slotBytes_map (f : B → B') (slot : Slot B) : (slotBytes slot).map f = slotBytes (slot.map f) := by
  simp [slotBytes, Slot.map, Function.comp_def]

theorem storeBytes_map (f : B → B') (slots : List (Slot B)) :
    (storeBytes slots).map f = storeBytes (slots.map (Slot.map f)) := by
  simp [storeBytes, List.map_flatMap, List.flatMap_map, slotBytes_map]

theorem candidateBytes_map (f : B → B') (r : Candidate B) :
    (candidateBytes r).map f = candidateBytes (r.map f) := by
  simp [candidateBytes, Candidate.map, storeBytes_map, Function.comp_def]

theorem compiled_consume_correct (authentication : BVExpr 8) (key : Bytes (BVExpr 8) 32)
    (counter : Bytes (BVExpr 8) 4) (slots : List (Slot (BVExpr 8))) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (consumeBytes ByteAuth.symbolic authentication key counter slots).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (consumeBytes ByteAuth.symbolic authentication key counter slots))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (consumeBytes ByteAuth.symbolic authentication key counter slots))).vec.get index hi)) =
      (ByteCircuit.joinValue (consumeBytes ByteAuth.concrete (BVExpr.eval assign authentication)
        (BVExpr.eval assign ∘ key) (BVExpr.eval assign ∘ counter)
        (slots.map (Slot.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  unfold consumeBytes
  rw [candidateBytes_map, consume_map (ByteAuth.evaluationHom assign)]

theorem compiled_lookup_correct (key : Bytes (BVExpr 8) 32) (counter : Bytes (BVExpr 8) 4)
    (slots : List (Slot (BVExpr 8))) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (lookupBytes ByteAuth.symbolic key counter slots).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (lookupBytes ByteAuth.symbolic key counter slots))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (lookupBytes ByteAuth.symbolic key counter slots))).vec.get index hi)) =
      (ByteCircuit.joinValue (candidateBytes (lookupSpec
        (BVExpr.eval assign ∘ key) (BVExpr.eval assign ∘ counter)
        (slots.map (Slot.map (BVExpr.eval assign)))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  unfold lookupBytes
  rw [candidateBytes_map, lookup_map (ByteAuth.evaluationHom assign), lookup_spec]

theorem compiled_insert_correct (key : Bytes (BVExpr 8) 32) (counter : Bytes (BVExpr 8) 4)
    (seed : Bytes (BVExpr 8) 32) (slots : List (Slot (BVExpr 8))) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (storeBytes (insertFront ByteAuth.symbolic key counter seed slots)).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (storeBytes (insertFront ByteAuth.symbolic key counter seed slots)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (storeBytes (insertFront ByteAuth.symbolic key counter seed slots)))).vec.get index hi)) =
      (ByteCircuit.joinValue (storeBytes (insertFront ByteAuth.concrete
        (BVExpr.eval assign ∘ key) (BVExpr.eval assign ∘ counter) (BVExpr.eval assign ∘ seed)
        (slots.map (Slot.map (BVExpr.eval assign)))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, storeBytes_map, insert_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.SkippedKeys
