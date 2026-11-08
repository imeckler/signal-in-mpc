import ProtoParseWork.ParserErrorStateV2Work.Initialization
open TlsMpc TlsMpc.Signal
namespace ParserErrorStateV2
set_option maxHeartbeats 1000000

theorem initialize_zero (tag : BitVec 64)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :
    ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 0 tag fields = fields := by
  apply List.ext_getElem
  · simp [ProtoParse.initializeFields]
  · intro i h1 h2
    simp only [ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    rw [byte_zero_and]
    exact select_zero _ _

theorem word_select_zero (x y : BitVec 64) : Word64.concrete.select 0 x y = y := by
  simp [Word64.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

theorem stack_zero (index tag : BitVec 64) (stack : List (BitVec 64)) :
    ProtoParse.writeStack Word64.concrete ByteAuth.concrete 0 index tag stack = stack := by
  apply List.ext_getElem
  · simp [ProtoParse.writeStack]
  · intro i h1 h2
    simp only [ProtoParse.writeStack,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    rw [byte_zero_and]
    exact word_select_zero _ _

/-- Public scanning after rejection preserves the complete mutated error state. -/
theorem apply_failed (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (position : Nat)
    (h : state.ok = 0) :
    ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state = state := by
  cases state with
  | mk ok next depth stack fields =>
    simp only [ProtoParse.applyPlan] at *
    simp only [h,byte_zero_and,word_select_zero,stack_zero,initialize_zero,write_zero]

theorem step_failed (capacity : Nat) (decoders : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (position : Nat)
    (h : state.ok = 0) :
    ProtoParse.step Word64.concrete ByteAuth.concrete capacity decoders state position = state :=
  apply_failed _ state position h

theorem scan_failed (capacity : Nat) (decoders : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (positions : List Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (h : state.ok = 0) :
    positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity decoders) state = state := by
  induction positions with
  | nil => rfl
  | cons pos rest ih => simp only [List.foldl_cons,step_failed _ _ _ _ h,ih]

/-- Compose an actual rejected plan with any remaining public scan positions;
rejection, initialized fields and exact failure cursor persist. -/
theorem rejected_scan (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position capacity : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (decoders : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (positions : List Nat)
    (hok : state.ok = 255) (hhere : state.next = BitVec.ofNat 64 position)
    (hdepth : state.depth = 0) (hp : p.ok = 0) :
    let endState := positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity decoders)
      (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state)
    endState.ok = 0 ∧ endState.next = p.stop ∧
      endState.fields = ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.fields := by
  have hr := apply_reject state position p hok hhere hdepth hp
  dsimp only
  rw [scan_failed _ _ _ _ hr.1]
  exact hr

#print axioms apply_failed
#print axioms scan_failed
#print axioms rejected_scan
end ParserErrorStateV2
