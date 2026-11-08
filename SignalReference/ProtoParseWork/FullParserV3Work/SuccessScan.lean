import ProtoParseWork.FullParserV3Work.Table
import ProtoParseWork.FullParserV3Work.KeyCircuit
import ProtoParseWork.ParserErrorStateV2Work.FailureScan
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey
open DispatcherIntegration ParserErrorStateV2
namespace FullParserV3
set_option maxHeartbeats 1000000

/-- V2 cursor handling is identical to the established plan on successful,
valid decoded keys. The key premise is discharged by actual key extraction. -/
theorem successful_plan (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : (keyFields Word64.concrete ByteAuth.concrete key).ok = 255)
    (hp : (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255) :
    ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state =
      ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state := by
  have htag := (plan_key_fields capacity key payload state).1
  have hkind := (plan_key_fields capacity key payload state).2
  dsimp only [ProtoParse.planWithCursor]
  have hkey : ByteAuth.concrete.and key.ok
    (ByteAuth.concrete.and (Word64.concrete.ule key.value (Word64.concrete.const 4294967295))
      (ByteAuth.concrete.and (ByteAuth.concrete.not (Word64.eq Word64.concrete ByteAuth.concrete
        (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag (Word64.concrete.const 0)))
        (Word64.concrete.ule (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 5)))) = 255 := hk
  rw [hp,hkey]
  simp only [Word64.select_accept]
  rw [← hp]

/-- Successful writes overwrite the same row initialization would affect. -/
theorem write_after_initialize (tag : BitVec 64)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 tag payload
      (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag fields) =
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 tag payload fields := by
  apply List.ext_getElem
  · simp [ProtoParse.writeFields,ProtoParse.initializeFields]
  · intro i h1 h2
    simp only [ProtoParse.writeFields,ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    rw [word_eq_value]
    split
    · change ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 _ _ =
        ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 _ _
      rw [select_full,select_full]
    · change ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 _
        (ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 _ _) =
        ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 _ _
      rw [select_zero,select_zero,select_zero]

/-- Any public scan position before the current absolute cursor is inert. -/
theorem apply_inactive (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : state.next ≠ BitVec.ofNat 64 position) :
    ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state = state := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 0 := by
    rw [word_eq_value]; exact if_neg hn
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.applyPlan,hh,hz,hz',Word64.select_reject,stack_zero,write_zero,initialize_zero]
  cases state
  simp [ByteAuth.concrete]
  exact BitVec.and_allOnes

theorem step_inactive (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : state.next ≠ BitVec.ofNat 64 position) :
    ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position = state :=
  apply_inactive position _ state hn

theorem scan_inactive (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : ∀ p ∈ positions, state.next ≠ BitVec.ofNat 64 p) :
    positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state = state := by
  induction positions with
  | nil => rfl
  | cons p rest ih =>
    rw [List.foldl_cons,step_inactive _ _ _ _ (hn p (by simp))]
    exact ih (fun q hq => hn q (by simp [hq]))

#print axioms successful_plan
#print axioms write_after_initialize
#print axioms scan_inactive
end FullParserV3
