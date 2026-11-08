import ProtoParseWork.ParserErrorStateV2Work.Replayed.NumericBridge
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
open SignalMessageIntegration DispatcherIntegration
namespace ParserErrorStateV2
set_option maxHeartbeats 1000000

theorem select_zero (yes no : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 yes no = no := by
  cases no
  simp [ProtoParse.selectField, Word64.concrete, ByteAuth.concrete, Unpad.chooseByte,
    show (18446744073709551615#64) = BitVec.allOnes 64 by rfl]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and, true_and]

theorem byte_zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := by simp only [ByteAuth.concrete]; bv_decide

theorem write_zero (tag : BitVec 64) (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete 0 tag payload fields = fields := by
  apply List.ext_getElem
  · simp [ProtoParse.writeFields]
  · intro i h1 h2
    simp only [ProtoParse.writeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    rw [byte_zero_and]
    exact select_zero _ _

theorem initialize_length (enabled : BitVec 8) (tag : BitVec 64)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :
    (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete enabled tag fields).length = fields.length := by
  simp [ProtoParse.initializeFields]

theorem word_eq_self (x : BitVec 64) :
    Word64.eq Word64.concrete ByteAuth.concrete x x = 255 := by
  unfold Word64.eq
  rw [ByteAuth.equalMask_value]
  exact if_pos rfl

/-- Get-or-insert changes only absence; existing scalar/bytes values survive. -/
theorem initialize_get (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (i : Nat) (hi : i < fields.length) :
    (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 (i+1)) fields)[i]'(by
      rw [initialize_length]; exact hi) =
      ProtoParse.selectField Word64.concrete ByteAuth.concrete fields[i].present fields[i] ⟨255,0,0,0⟩ := by
  simp only [ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
  have hm : Word64.eq Word64.concrete ByteAuth.concrete
    (BitVec.ofNat 64 (i+1)) (Word64.concrete.const (i+1)) = 255 := word_eq_self _
  rw [hm]
  change ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 _ _ = _
  exact select_full _ _

theorem initialize_absent (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (i : Nat) (hi : i < fields.length) (hp : fields[i].present = 0) :
    (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 (i+1)) fields)[i]'(by
      rw [initialize_length]; exact hi) = ⟨255,0,0,0⟩ := by
  rw [initialize_get fields i hi, hp]
  exact select_zero _ _

theorem initialize_existing (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (i : Nat) (hi : i < fields.length) (hp : fields[i].present = 255) :
    (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 (i+1)) fields)[i]'(by
      rw [initialize_length]; exact hi) = fields[i] := by
  rw [initialize_get fields i hi,hp]
  exact select_full _ _

/-- Universal scalar Option initialization bridge, including existing fields. -/
theorem scalar_option_initialization (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (i : Nat) (hi : i < fields.length) (hp : fields[i].present = 0 ∨ fields[i].present = 255) :
    scalarView ((ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255
      (BitVec.ofNat 64 (i+1)) fields)[i]'(by rw [initialize_length]; exact hi)) =
      some ((scalarView fields[i]).getD 0#u32) := by
  rcases hp with hp | hp
  · rw [initialize_absent fields i hi hp]
    simp only [scalarView,hp]
    rfl
  · rw [initialize_existing fields i hi hp]
    simp only [scalarView,hp]
    rfl

/-- Universal bytes Option initialization bridge under the accepted content
view; empty initialization does not read or disclose any body content. -/
theorem bytes_option_initialization (body : Aeneas.Std.Slice Aeneas.Std.U8)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (i : Nat) (hi : i < fields.length) (hp : fields[i].present = 0 ∨ fields[i].present = 255) :
    bytesView body ((ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255
      (BitVec.ofNat 64 (i+1)) fields)[i]'(by rw [initialize_length]; exact hi)) =
      some ((bytesView body fields[i]).getD (Aeneas.Std.alloc.vec.Vec.new Aeneas.Std.U8)) := by
  rcases hp with hp | hp
  · rw [initialize_absent fields i hi hp]
    simp only [bytesView,hp]
    rfl
  · rw [initialize_existing fields i hi hp]
    simp only [bytesView,hp]
    rfl

/-- On rejection, an active top-level known field keeps initialization instead
of suppressing the field write. The failed plan's exact cursor is retained. -/
theorem apply_reject (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (hok : state.ok = 255) (hhere : state.next = BitVec.ofNat 64 position)
    (hdepth : state.depth = 0) (hp : p.ok = 0) :
    let next := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state
    next.ok = 0 ∧ next.next = p.stop ∧
    next.fields = ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.fields := by
  have hpos : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hhere]; exact word_eq_self _
  have htop : Word64.eq Word64.concrete ByteAuth.concrete state.depth (Word64.concrete.const 0) = 255 := by
    rw [hdepth]; exact word_eq_self _
  simp only [ProtoParse.applyPlan,hpos,htop,hok,hp]
  refine ⟨by decide, ?_, ?_⟩
  · change Word64.concrete.select 255 p.stop state.next = p.stop
    simp [Word64.concrete]
    simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]
  · change ProtoParse.writeFields Word64.concrete ByteAuth.concrete 0 p.tag p.payload
      (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.fields) = _
    exact write_zero _ _ _

#print axioms initialize_absent
#print axioms initialize_existing
#print axioms apply_reject
#print axioms scalar_option_initialization
#print axioms bytes_option_initialization
end ParserErrorStateV2
