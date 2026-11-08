import ProtoParseWork.FullParserV3Work.FieldProjection
import ProtoParseWork.FullParserV3Work.SuccessScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open ParserErrorStateV2 DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000

theorem apply_top_success_fields (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (hok : state.ok = 255) (hhere : state.next = BitVec.ofNat 64 position)
    (hdepth : state.depth = 0) (hp : p.ok = 255) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields =
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 p.tag p.payload state.fields := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hhere]; exact word_eq_self _
  have ht : Word64.eq Word64.concrete ByteAuth.concrete state.depth (Word64.concrete.const 0) = 255 := by
    rw [hdepth]; exact word_eq_self _
  simp only [ProtoParse.applyPlan,hok,hp,hh,ht]
  change ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 p.tag p.payload
    (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.fields) = _
  exact write_after_initialize _ _ _

theorem apply_fields_length (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64)) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields.length = state.fields.length := by
  simp only [ProtoParse.applyPlan,ProtoParse.writeFields,ProtoParse.initializeFields,List.length_map,List.length_zipIdx]

/-- Full six-field projection of a successful active top-level scan step. -/
theorem apply_top_success_view (body : Slice U8) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (hl : state.fields.length = 6) (hok : state.ok = 255)
    (hhere : state.next = BitVec.ofNat 64 position) (hdepth : state.depth = 0) (hp : p.ok = 255) :
    messageView body (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields
      (by rw [apply_fields_length,hl]) =
    replaceMessage body p.tag p.payload (messageView body state.fields hl) := by
  simp only [apply_top_success_fields state position p hok hhere hdepth hp]
  exact message_write_view body state.fields p.tag p.payload hl

/-- Full six-field projection on rejection, including get-or-insert before the
failure and retention of all existing values. The failed cursor is not masked. -/
theorem apply_top_error_view (body : Slice U8) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (hl : state.fields.length = 6)
    (hm : ∀ i (hi : i < state.fields.length), state.fields[i].present = 0 ∨ state.fields[i].present = 255)
    (hok : state.ok = 255) (hhere : state.next = BitVec.ofNat 64 position)
    (hdepth : state.depth = 0) (hp : p.ok = 0) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).next = p.stop ∧
    messageView body (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields
      (by rw [apply_fields_length,hl]) = initializeMessage p.tag (messageView body state.fields hl) := by
  have h := apply_reject state position p hok hhere hdepth hp
  refine ⟨h.2.1,?_⟩
  simp only [h.2.2]
  exact message_initialize_view body state.fields p.tag hl hm

#print axioms apply_top_success_fields
#print axioms apply_fields_length
#print axioms apply_top_success_view
#print axioms apply_top_error_view
end FullParserV3
