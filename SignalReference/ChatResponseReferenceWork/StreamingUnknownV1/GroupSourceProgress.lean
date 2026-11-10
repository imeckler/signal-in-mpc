import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std
namespace ChatResponseReference.StreamingUnknownV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Progress is derived from the proved actual source decoder/skip totality,
not assumed as a primitive termination or cursor oracle. -/
theorem source_key_decreases (before after : Slice U8) (tag : U32) (wire : encoding.wire_type.WireType)
    (actual : encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) : after.length < before.length := by
  obtain ⟨result,rest,run,bound,strict⟩ := FullParserV3.key_total before
  rw [actual] at run
  cases run
  exact strict (tag,wire) rfl

theorem source_varint_nonincrease (before after : Slice U8) (decoded : core.result.Result U64 error.DecodeError)
    (actual : encoding.varint.decode_varint sliceBuf before = .ok (decoded,after)) : after.length ≤ before.length := by
  obtain ⟨result,rest,run,bound,strict⟩ := FullParserV3.varint_total before
  rw [actual] at run
  cases run
  exact bound

theorem source_field_nonincrease (before after : Slice U8) (tag count : U32) (wire : encoding.wire_type.WireType)
    (status : core.result.Result Unit error.DecodeError)
    (actual : encoding.skip_field sliceBuf wire tag before ⟨count⟩ = .ok (status,after)) : after.length ≤ before.length := by
  obtain ⟨result,derivation,run,bound⟩ := FullParserV3.skip_field_total wire tag count before
  rw [actual] at run
  cases run
  exact bound

theorem source_group_nonincrease (before after : Slice U8) (tag count : U32) (positive : count ≠ 0#u32)
    (status : core.result.Result Unit error.DecodeError)
    (actual : encoding.skip_field_loop sliceBuf tag before ⟨count⟩ = .ok (status,after)) : after.length ≤ before.length := by
  obtain ⟨result,derivation,run,bound⟩ := FullParserV3.skip_group_total tag count before positive
  rw [actual] at run
  cases run
  exact bound

/-- Every successful actual finite group derivation consumes a key, including
empty groups. Remaining child/rest cannot grow the actual contiguous view. -/
theorem group_grammar_success_decreases {tag count before result}
    (derivation : SkipSemantics .group tag count before result) (positive : count ≠ 0#u32)
    (success : result.1 = .Ok ()) : result.2.length < before.length := by
  cases derivation with
  | keyError actual => cases success
  | close actual =>
    have strict := source_key_decreases _ _ _ _ actual
    unfold groupClose
    split <;> exact strict
  | childError notEnd actual decremented child => cases success
  | childNext notEnd actual decremented child rest =>
    have strict := source_key_decreases _ _ _ _ actual
    have childBound := source_field_nonincrease _ _ _ _ _ _ (skip_semantics_reference child)
    have restBound := source_group_nonincrease _ _ _ _ positive _ (skip_semantics_reference rest)
    omega

theorem source_group_success_decreases (before after : Slice U8) (tag count : U32) (positive : count ≠ 0#u32)
    (actual : encoding.skip_field_loop sliceBuf tag before ⟨count⟩ = .ok (.Ok (),after)) : after.length < before.length := by
  obtain ⟨result,derivation,run,bound⟩ := FullParserV3.skip_group_total tag count before positive
  rw [actual] at run
  cases run
  exact group_grammar_success_decreases derivation positive rfl

/-- With a successful non-end first key, successful source group completion
strictly advances beyond that key's suffix, so an already-exhausted private
child cannot recover into a source success within its declared limit. -/
theorem group_success_after_nonend_key {parent count before result}
    (derivation : SkipSemantics .group parent count before result) (positive : count ≠ 0#u32)
    (success : result.1 = .Ok ()) (tag : U32) (wire : encoding.wire_type.WireType) (middle : Slice U8)
    (notEnd : wire ≠ .EndGroup)
    (keyRun : encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),middle)) : result.2.length < middle.length := by
  cases derivation with
  | keyError actual => cases success
  | close actual =>
    rw [keyRun] at actual
    have pair := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj actual))
    exact False.elim (notEnd (congrArg Prod.snd pair))
  | childError notEnd actual decremented child => cases success
  | childNext notEnd actual decremented child rest =>
    rw [keyRun] at actual
    have same := congrArg Prod.snd (Result.ok.inj actual)
    dsimp only at same
    have childBound := source_field_nonincrease _ _ _ _ _ _ (skip_semantics_reference child)
    have restStrict := group_grammar_success_decreases rest positive success
    rw [same]
    omega

#print axioms source_key_decreases
#print axioms source_varint_nonincrease
#print axioms source_field_nonincrease
#print axioms source_group_nonincrease
#print axioms group_grammar_success_decreases
#print axioms source_group_success_decreases
#print axioms group_success_after_nonend_key
end ChatResponseReference.StreamingUnknownV1
