import ChatResponseReferenceWork.StreamingV1.ConsumedPrefix
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def scalarUpdateData (isStatus : Bool) (old : ResponseData) (native : U64) : ResponseData :=
  if isStatus then {old with status := statusWord (UScalar.cast .U32 native)}
  else {old with idPresent := 255,id := native.bv}

/-- Actual native successful ID/status payload changes exactly its cached source
field and returns the complete lexer control state at the actual native suffix. -/
theorem native_scalar_data_complete (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat) (isStatus : Bool)
    (remainingBound : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = if isStatus then 2 else 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = scalarUpdateData isStatus (responseData state) native ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).positions = oneHot 0 ∧
      (feed state consumed).value = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have childEnough : leading.length < remaining := by omega
  have context := bounded_varint_prefix_context state leading remaining remainingBound childEnough inner childCounter continues
  have invariant := core_prefix_invariant state leading 1 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have data : responseData next = scalarUpdateData isStatus (responseData state) native := by
    cases isStatus with
    | false =>
      have tagOne : (feed state leading).tag = 1 := context.1.trans tag
      rw [id_terminal_response_data _ byte invariant.1 (context.2.1.trans known) context.2.2.2.1 tagOne terminal,
        nonterminal_prefix_data state leading continues,decoded]
      rfl
    | true =>
      have tagTwo : (feed state leading).tag = 2 := context.1.trans tag
      rw [status_terminal_response_data _ byte invariant.1 (context.2.1.trans known) context.2.2.2.1 tagTwo terminal,
        nonterminal_prefix_data state leading continues,decoded]
      simp only [scalarUpdateData,if_true,status_cast_projection]
      rfl
  have nextModes : next.modes = lane 0 := scalar_terminal_modes _ byte invariant.1 terminal
  have nextPositions : next.positions = oneHot 0 := terminal_position_reset _ byte 1 leading.length (by decide) invariant.1 currentPositions terminal
  have nextValue : next.value = 0 := terminal_value_reset _ byte 1 (by decide) invariant.1 terminal
  let consumed := leading ++ [byte]
  refine ⟨consumed,?_,?_,?_,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using data
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextModes
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextPositions
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextValue

/-- Data/control and validity are joined at one uniquely determined actual
consumed prefix. Initial state relations remain the full scan's obligation. -/
theorem native_scalar_complete (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat) (isStatus : Bool)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = if isStatus then 2 else 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = scalarUpdateData isStatus (responseData state) native ∧
      (feed state consumed).valid = 255 ∧ (feed state consumed).modes = lane 0 ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 := by
  obtain ⟨consumed,span,data,nextModes,nextPositions,nextValue⟩ := native_scalar_data_complete state before after native remaining isStatus
    remainingBound physical childFits modes positions value inner childCounter known tag sourceSuccess
  obtain ⟨validPrefix,validSpan,validField⟩ := native_scalar_success_valid state before after native budget remaining budgetBound remainingBound
    budgetEnough physical childFits modes positions valid seen finished inner depth budgetCounter childCounter sourceSuccess
  have same := consumed_prefix_unique (contents before) (contents after) validPrefix consumed validSpan span
  rw [same] at validField
  exact ⟨consumed,span,data,validField,nextModes,nextPositions,nextValue⟩

/-- Actual generated ID/status source result joined with one complete numeric
cached-data/control/validity transition. Error cases remain in the all-outcomes
source/rejection theorems; this is their successful-field induction branch. -/
theorem actual_scalar_field_complete (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat) (isStatus : Bool)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = if isStatus then 2 else 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (if isStatus then ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (2#u32) .Varint before ctx
      else ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (1#u32) .Varint before ctx) =
      .ok (.Ok (),if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native},after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = scalarUpdateData isStatus (responseData state) native ∧
      (feed state consumed).valid = 255 ∧ (feed state consumed).modes = lane 0 ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 := by
  refine ⟨?_,native_scalar_complete state before after native budget remaining isStatus budgetBound remainingBound
    budgetEnough physical childFits modes positions value valid seen finished inner depth budgetCounter childCounter known tag sourceSuccess⟩
  cases isStatus with
  | false =>
    rw [actual_id_field_decoded source before after ctx (.Ok native) sourceSuccess]
    rfl
  | true =>
    rw [actual_status_field_decoded source before after ctx (.Ok native) sourceSuccess]
    rfl

#print axioms native_scalar_data_complete
#print axioms native_scalar_complete
#print axioms actual_scalar_field_complete
end ChatResponseReference.StreamingV1
