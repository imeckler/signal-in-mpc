import ChatResponseReferenceWork.StreamingUnknownV1.LengthScope
import ChatResponseReferenceWork.StreamingUnknownV1.LengthData
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Complete post-header invariant, derived from actual native decoding. Empty
fields can close the private child; nonempty payloads remain strictly inside it.
The known-field cache is unchanged and the opaque length remains private. -/
theorem actual_unknown_length_header_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (budget remaining : Nat) (ready : ChildReady state before budget remaining)
    (cache : CacheAgrees outer source state)
    (fits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,0,0])
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ header,
      contents before = header ++ contents after ∧
      CacheAgrees outer source (feed state header) ∧
      (feed state header).kinds = [0,0,0,0] ∧
      (feed state header).skip = native.bv ∧
      if native.val = 0 then
        ChildAtKey (feed state header) after (budget-header.length) (remaining-header.length)
      else
        ChildReady (feed state header) after (budget-header.length) (remaining-header.length) ∧
        (feed state header).modes = lane 3 := by
  obtain ⟨leading,byte,tail,span,suffix,nextSkip,nextModes⟩ :=
    native_unknown_length_transition state before after native modes ready.positions ready.value kinds actual
  let header := leading ++ [byte]
  have headerSpan : contents before = header ++ contents after := by
    calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = header ++ contents after := by simp only [header,List.append_assoc,List.singleton_append]
  have inputLength : before.length = header.length+after.length := by
    have result := congrArg List.length headerSpan
    simpa only [contents,List.length_map,List.length_append] using result
  have headerFit : before.length-remaining ≤ after.length := by omega
  obtain ⟨scopeHeader,scopeSpan,nextRemaining,nextInner,nextDepth⟩ :=
    native_unknown_length_header_scope state before after native remaining ready.remainingBound ready.physical headerFit
      modes ready.positions kinds ready.inner ready.childCounter actual
  have sameScope : scopeHeader = header := consumed_prefix_unique _ _ _ _ scopeSpan headerSpan
  subst scopeHeader
  obtain ⟨validHeader,validSpan,nextValid⟩ := native_unknown_length_header_valid state before after native budget remaining
    ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical fits modes ready.positions ready.value kinds
    ready.valid ready.seen ready.finished ready.inner ready.depth ready.budgetCounter ready.childCounter actual
  have sameValid : validHeader = header := consumed_prefix_unique _ _ _ _ validSpan headerSpan
  subst validHeader
  obtain ⟨dataHeader,dataSpan,nextData⟩ := native_unknown_length_header_data state before after native modes ready.positions kinds actual
  have sameData : dataHeader = header := consumed_prefix_unique _ _ _ _ dataSpan headerSpan
  subst dataHeader
  obtain ⟨lexerLeading,lexerByte,lexerTail,lexerSpan,lexerSuffix,lexerBound,decoded,nextValue,nextPositions⟩ :=
    any_native_varint_success state before after native 2 (by decide) modes ready.positions ready.value actual
  let lexerHeader := lexerLeading ++ [lexerByte]
  have lexerHeaderSpan : contents before = lexerHeader ++ contents after := by
    calc
      contents before = lexerLeading ++ lexerByte::contents after := by rw [lexerSpan,←lexerSuffix]
      _ = lexerHeader ++ contents after := by simp only [lexerHeader,List.append_assoc,List.singleton_append]
  have sameLexer : lexerHeader = header := consumed_prefix_unique _ _ _ _ lexerHeaderSpan headerSpan
  have positions : (feed state header).positions = oneHot 0 := by
    rw [←sameLexer]
    simpa only [lexerHeader,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextPositions
  have value : (feed state header).value = 0 := by
    rw [←sameLexer]
    simpa only [lexerHeader,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextValue
  have shape := feed_shape state header ready.shape
  have common : ChildCommon (feed state header) after (budget-header.length) (remaining-header.length) :=
    ⟨by have := ready.budgetBound; omega,by have := ready.remainingBound; omega,
      by have := ready.physical; omega,by have := ready.budgetEnough; omega,shape,positions,value,nextValid,
      (feed_seen state header).trans ready.seen,(feed_finished state header).trans ready.finished,
      nextDepth.trans ready.depth,feed_budget state header budget (by have := ready.budgetEnough; omega) ready.budgetCounter,nextRemaining⟩
  have sourceSpan := native_success_span before after native actual
  rcases sourceSpan with ⟨actualLeading,actualByte,actualTail,actualSpan,actualSuffix,bound,continues,terminal,tenth,nativeValue⟩
  have actualHeaderSpan : contents before = (actualLeading ++ [actualByte]) ++ contents after := by
    rw [actualSpan,←actualSuffix]; simp only [List.append_assoc,List.singleton_append]
  have sameActual : actualLeading ++ [actualByte] = header := consumed_prefix_unique _ _ _ _ actualHeaderSpan headerSpan
  have invariant := core_prefix_invariant state actualLeading 2 0 (by decide) (by omega) modes ready.positions continues
  have currentKinds := (prefix_kinds state actualLeading continues ready.shape.kinds).trans kinds
  have finalKinds : (feed state header).kinds = [0,0,0,0] := by
    rw [←sameActual]
    simpa only [feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using
      (body_length_kinds_step (feed state actualLeading) actualByte invariant.1 (feed_kinds_shape state actualLeading ready.shape.kinds)).trans currentKinds
  have skip : (feed state header).skip = native.bv := by
    simpa only [header,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextSkip
  have finalModes : (feed state header).modes = if native.bv = BitVec.ofNat 64 0 then lane 0 else lane 3 := by
    simpa only [header,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextModes
  refine ⟨header,headerSpan,nextData.trans cache,finalKinds,skip,?_⟩
  have emptyBits : native.bv = BitVec.ofNat 64 0 ↔ native.val = 0 := by
    constructor
    · intro equal; have numeric := congrArg BitVec.toNat equal
      simpa only [UScalar.bv_toNat,BitVec.toNat_ofNat] using numeric
    · intro equal; apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,equal]
  simp only [emptyBits] at finalModes
  by_cases empty : native.val = 0
  · rw [if_pos empty] at finalModes ⊢
    exact ⟨common,finalModes,by simpa only [Nat.sub_eq_zero_iff_le,show remaining ≤ header.length ↔ header.length = remaining by omega] using nextInner⟩
  · rw [if_neg empty] at finalModes ⊢
    have positive : 0 < remaining-header.length := by omega
    exact ⟨⟨common,positive,by rw [if_neg (by omega : header.length ≠ remaining)] at nextInner; exact nextInner⟩,finalModes⟩

#print axioms actual_unknown_length_header_ready
end ChatResponseReference.StreamingUnknownV1
