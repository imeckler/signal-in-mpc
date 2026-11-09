import ChatResponseReferenceWork.StreamingV1.OpaquePayloadValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

noncomputable def bodyTrace (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    List (BitVec 8) → List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)
  | [] => []
  | byte::rest =>
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    (event.bodyData,event.bodyReset,event.headerData,byte)::bodyTrace event.state rest

theorem opaque_reset_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).bodyReset = 0 := by
  change ByteAuth.concrete.and _ (ByteAuth.concrete.and
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) = 0
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2 = 0 := by rw [modes]; rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rw [off]
  simp only [zeroAnd,andZero]

theorem body_header_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (kinds : state.kinds = [0,255,0,0]) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).headerData = 0 := by
  change ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3)) = 0
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3 = 0 := by rw [kinds]; rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rw [off]
  simp only [andZero]

/-- Exact actual body-byte events for every supplied proper/exact bounded payload
prefix: each byte is body data, no payload reset, and no header data. -/
theorem opaque_body_trace_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : bytes.length ≤ budget) (payloadEnough : bytes.length ≤ count) (childEnough : count ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,255,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0) (skip : state.skip = BitVec.ofNat 64 count)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    bodyTrace state bytes = bytes.map (fun byte => (255,0,0,byte)) := by
  induction bytes generalizing state count budget remaining with
  | nil => rfl
  | cons byte rest ih =>
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    have nextValid : event.state.valid = 255 := opaque_payload_step_valid state byte count budget remaining budgetBound remainingBound
      (by simp only [List.length_cons] at budgetEnough; omega) (by simp only [List.length_cons] at payloadEnough; omega)
      childEnough modes kinds valid seen finished depth skip budgetCounter childCounter
    have data : event.bodyData = 255 := (opaque_body_event state byte modes kinds).trans nextValid
    have reset : event.bodyReset = 0 := opaque_reset_zero state byte modes
    have header : event.headerData = 0 := body_header_zero state byte kinds
    simp only [bodyTrace,List.map_cons]
    rw [data,reset,header]
    congr 1
    cases rest with
    | nil => rfl
    | cons following tail =>
      have countBound : count < 2^64 := by omega
      have first := opaque_prefix_inside state [byte] count countBound (by simp only [List.length_cons,List.length_nil] at *; omega) modes skip
      have nextModes : event.state.modes = lane 3 := first.1
      have nextSkip : event.state.skip = BitVec.ofNat 64 (count-1) := first.2
      have nextKinds : event.state.kinds = [0,255,0,0] := (opaque_kinds_step state byte modes (by rw [kinds]; rfl)).trans kinds
      have notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
        rw [childCounter]
        unfold TlsChatResponse.weq
        rw [word_eq_value]
        apply if_neg
        intro equal
        have numeric := congrArg BitVec.toNat equal
        have small : remaining < 2^64 := by omega
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
        change remaining = 1 at numeric
        simp only [List.length_cons] at payloadEnough
        omega
      have nextInner : event.state.inner = 255 := opaque_inner_step state byte modes inner notClosing
      have nextDepth : event.state.depth = 0 := (opaque_depth_step state byte modes).trans depth
      have nextBudget : event.state.budget = BitVec.ofNat 64 (budget-1) := by
        rw [step_budget state byte,budgetCounter]
        exact BitVec.ofNat_sub_ofNat_of_le budget 1 (by decide) (by simp only [List.length_cons] at budgetEnough; omega)
      have nextRemaining : event.state.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
        rw [opaque_remaining_step state byte modes inner,childCounter]
        exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at payloadEnough; omega)
      exact ih event.state (count-1) (budget-1) (remaining-1) (by omega) (by omega)
        (by simp only [List.length_cons] at budgetEnough ⊢; omega) (by simp only [List.length_cons] at payloadEnough ⊢; omega) (by omega)
        nextModes nextKinds nextValid seen finished nextInner nextDepth nextSkip nextBudget nextRemaining

open Aeneas Aeneas.Std
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
/-- The emitted payload events contain exactly the bytes copied by the actual
native Bytes merger, including all byte values. The full field proof must supply
the post-length state/budget/child conditions. -/
theorem native_copied_body_events (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (afterLength : Slice U8) (native : U64) (budget remaining : Nat)
    (physical : native.val ≤ afterLength.length)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : native.val ≤ budget) (childEnough : native.val ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,255,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0) (skip : state.skip = native.bv)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    let copied := ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val
    bodyTrace state (contents copied) = (contents copied).map (fun byte => (255,0,0,byte)) ∧
    (feed state (contents copied)).valid = 255 := by
  let copied := ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val
  have length : (contents copied).length = native.val := by
    have result := copied_body_length afterLength native physical
    simpa only [contents,List.length_map] using result
  have nativeBound : native.val < 2^64 := native.bv.isLt
  have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound,UScalar.bv_toNat]
  have count : state.skip = BitVec.ofNat 64 native.val := skip.trans nativeBits
  exact ⟨opaque_body_trace_exact state (contents copied) native.val budget remaining budgetBound remainingBound
      (by rw [length]; exact budgetEnough) (by rw [length]) childEnough modes kinds valid seen finished inner depth count budgetCounter childCounter,
    opaque_payload_prefix_valid state (contents copied) native.val budget remaining budgetBound remainingBound
      (by rw [length]; exact budgetEnough) (by rw [length]) childEnough modes kinds valid seen finished inner depth count budgetCounter childCounter⟩

#print axioms opaque_reset_zero
#print axioms body_header_zero
#print axioms opaque_body_trace_exact
#print axioms native_copied_body_events
end ChatResponseReference.StreamingV1
