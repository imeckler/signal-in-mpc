import ProtoParseWork.KeyReferenceWork.KeyValue
import ProtoParseWork.KeyReferenceWork.Replayed.Consumption

namespace LibSignalReference.Candidate.ProstKey
open Aeneas Aeneas.Std ProstKeyCandidate TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstKeySlice
set_option maxHeartbeats 300000

def ValidValue (value : U64) : Prop :=
  value.val ≤ 4294967295 ∧ 8 ≤ value.val ∧ value.val % 8 ≤ 5

theorem wire_exists (value : U64) :
    (∃ kind,wireResult value = .Ok kind) ↔ value.val ≤ 5 := by
  constructor
  · rintro ⟨kind,hk⟩
    have h := (wire_ok value kind).mp hk
    cases kind <;> simp only [wireNumber] at h <;> omega
  · intro h
    have hc : value.val = 0 ∨ value.val = 1 ∨ value.val = 2 ∨ value.val = 3 ∨ value.val = 4 ∨ value.val = 5 := by omega
    rcases hc with hv | hv | hv | hv | hv | hv
    · exact ⟨.Varint,(wire_ok _ _).mpr hv⟩
    · exact ⟨.SixtyFourBit,(wire_ok _ _).mpr hv⟩
    · exact ⟨.LengthDelimited,(wire_ok _ _).mpr hv⟩
    · exact ⟨.StartGroup,(wire_ok _ _).mpr hv⟩
    · exact ⟨.EndGroup,(wire_ok _ _).mpr hv⟩
    · exact ⟨.ThirtyTwoBit,(wire_ok _ _).mpr hv⟩

theorem key_success (value : U64) (h : ValidValue value) :
    ∃ kind,keyResult value = .Ok (tagOf value,kind) ∧ wireNumber kind = value.val % 8 := by
  have hr : ¬4294967295 < value.val := by have := h.1; omega
  obtain ⟨kind,hk⟩ := (wire_exists (kindOf value)).mpr (by rw [kind_value]; exact h.2.2)
  have ht : ¬(tagOf value).val < 1 := by rw [tag_value value h.1]; have := h.2.1; omega
  refine ⟨kind,?_,?_⟩
  · simp only [keyResult,if_neg hr,hk,if_neg ht]
  · have hv := (wire_ok _ _).mp hk
    rw [kind_value] at hv
    exact hv.symm

theorem key_success_fields (value : U64) (tag : U32) (kind : WireType)
    (h : keyResult value = .Ok (tag,kind)) :
    ValidValue value ∧ tag = tagOf value ∧ tag.val = value.val / 8 ∧ wireNumber kind = value.val % 8 := by
  unfold keyResult at h
  split at h
  · contradiction
  · rename_i hr
    have hb : value.val ≤ 4294967295 := by omega
    cases hw : wireResult (kindOf value) with
    | Err error => rw [hw] at h; contradiction
    | Ok kind' =>
      rw [hw] at h
      dsimp only at h
      split at h
      · contradiction
      · rename_i ht
        cases h
        have hv := (wire_ok _ _).mp hw
        rw [kind_value] at hv
        have hn : wireNumber kind ≤ 5 := by cases kind <;> decide
        have htag := tag_value value hb
        refine ⟨⟨hb,?_,by omega⟩,rfl,htag,hv.symm⟩
        omega

theorem key_invalid (value : U64) (h : ¬ValidValue value) :
    ∃ error,keyResult value = .Err error := by
  cases hk : keyResult value with
  | Err error => exact ⟨error,rfl⟩
  | Ok pair =>
    have hv := (key_success_fields value pair.1 pair.2 hk).1
    exact False.elim (h hv)

def finishResult (result : core.result.Result U64 error.DecodeError) :
    core.result.Result (U32 × WireType) error.DecodeError :=
  match result with
  | .Ok value => keyResult value
  | .Err error => .Err error

/-- Actual decode_key performs no additional buffer mutation after decode_varint,
even when key validation returns InvalidKey, InvalidWireType, or InvalidTag. -/
theorem key_from_varint (bytes after : Slice U8)
    (result : core.result.Result U64 error.DecodeError)
    (h : encoding.varint.decode_varint ProstKeyVarint.sliceBuf bytes = .ok (result,after)) :
    encoding.decode_key ProstKeyVarint.sliceBuf bytes = .ok (finishResult result,after) := by
  cases result with
  | Ok value => exact key_after_varint _ _ _ _ h
  | Err error => exact key_after_varint_error _ _ _ _ h

/-- Full actual key reference, including the strict varint fields and exact
mutation/error precedence. The inherited ErrorPost describes varint failures;
key-validation failures preserve the already consumed varint suffix. -/
theorem decode_key_reference (bytes : Slice U8) :
    ∃ result remaining,
      encoding.varint.decode_varint ProstKeyVarint.sliceBuf bytes = .ok (result,remaining) ∧
      ProstKeyVarint.PrefixPost bytes result remaining ∧
      ProstKeyVarint.ErrorPost bytes result remaining ∧
      encoding.decode_key ProstKeyVarint.sliceBuf bytes = .ok (finishResult result,remaining) := by
  obtain ⟨result,remaining,hd,hp,he⟩ := ProstKeyVarint.decode_full_reference bytes
  exact ⟨result,remaining,hd,hp,he,key_from_varint bytes remaining result hd⟩

/-- Every actual successful key yields the exact strict-prefix value, tag,
wire type, count and suffix, with all protobuf key range checks. -/
theorem decode_key_success (bytes remaining : Slice U8) (tag : U32) (kind : WireType)
    (h : encoding.decode_key ProstKeyVarint.sliceBuf bytes = .ok (.Ok (tag,kind),remaining)) :
    ∃ value count, ValidValue value ∧ tag.val = value.val / 8 ∧ wireNumber kind = value.val % 8 ∧
      count ≤ bytes.length ∧ count ≤ 10 ∧ remaining = ProstKeyVarint.drop bytes count ∧
      ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0 =
        ⟨255,BitVec.ofNat 64 count,value.bv⟩ := by
  obtain ⟨result,after,_,hp,_,hk⟩ := decode_key_reference bytes
  rw [h] at hk
  have heq := Result.ok.inj hk
  cases result with
  | Err error => simp only [finishResult,Prod.mk.injEq,reduceCtorEq,false_and] at heq
  | Ok value =>
    have hresult : keyResult value = .Ok (tag,kind) := (congrArg Prod.fst heq).symm
    have hafter : remaining = after := congrArg Prod.snd heq
    obtain ⟨count,hc,ht,hp,hr⟩ := hp
    have hv := key_success_fields value tag kind hresult
    exact ⟨value,count,hv.1,hv.2.2.1,hv.2.2.2,hc,ht,hafter.trans hr,hp⟩

#print axioms key_success
#print axioms key_success_fields
#print axioms key_invalid
#print axioms key_from_varint
#print axioms decode_key_reference
#print axioms decode_key_success
end LibSignalReference.Candidate.ProstKey
