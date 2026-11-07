import ProtoParseWork.KeyReferenceWork.PlanBridge

namespace LibSignalReference.Candidate.ProstKey
open Aeneas Aeneas.Std ProstKeyCandidate TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstKeySlice
open _root_.Std.Tactic.BVDecide
set_option maxHeartbeats 400000

local instance (value : U64) : Decidable (ValidValue value) := by unfold ValidValue; infer_instance

def prefixKey (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : KeyFields B W :=
  keyFields o a (ProtoParse.decodePrefix d o a wire 0)

def fieldsBytes (o : Word64.Ops B W) (a : ByteAuth.Ops B) (key : KeyFields B W) : List B :=
  key.ok :: ByteAuth.release a key.ok
    (Word64.bytes o key.stop ++ Word64.bytes o key.tag ++ Word64.bytes o key.kind)

def keyBytes (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : List B :=
  fieldsBytes o a (prefixKey d o a wire)

/-- status1 || consumedBE8 || tagBE8 || wireTypeBE8; errors are25 zero bytes. -/
def resultBytes (before after : Slice U8)
    (result : core.result.Result (U32 × WireType) error.DecodeError) : List (BitVec 8) :=
  match result with
  | .Ok (tag,kind) => 255 :: (Word64.bytes Word64.concrete (BitVec.ofNat 64 (before.length-after.length)) ++
      Word64.bytes Word64.concrete (tag.bv.setWidth 64) ++ Word64.bytes Word64.concrete (BitVec.ofNat 64 (wireNumber kind)))
  | .Err _ => List.replicate 25 0

theorem tag_wide (value : U64) (h : value.val ≤ 4294967295) :
    (tagOf value).bv.setWidth 64 = value.bv >>> 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,UScalar.bv_toNat,tag_value value h,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by have := value.hmax; omega)

theorem kind_word (value : U64) (kind : WireType) (h : wireNumber kind = value.val % 8) :
    value.bv &&& 7 = BitVec.ofNat 64 (wireNumber kind) := by
  apply BitVec.eq_of_toNat_eq
  rw [kind_nat,BitVec.toNat_ofNat]
  change value.val % 8 = wireNumber kind % 2^64
  rw [h,Nat.mod_eq_of_lt (by omega : value.val % 8 < 2^64)]

theorem fields_success (value : U64) (count : Nat) (tag : U32) (kind : WireType)
    (h : keyResult value = .Ok (tag,kind)) :
    keyFields Word64.concrete ByteAuth.concrete ⟨255,BitVec.ofNat 64 count,value.bv⟩ =
      ⟨255,BitVec.ofNat 64 count,tag.bv.setWidth 64,BitVec.ofNat 64 (wireNumber kind)⟩ := by
  have hv := key_success_fields value tag kind h
  have hm := key_mask (⟨255,BitVec.ofNat 64 count,value.bv⟩ : ProtoParse.Decoded (BitVec 8) (BitVec 64))
  have hm' : (keyFields Word64.concrete ByteAuth.concrete ⟨255,BitVec.ofNat 64 count,value.bv⟩).ok = 255 := by
    rw [hm]
    change (255 : BitVec 8) &&& (if ValidValue value then 255 else 0) = 255
    rw [if_pos hv.1]
    rfl
  change (⟨_,_,_,_⟩ : KeyFields (BitVec 8) (BitVec 64)) = _
  congr 1
  · rw [hv.2.1]
    exact (tag_wide value hv.1.1).symm
  · exact kind_word value kind hv.2.2.2

theorem post_error_mask (bytes after : Slice U8) (result : core.result.Result U64 error.DecodeError)
    (error : error.DecodeError) (hp : ProstKeyVarint.PrefixPost bytes result after)
    (he : finishResult result = .Err error) :
    (prefixKey VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).ok = 0 := by
  unfold prefixKey
  rw [key_mask]
  cases result with
  | Err original => rw [hp.2]; exact BitVec.zero_and
  | Ok value =>
    obtain ⟨count,_,_,hp,_⟩ := hp
    rw [hp]
    have hn : ¬ValidValue value := by
      intro hv
      obtain ⟨kind,hk,_⟩ := key_success value hv
      change keyResult value = .Err error at he
      rw [hk] at he
      contradiction
    change (255 : BitVec 8) &&& (if ValidValue value then 255 else 0) = 0
    rw [if_neg hn]
    exact BitVec.and_zero

theorem post_bytes (bytes after : Slice U8) (result : core.result.Result U64 error.DecodeError)
    (hp : ProstKeyVarint.PrefixPost bytes result after) :
    keyBytes VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) =
      resultBytes bytes after (finishResult result) := by
  cases he : finishResult result with
  | Err error =>
    have hz := post_error_mask bytes after result error hp he
    simp only [keyBytes,fieldsBytes,hz,ByteAuth.release_reject,List.length_append,Word64.bytes_length,resultBytes]
    rfl
  | Ok pair =>
    rcases pair with ⟨tag,kind⟩
    cases result with
    | Err error => contradiction
    | Ok value =>
      obtain ⟨count,hc,_,hp,hr⟩ := hp
      have hcount : bytes.length-after.length = count := by rw [hr,ProstKeyVarint.drop_length]; omega
      unfold keyBytes prefixKey
      rw [hp,fields_success value count tag kind he]
      simp only [fieldsBytes,resultBytes,hcount]
      exact congrArg (List.cons 255) (ByteAuth.release_accept _)

theorem keyBytes_map {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops B' W'}
    {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {f : B → B'} {fw : W → W'} (hd : VarintDecode.Spqr.Hom d d' f fw)
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (wire : List B) :
    (keyBytes d o a wire).map f = keyBytes d' o' a' (wire.map f) := by
  have hk := keyFields_map ho ha (ProtoParse.decodePrefix d o a wire 0)
  rw [ProtoParse.decodePrefix_map hd ho ha] at hk
  unfold keyBytes fieldsBytes prefixKey
  simp only [List.map_cons,ByteAuth.release_map ha,List.map_append,Word64.bytes_map ho]
  have h0 := congrArg KeyFields.ok hk
  have h1 := congrArg KeyFields.stop hk
  have h2 := congrArg KeyFields.tag hk
  have h3 := congrArg KeyFields.kind hk
  simp only [KeyFields.map] at h0 h1 h2 h3
  rw [h0,h1,h2,h3]


/-- Every bit of the normalized key circuit agrees with actual pinned decode_key
on every contiguous slice. Errors retain the exact mutable suffix from the reference. -/
theorem decode_key_refines_artifact (bytes : Slice U8) (secret : List (BVExpr 8))
    (assign : BVExpr.Assignment) (hinput : secret.map (BVExpr.eval assign) = contents bytes) :
    ∃ result remaining,
      encoding.decode_key ProstKeyVarint.sliceBuf bytes = .ok (result,remaining) ∧
      ∀ (index : Nat) (hi : index < 8*(keyBytes VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (keyBytes VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (keyBytes VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (resultBytes bytes remaining result)).getLsbD index := by
  obtain ⟨result,remaining,_,hp,_,hk⟩ := decode_key_reference bytes
  refine ⟨finishResult result,remaining,hk,?_⟩
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,keyBytes_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign),hinput,post_bytes bytes remaining result hp]

/-- Every actual key error is rejected by the existing parser plan for all
payloads and group/field states. This does not assert payload/parser equivalence. -/
theorem decode_key_error_rejected (bytes remaining : Slice U8) (error : error.DecodeError)
    (h : encoding.decode_key ProstKeyVarint.sliceBuf bytes = .ok (.Err error,remaining))
    (capacity : Nat) (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity
      (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0)
      payload state).ok = 0 := by
  obtain ⟨result,after,_,hp,_,hk⟩ := decode_key_reference bytes
  rw [h] at hk
  have he : finishResult result = .Err error := (congrArg Prod.fst (Result.ok.inj hk)).symm
  exact plan_key_rejects capacity _ payload state (post_error_mask bytes after result error hp he)

#print axioms post_bytes
#print axioms decode_key_refines_artifact
#print axioms decode_key_error_rejected
end LibSignalReference.Candidate.ProstKey
