import SealedSenderPackagingWork.Generated.WireContent.Funs
import ProstEncodingWork.CircuitBridge
import TlsMpc.Signal.Serialization
import TlsMpc.Signal.SealedSenderV1

namespace LibSignalReference.Candidate.SealedSenderContentWire
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstEncoding
set_option maxHeartbeats 4000000

/-- Same actual Vec override and same actual u8/put_slice methods, projected
between extraction-local dictionary types. No payload implementation assumed. -/
def actualVecDictionary : SealedSenderPackaging.bytes.buf.buf_mut.BufMut (alloc.vec.Vec U8) where
  put := fun inst target source =>
    ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put (SealedSenderPackaging.forwardSourceBuf inst) target source
  put_slice := vecDictionary.put_slice
  put_u8 := vecDictionary.put_u8

def varintDictionary {B : Type} (dict : SealedSenderPackaging.bytes.buf.buf_mut.BufMut B) :
    _root_.ProstEncoding.bytes.buf.buf_mut.BufMut B := ⟨dict.put_slice,dict.put_u8⟩

theorem varint_eq {B : Type} (dict : SealedSenderPackaging.bytes.buf.buf_mut.BufMut B) (value : U64) (buf : B) :
    SealedSenderPackaging.prost.encoding.varint.encode_varint dict value buf =
      _root_.ProstEncoding.encoding.varint.encode_varint (varintDictionary dict) value buf := rfl

theorem actual_varint_dictionary : varintDictionary actualVecDictionary=vecDictionary := rfl

theorem actual_append (value target : alloc.vec.Vec U8) (fits : target.length+value.length≤Usize.max) :
    ∃ after, SealedSenderPackaging.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.append_to actualVecDictionary value target=.ok after ∧
      vecContents after=vecContents target++vecContents value := by
  obtain ⟨after,ha,hv⟩ := LibSignalReference.Candidate.SealedSenderPayload.actual_put_slice_appends target (alloc.vec.Vec.deref value) fits
  refine ⟨after,?_,?_⟩
  · exact ha
  · simp only [vecContents,hv,List.map_append,alloc.vec.Vec.deref]

inductive ContentField where | certificate | content

def ContentField.tag : ContentField → U32 | .certificate=>2#u32 | .content=>3#u32

def ContentField.key : ContentField → U64 | .certificate=>18#u64 | .content=>26#u64

theorem key_eq {B : Type} (dict : SealedSenderPackaging.bytes.buf.buf_mut.BufMut B) (field : ContentField) (buf : B) :
    SealedSenderPackaging.prost.encoding.encode_key dict field.tag .LengthDelimited buf =
      _root_.ProstEncoding.encoding.varint.encode_varint (varintDictionary dict) field.key buf := by
  cases field <;> simp only [SealedSenderPackaging.prost.encoding.encode_key,ContentField.tag,ContentField.key,
    SealedSenderPackaging.prost.encoding.MAX_TAG,SealedSenderPackaging.prost.encoding.MIN_TAG,_root_.ProstBytesField.encoding.MAX_TAG,
    _root_.ProstBytesField.encoding.MIN_TAG]
  all_goals exact varint_eq dict _ buf

theorem publicNatLoop_length (fuel value : Nat) : (Varint.publicNatLoop ByteAuth.concrete fuel value).length≤fuel := by
  induction fuel generalizing value with
  | zero => simp [Varint.publicNatLoop]
  | succ fuel ih => simp only [Varint.publicNatLoop];split <;> simp_all

theorem publicNat_length (value : Nat) : (Varint.publicNat ByteAuth.concrete value).length≤10 := publicNatLoop_length 10 value

theorem key_bytes (field : ContentField) : Varint.publicNat ByteAuth.concrete field.key.val=[BitVec.ofNat 8 field.key.val] := by
  cases field <;> rfl

theorem bytes_field_appends (field : ContentField) (value buf : alloc.vec.Vec U8)
    (fits : buf.length+value.length+21≤Usize.max) :
    ∃ after, SealedSenderPackaging.prost.encoding.bytes.encode SealedSenderPackaging.alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter actualVecDictionary field.tag value buf=.ok after ∧
      vecContents after=vecContents buf++Serialization.bytesField ByteAuth.concrete field.key.val (vecContents value) := by
  obtain ⟨afterKey,hk,hkv⟩ := vec_encode_appends field.key buf (by omega)
  rw [key_bytes] at hkv
  have keyLen : afterKey.length=buf.length+1 := by have h:=congrArg List.length hkv;simpa [vecContents] using h
  let size : U64 := UScalar.cast .U64 (alloc.vec.Vec.len value)
  have sizeVal : size.val=value.length := by
    simp [size,UScalar.cast_val_eq,alloc.vec.Vec.len]
    have hb:=alloc.vec.Vec.len_ineq value
    have hm : Usize.max<18446744073709551616 := by
      rcases Usize.bounds_eq with h|h <;> rw [h] <;> simp [U32.max,U64.max,U32.numBits,U64.numBits]
    omega
  obtain ⟨afterLength,hl,hlv⟩ := vec_encode_appends size afterKey (by omega)
  have lengthBound : afterLength.length≤buf.length+11 := by
    have h:=congrArg List.length hlv
    have b:=publicNat_length size.val
    simp only [vecContents,List.length_map,List.length_append] at h
    change afterLength.length=afterKey.length+(Varint.publicNat ByteAuth.concrete size.val).length at h
    omega
  obtain ⟨after,ha,hav⟩ := actual_append value afterLength (by omega)
  refine ⟨after,?_,?_⟩
  · unfold SealedSenderPackaging.prost.encoding.bytes.encode
    rw [key_eq,actual_varint_dictionary,hk]
    change (do
      let next ← _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary size afterKey
      SealedSenderPackaging.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.append_to actualVecDictionary value next)=.ok after
    rw [hl]
    exact ha
  · rw [hav,hlv,hkv,sizeVal]
    simp [Serialization.bytesField,vecContents,List.append_assoc,ByteAuth.concrete]

theorem type_key_eq {B : Type} (dict : SealedSenderPackaging.bytes.buf.buf_mut.BufMut B) (buf : B) :
    SealedSenderPackaging.prost.encoding.encode_key dict 1#u32 .Varint buf =
      _root_.ProstEncoding.encoding.varint.encode_varint (varintDictionary dict) 8#u64 buf := by
  simp only [SealedSenderPackaging.prost.encoding.encode_key,
    SealedSenderPackaging.prost.encoding.MAX_TAG,SealedSenderPackaging.prost.encoding.MIN_TAG,
    _root_.ProstBytesField.encoding.MAX_TAG,_root_.ProstBytesField.encoding.MIN_TAG]
  exact varint_eq dict _ buf

theorem type_field_eq (buf : alloc.vec.Vec U8) :
    SealedSenderPackaging.prost.encoding.int32.encode actualVecDictionary 1#u32 2#i32 buf =
      (do
        let first ← _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary 8#u64 buf
        _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary 2#u64 first) := by
  unfold SealedSenderPackaging.prost.encoding.int32.encode
  rw [type_key_eq,actual_varint_dictionary]
  simp_rw [varint_eq,actual_varint_dictionary]
  rfl

theorem type_field_appends (buf : alloc.vec.Vec U8) (fits : buf.length+12≤Usize.max) :
    ∃ after, SealedSenderPackaging.prost.encoding.int32.encode actualVecDictionary 1#u32 2#i32 buf=.ok after ∧
      vecContents after=vecContents buf++[8,2] := by
  obtain ⟨first,hf,hfv⟩ := vec_encode_appends 8#u64 buf (by omega)
  have firstLen : first.length=buf.length+1 := by
    have h:=congrArg List.length hfv
    simpa [vecContents,Varint.publicNat,Varint.publicNatLoop] using h
  obtain ⟨after,ha,hav⟩ := vec_encode_appends 2#u64 first (by omega)
  refine ⟨after,?_,?_⟩
  · rw [type_field_eq,hf]
    exact ha
  · rw [hav,hfv]
    simp [Varint.publicNat,Varint.publicNatLoop,List.append_assoc,ByteAuth.concrete]

def contentMessage (certificate inner : alloc.vec.Vec U8) :
    SealedSenderPackaging.proto.sealed_sender.unidentified_sender_message.Message :=
  ⟨some 2#i32,some certificate,some inner,none,none⟩

/-- Actual derive-generated USMC MESSAGE, default hint/no group, equals the
circuit's precise certificate/content protobuf bytes under content bounds. -/
theorem actual_usmc_appends (certificate inner buf : alloc.vec.Vec U8)
    (fits : buf.length+certificate.length+inner.length+34≤Usize.max) :
    ∃ after, SealedSenderPackaging.proto.sealed_sender.unidentified_sender_message.Message.Insts.ProstMessageMessage.encode_raw
        actualVecDictionary (contentMessage certificate inner) buf=.ok after ∧
      vecContents after=vecContents buf++SealedSenderV1.usmc ByteAuth.concrete
        (vecContents certificate) (vecContents inner) := by
  obtain ⟨afterType,ht,htv⟩ := type_field_appends buf (by omega)
  have typeLen : afterType.length=buf.length+2 := by
    have h:=congrArg List.length htv
    simpa [vecContents] using h
  obtain ⟨afterCert,hc,hcv⟩ := bytes_field_appends .certificate certificate afterType (by omega)
  have certBound : afterCert.length≤buf.length+certificate.length+13 := by
    have h:=congrArg List.length hcv
    have bound:=publicNat_length certificate.length
    simp only [vecContents,List.length_map,List.length_append,Serialization.bytesField,List.length_cons,
      List.length_append,ContentField.key] at h
    change afterCert.length=afterType.length+((Varint.publicNat ByteAuth.concrete certificate.length).length+certificate.length+1) at h
    omega
  obtain ⟨after,hi,hiv⟩ := bytes_field_appends .content inner afterCert (by omega)
  simp only [ContentField.tag] at hc hi
  refine ⟨after,?_,?_⟩
  · change (do
      let first ← SealedSenderPackaging.prost.encoding.int32.encode actualVecDictionary 1#u32 2#i32 buf
      let second ← SealedSenderPackaging.prost.encoding.bytes.encode SealedSenderPackaging.alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        actualVecDictionary 2#u32 certificate first
      let third ← SealedSenderPackaging.prost.encoding.bytes.encode SealedSenderPackaging.alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        actualVecDictionary 3#u32 inner second
      pure third)=.ok after
    rw [ht]
    simp only [bind_tc_ok]
    rw [hc]
    simp only [bind_tc_ok]
    rw [hi]
    rfl
  · rw [hiv,hcv,htv]
    simp [SealedSenderV1.usmc,ContentField.key,ByteAuth.concrete,List.append_assoc]

theorem actual_usmc_serialized (certificate inner : alloc.vec.Vec U8)
    (fits : certificate.length+inner.length+34≤Usize.max) :
    ∃ after, SealedSenderPackaging.proto.sealed_sender.unidentified_sender_message.Message.Insts.ProstMessageMessage.encode_raw
        actualVecDictionary (contentMessage certificate inner) (alloc.vec.Vec.new U8)=.ok after ∧
      vecContents after=SealedSenderV1.usmc ByteAuth.concrete (vecContents certificate) (vecContents inner) := by
  obtain ⟨after,ha,hv⟩ := actual_usmc_appends certificate inner (alloc.vec.Vec.new U8) (by simpa using fits)
  exact ⟨after,ha,by simpa [vecContents,alloc.vec.Vec.new] using hv⟩

open _root_.Std.Tactic.BVDecide

/-- Numeric USMC protobuf bytes refine the actual derive-generated encoder.
This endpoint is a packaging component; it does not assume/establish AES/HMAC. -/
theorem compiled_actual_usmc (certificate inner : alloc.vec.Vec U8)
    (fits : certificate.length+inner.length+34≤Usize.max)
    (secretCertificate secretInner : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (hc : secretCertificate.map (BVExpr.eval assign)=vecContents certificate)
    (hi : secretInner.map (BVExpr.eval assign)=vecContents inner) :
    let wire := SealedSenderV1.usmc ByteAuth.symbolic secretCertificate secretInner
    ∃ after, SealedSenderPackaging.proto.sealed_sender.unidentified_sender_message.Message.Insts.ProstMessageMessage.encode_raw
        actualVecDictionary (contentMessage certificate inner) (alloc.vec.Vec.new U8)=.ok after ∧
      ∀ (index : Nat) (bound : index<8*wire.length),
        AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr wire)).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr wire)).vec.get index bound)) =
        (ByteCircuit.joinValue (vecContents after)).getLsbD index := by
  obtain ⟨after,ha,hv⟩ := actual_usmc_serialized certificate inner fits
  refine ⟨after,ha,?_⟩
  intro index bound
  rw [ByteCircuit.compile_bytes_correct,SealedSenderV1.usmc_map (ByteAuth.evaluationHom assign),hc,hi,←hv]

end LibSignalReference.Candidate.SealedSenderContentWire
