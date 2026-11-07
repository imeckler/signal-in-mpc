import SignalMessageWork.BytesFieldWork.GeneratedSelected.Funs
import ProstEncodingWork.CircuitBridge
import TlsMpc.Signal.Serialization

/-! The actual generic Prost byte-field encoder. Its supplied dictionary
operations remain explicit arguments. The unconditional equation preserves
every supplied error/divergence. The circuit theorem is conditional on the
concrete payload adapter: those hypotheses must be discharged against actual
Rust before claiming complete concrete byte-field refinement. -/

namespace LibSignalReference.Candidate.SignalBytesField

open Aeneas Aeneas.Std TlsMpc
open LibSignalReference.Candidate.ProstEncoding

set_option maxHeartbeats 2000000

inductive Field where
  | ratchet | ciphertext | pq | addresses
  deriving DecidableEq

def Field.tag : Field → U32
  | .ratchet => 1#u32
  | .ciphertext => 4#u32
  | .pq => 5#u32
  | .addresses => 6#u32

def Field.key : Field → U64
  | .ratchet => 10#u64
  | .ciphertext => 34#u64
  | .pq => 42#u64
  | .addresses => 50#u64

def varintDictionary (dictionary : _root_.ProstBytesField.bytes.buf.buf_mut.BufMut B) :
    _root_.ProstEncoding.bytes.buf.buf_mut.BufMut B :=
  ⟨dictionary.put_slice, dictionary.put_u8⟩

theorem varint_eq (dictionary : _root_.ProstBytesField.bytes.buf.buf_mut.BufMut B)
    (value : U64) (buf : B) :
    _root_.ProstBytesField.encoding.varint.encode_varint dictionary value buf =
      _root_.ProstEncoding.encoding.varint.encode_varint (varintDictionary dictionary) value buf := by
  rfl

theorem key_eq (dictionary : _root_.ProstBytesField.bytes.buf.buf_mut.BufMut B)
    (field : Field) (buf : B) :
    _root_.ProstBytesField.encoding.encode_key dictionary field.tag .LengthDelimited buf =
      _root_.ProstEncoding.encoding.varint.encode_varint
        (varintDictionary dictionary) field.key buf := by
  cases field <;>
    simp only [_root_.ProstBytesField.encoding.encode_key, Field.tag, Field.key,
      _root_.ProstBytesField.encoding.MAX_TAG, _root_.ProstBytesField.encoding.MIN_TAG]
  all_goals exact varint_eq dictionary _ buf

/-- Exact operation-level decomposition, with no success assumption about the
payload adapter or output dictionary. -/
theorem field_eq (adapter : _root_.ProstBytesField.encoding.BytesAdapter V)
    (dictionary : _root_.ProstBytesField.bytes.buf.buf_mut.BufMut B)
    (field : Field) (value : V) (buf : B) :
    _root_.ProstBytesField.encoding.bytes.encode adapter dictionary field.tag value buf =
      (do
        let afterKey ← _root_.ProstEncoding.encoding.varint.encode_varint
          (varintDictionary dictionary) field.key buf
        let size ← adapter.sealedBytesAdapterInst.len value
        let afterLength ← _root_.ProstEncoding.encoding.varint.encode_varint
          (varintDictionary dictionary) (UScalar.cast .U64 size) afterKey
        adapter.sealedBytesAdapterInst.append_to dictionary value afterLength) := by
  rw [_root_.ProstBytesField.encoding.bytes.encode, key_eq]
  rfl

def actualVecDictionary : _root_.ProstBytesField.bytes.buf.buf_mut.BufMut (Aeneas.Std.alloc.vec.Vec U8) :=
  ⟨vecDictionary.put_slice, vecDictionary.put_u8⟩

theorem varint_actualVec : varintDictionary actualVecDictionary = vecDictionary := by rfl

theorem key_bytes (field : Field) :
    Signal.Varint.publicNat ByteAuth.concrete field.key.val =
      [BitVec.ofNat 8 field.key.val] := by cases field <;> rfl

theorem publicNatLoop_length (fuel value : Nat) :
    (Signal.Varint.publicNatLoop ByteAuth.concrete fuel value).length ≤ fuel := by
  induction fuel generalizing value with
  | zero => simp [Signal.Varint.publicNatLoop]
  | succ fuel ih =>
    simp only [Signal.Varint.publicNatLoop]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _)

theorem publicNat_length (value : Nat) :
    (Signal.Varint.publicNat ByteAuth.concrete value).length ≤ 10 :=
  publicNatLoop_length 10 value

/-- Remaining concrete adapter obligation. This is a theorem hypothesis,
never an axiom or an accepted replacement for the missing Rust operation. -/
def PayloadAppends
    (adapter : _root_.ProstBytesField.encoding.BytesAdapter (Aeneas.Std.alloc.vec.Vec U8))
    (value : Aeneas.Std.alloc.vec.Vec U8) : Prop :=
  ∀ buf : Aeneas.Std.alloc.vec.Vec U8, buf.length + value.length ≤ Usize.max →
    ∃ after, adapter.sealedBytesAdapterInst.append_to actualVecDictionary value buf = .ok after ∧
      vecContents after = vecContents buf ++ vecContents value

theorem field_appends_of_payload_contract
    (adapter : _root_.ProstBytesField.encoding.BytesAdapter (Aeneas.Std.alloc.vec.Vec U8))
    (field : Field) (value buf : Aeneas.Std.alloc.vec.Vec U8)
    (length_eq : adapter.sealedBytesAdapterInst.len value = .ok (Aeneas.Std.alloc.vec.Vec.len value))
    (append_eq : PayloadAppends adapter value)
    (hsize : buf.length + value.length + 11 ≤ Usize.max) :
    ∃ after, _root_.ProstBytesField.encoding.bytes.encode adapter actualVecDictionary field.tag value buf = .ok after ∧
      vecContents after = vecContents buf ++
        Signal.Serialization.bytesField ByteAuth.concrete field.key.val (vecContents value) := by
  obtain ⟨afterKey, hk, hkb⟩ := vec_encode_appends field.key buf (by omega)
  rw [key_bytes] at hkb
  have hkl : afterKey.length = buf.length + 1 := by
    have hl := congrArg List.length hkb
    simpa [vecContents] using hl
  let size : U64 := UScalar.cast .U64 (Aeneas.Std.alloc.vec.Vec.len value)
  have hsize_val : size.val = value.length := by
    simp [size, UScalar.cast_val_eq, Aeneas.Std.alloc.vec.Vec.len]
    have hb := Aeneas.Std.alloc.vec.Vec.len_ineq value
    have hm : Usize.max < 18446744073709551616 := by
      rcases Usize.bounds_eq with h | h <;> rw [h] <;>
        simp [U32.max, U64.max, U32.numBits, U64.numBits]
    omega
  obtain ⟨afterLength, hl, hlb⟩ := vec_encode_appends size afterKey (by omega)
  rw [hsize_val] at hlb
  have hll : afterLength.length ≤ afterKey.length + 10 := by
    have h := congrArg List.length hlb
    simp only [vecContents, List.length_map, List.length_append] at h
    change afterLength.length = afterKey.length +
      (Signal.Varint.publicNat ByteAuth.concrete value.length).length at h
    have bound := publicNat_length value.length
    omega
  obtain ⟨after, ha, hab⟩ := append_eq afterLength (by omega)
  refine ⟨after, ?_, ?_⟩
  · rw [field_eq, varint_actualVec, hk, length_eq]
    change (do
      let next ← _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary size afterKey
      adapter.sealedBytesAdapterInst.append_to actualVecDictionary value next) = .ok after
    rw [hl]
    exact ha
  · rw [hab, hlb, hkb]
    simp [Signal.Serialization.bytesField, vecContents, ByteAuth.concrete,
      List.append_assoc]

/-- Composition into the exact exported byte-field expression, conditional on
the two remaining concrete adapter equations. The theorem does not supply or
assume an opaque Rust buffer implementation. -/
theorem field_refines_artifact_of_payload_contract
    (adapter : _root_.ProstBytesField.encoding.BytesAdapter (Aeneas.Std.alloc.vec.Vec U8))
    (field : Field) (value buf : Aeneas.Std.alloc.vec.Vec U8)
    (length_eq : adapter.sealedBytesAdapterInst.len value = .ok (Aeneas.Std.alloc.vec.Vec.len value))
    (append_eq : PayloadAppends adapter value)
    (hsize : buf.length + value.length + 11 ≤ Usize.max)
    (secret : List (_root_.Std.Tactic.BVDecide.BVExpr 8))
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) = vecContents value) :
    ∃ after, _root_.ProstBytesField.encoding.bytes.encode adapter actualVecDictionary field.tag value buf = .ok after ∧
      ∀ (index : Nat)
        (hi : index < 8 * (Signal.Serialization.bytesField ByteAuth.symbolic field.key.val secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Signal.Serialization.bytesField ByteAuth.symbolic field.key.val secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Signal.Serialization.bytesField ByteAuth.symbolic field.key.val secret))).vec.get index hi)) =
          (ByteCircuit.joinValue ((vecContents after).drop (vecContents buf).length)).getLsbD index := by
  obtain ⟨after, ha, hv⟩ := field_appends_of_payload_contract adapter field value buf
    length_eq append_eq hsize
  have written : (vecContents after).drop (vecContents buf).length =
      Signal.Serialization.bytesField ByteAuth.concrete field.key.val (vecContents value) := by
    rw [hv]
    simp
  refine ⟨after, ha, ?_⟩
  intro index hi
  have evaluated :
      (Signal.Serialization.bytesField ByteAuth.symbolic field.key.val secret).map
        (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) =
      Signal.Serialization.bytesField ByteAuth.concrete field.key.val (vecContents value) := by
    rw [Signal.Serialization.bytesField_map (ByteAuth.evaluationHom assign), hsecret]
  rw [ByteCircuit.compile_bytes_correct, evaluated, ← written]

end LibSignalReference.Candidate.SignalBytesField
