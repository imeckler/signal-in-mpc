import SignalMessageWork.Generated.UInt32Selected.Funs
import ProstEncodingWork.CircuitBridge

namespace LibSignalReference.Candidate.SignalField

open Aeneas Aeneas.Std TlsMpc
open LibSignalReference.Candidate.ProstEncoding

set_option maxHeartbeats 2000000

def varintDictionary (dictionary : _root_.ProstUInt32.bytes.buf.buf_mut.BufMut B) :
    _root_.ProstEncoding.bytes.buf.buf_mut.BufMut B :=
  ⟨dictionary.put_slice, dictionary.put_u8⟩

/-- Two independently selected copies of the same actual generic varint
operation have definitionally equal semantics after dictionary projection. -/
theorem varint_eq (dictionary : _root_.ProstUInt32.bytes.buf.buf_mut.BufMut B)
    (value : U64) (buf : B) :
    _root_.ProstUInt32.encoding.varint.encode_varint dictionary value buf =
      _root_.ProstEncoding.encoding.varint.encode_varint (varintDictionary dictionary) value buf := by
  rfl

def fieldTag (previous : Bool) : U32 := if previous then 3#u32 else 2#u32
def fieldKey (previous : Bool) : U64 := if previous then 24#u64 else 16#u64

/-- The real tag encoder, including its debug tag-range check and wire-type
discriminant, for the two actual SignalMessage counter field tags. -/
theorem key_eq (dictionary : _root_.ProstUInt32.bytes.buf.buf_mut.BufMut B)
    (previous : Bool) (buf : B) :
    _root_.ProstUInt32.encoding.encode_key dictionary (fieldTag previous)
      .Varint buf =
      _root_.ProstEncoding.encoding.varint.encode_varint (varintDictionary dictionary)
        (fieldKey previous) buf := by
  cases previous <;>
    simp only [_root_.ProstUInt32.encoding.encode_key, fieldTag, fieldKey, if_true,
      _root_.ProstUInt32.encoding.MAX_TAG, _root_.ProstUInt32.encoding.MIN_TAG]
  all_goals
    exact varint_eq dictionary _ buf

theorem field_eq (dictionary : _root_.ProstUInt32.bytes.buf.buf_mut.BufMut B)
    (previous : Bool) (value : U32) (buf : B) :
    _root_.ProstUInt32.encoding.uint32.encode dictionary (fieldTag previous) value buf =
      (do
        let next ← _root_.ProstEncoding.encoding.varint.encode_varint
          (varintDictionary dictionary) (fieldKey previous) buf
        _root_.ProstEncoding.encoding.varint.encode_varint
          (varintDictionary dictionary) (UScalar.cast .U64 value) next) := by
  rw [_root_.ProstUInt32.encoding.uint32.encode, key_eq]
  rfl

def actualVecDictionary : _root_.ProstUInt32.bytes.buf.buf_mut.BufMut (Aeneas.Std.alloc.vec.Vec U8) :=
  ⟨vecDictionary.put_slice, vecDictionary.put_u8⟩

theorem varint_actualVec : varintDictionary actualVecDictionary = vecDictionary := by rfl

theorem field_key_bytes (previous : Bool) :
    Signal.Varint.publicNat ByteAuth.concrete (fieldKey previous).val =
      [BitVec.ofNat 8 (if previous then 24 else 16)] := by cases previous <;> rfl

theorem key_appends (previous : Bool) (buf : Aeneas.Std.alloc.vec.Vec U8)
    (hsize : buf.length + 10 ≤ Usize.max) :
    ∃ next, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary
        (fieldKey previous) buf = .ok next ∧
      vecContents next = vecContents buf ++ [BitVec.ofNat 8 (if previous then 24 else 16)] := by
  obtain ⟨next, hn, hb⟩ := vec_encode_appends (fieldKey previous) buf hsize
  exact ⟨next, hn, by simpa only [field_key_bytes] using hb⟩

theorem field_appends (previous : Bool) (value : U32) (width : Nat)
    (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Signal.Varint.canonicalGroups
      (Signal.Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : Aeneas.Std.alloc.vec.Vec U8) (hsize : buf.length + 11 ≤ Usize.max) :
    ∃ after, _root_.ProstUInt32.encoding.uint32.encode actualVecDictionary
        (fieldTag previous) value buf = .ok after ∧
      vecContents after = vecContents buf ++
        (BitVec.ofNat 8 (if previous then 24 else 16) ::
          Signal.Varint.encode Sha256.concrete ByteAuth.concrete value.bv width) := by
  obtain ⟨next, hn, hb⟩ := key_appends previous buf (by omega)
  have hlength : next.length = buf.length + 1 := by
    have h := congrArg List.length hb
    simpa [vecContents] using h
  obtain ⟨after, ha, he⟩ := vec_encode_uint32 value width hw1 hw5 canonical next (by omega)
  refine ⟨after, ?_, ?_⟩
  · rw [field_eq, varint_actualVec, hn]
    exact ha
  · rw [he, hb]
    simp only [List.append_assoc, List.singleton_append]

def fieldExpr (previous : Bool) (secret : _root_.Std.Tactic.BVDecide.BVExpr 32)
    (width : Nat) : List (_root_.Std.Tactic.BVDecide.BVExpr 8) :=
  ByteAuth.symbolic.const (if previous then 24 else 16) ::
    Signal.Varint.encode Sha256.symbolic ByteAuth.symbolic secret width

/-- The exact field expression embedded in Serialization.content, lowered by
the verified numeric compiler, equals the actual Rust field encoder's appended
bytes for either Signal counter field. -/
theorem field_refines_artifact (previous : Bool) (value : U32) (width : Nat)
    (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Signal.Varint.canonicalGroups
      (Signal.Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : Aeneas.Std.alloc.vec.Vec U8) (hsize : buf.length + 11 ≤ Usize.max)
    (secret : _root_.Std.Tactic.BVDecide.BVExpr 32)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.eval assign = value.bv) :
    ∃ after, _root_.ProstUInt32.encoding.uint32.encode actualVecDictionary
        (fieldTag previous) value buf = .ok after ∧
      ∀ (index : Nat) (hi : index < 8 * (fieldExpr previous secret width).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (fieldExpr previous secret width))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (fieldExpr previous secret width))).vec.get index hi)) =
          (ByteCircuit.joinValue ((vecContents after).drop (vecContents buf).length)).getLsbD index := by
  obtain ⟨after, ha, hv⟩ := field_appends previous value width hw1 hw5 canonical buf hsize
  have written : (vecContents after).drop (vecContents buf).length =
      BitVec.ofNat 8 (if previous then 24 else 16) ::
        Signal.Varint.encode Sha256.concrete ByteAuth.concrete value.bv width := by
    rw [hv]
    simp
  refine ⟨after, ha, ?_⟩
  intro index hi
  have evaluated : (fieldExpr previous secret width).map
      (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) =
      BitVec.ofNat 8 (if previous then 24 else 16) ::
        Signal.Varint.encode Sha256.concrete ByteAuth.concrete value.bv width := by
    rw [fieldExpr, List.map_cons,
      Signal.Varint.encode_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign), hsecret]
    rfl
  rw [ByteCircuit.compile_bytes_correct, evaluated, ← written]

end LibSignalReference.Candidate.SignalField
