import TlsMpc.Signal.PrivateVarintSemantics
import ProstEncodingWork.CircuitBridge

namespace LibSignalReference.Candidate.PrivateVarint
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstEncoding

/-- Actual selected prost encoder agrees with private-length varint bytes.
The width is a mathematical witness, not a circuit input or validity flag. -/
theorem actual_uint32_private_wire (value : U32) (width : Nat)
    (hw : 0<width) (hl : width≤5)
    (canonical : Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary
        (UScalar.cast .U64 value) buf = .ok after ∧
      PrivateBuffer.output ByteAuth.concrete
        (PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete value.bv) =
        255 :: (BitVec.ofNat 8 (width/256) :: BitVec.ofNat 8 width ::
          ((vecContents after).drop (vecContents buf).length ++ List.replicate (5-width) 0)) := by
  obtain ⟨after,ha,hv⟩ := vec_encode_uint32 value width hw hl canonical buf hsize
  refine ⟨after,ha,?_⟩
  rw [hv,List.drop_left]
  exact PrivateVarint.uint32_wire value.bv width hw hl canonical

open _root_.Std.Tactic.BVDecide

theorem compiled_actual_uint32_private_wire (value : U32) (width : Nat)
    (hw : 0<width) (hl : width≤5)
    (canonical : Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max)
    (secret : BVExpr 32) (assign : BVExpr.Assignment) (hsecret : secret.eval assign=value.bv) :
    let wire := PrivateBuffer.output ByteAuth.symbolic (PrivateVarint.uint32 Sha256.symbolic ByteAuth.symbolic secret)
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary
        (UScalar.cast .U64 value) buf = .ok after ∧
      ∀ (index : Nat) (hi : index<8*wire.length),
        AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr wire)).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr wire)).vec.get index hi)) =
        (ByteCircuit.joinValue (255 :: (BitVec.ofNat 8 (width/256) :: BitVec.ofNat 8 width ::
          ((vecContents after).drop (vecContents buf).length ++ List.replicate (5-width) 0)))).getLsbD index := by
  obtain ⟨after,ha,wireEq⟩ := actual_uint32_private_wire value width hw hl canonical buf hsize
  refine ⟨after,ha,?_⟩
  intro index hi
  rw [PrivateVarint.compiled_uint32_correct secret assign index hi,hsecret,wireEq]

/-- Every uint32 has a canonical witness; this witness never enters the circuit. -/
theorem canonical_uint32_exists (word : BitVec 32) :
    ∃ width, 0<width ∧ width≤5 ∧
      Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete word) width := by
  have wordBound : word.toNat<4294967296 := word.isLt
  by_cases h1 : word.toNat<128
  · refine ⟨1,by omega,by omega,?_⟩
    rw [groups_values]
    simp [Varint.canonicalGroups,List.range_succ]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h2 : word.toNat<16384
  · refine ⟨2,by omega,by omega,?_⟩
    rw [groups_values]
    simp [Varint.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h3 : word.toNat<2097152
  · refine ⟨3,by omega,by omega,?_⟩
    rw [groups_values]
    simp [Varint.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h4 : word.toNat<268435456
  · refine ⟨4,by omega,by omega,?_⟩
    rw [groups_values]
    simp [Varint.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  · refine ⟨5,by omega,by omega,?_⟩
    rw [groups_values]
    simp [Varint.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega

/-- All uint32 values, without an acceptance or public-width precondition. -/
theorem actual_uint32_private_wire_total (value : U32)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary
        (UScalar.cast .U64 value) buf = .ok after ∧
      let written := (vecContents after).drop (vecContents buf).length
      PrivateBuffer.output ByteAuth.concrete
        (PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete value.bv) =
        255 :: (BitVec.ofNat 8 (written.length/256) :: BitVec.ofNat 8 written.length ::
          (written ++ List.replicate (5-written.length) 0)) := by
  obtain ⟨width,hw,hl,canonical⟩ := canonical_uint32_exists value.bv
  obtain ⟨after,ha,hv⟩ := vec_encode_uint32 value width hw hl canonical buf hsize
  refine ⟨after,ha,?_⟩
  simp only [hv,List.drop_left,Varint.encode_length]
  exact PrivateVarint.uint32_wire value.bv width hw hl canonical

end LibSignalReference.Candidate.PrivateVarint
