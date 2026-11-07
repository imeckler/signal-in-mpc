import TlsMpc.Signal.OpenResult
import TlsMpc.Sha256

/-! Bounded canonical protobuf uint32 varints. The two counters are shared
32-bit words; only their chosen encoded widths are public. A secret mask
rejects a width unless all higher groups vanish and the highest emitted group
is nonzero (except the one-byte zero representation). -/

namespace TlsMpc.Signal.Varint
open Std.Tactic.BVDecide

def pack (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (bytes : List B) : W :=
  s.pack (OpenResult.get a bytes 0) (OpenResult.get a bytes 1)
    (OpenResult.get a bytes 2) (OpenResult.get a bytes 3)

def groups (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (word : W) : List B :=
  (List.range 5).map (fun i => a.and (s.unpack (s.shr word (7 * i)) 3) (a.const 127))

def widthMask (a : ByteAuth.Ops B) (payload : List B) (width : Nat) : B :=
  a.and (ByteAuth.equalMask a (payload.drop width) (List.replicate (5 - width) (a.const 0)))
    (if width = 1 then a.const 255 else a.not (ByteAuth.zeroMask a (OpenResult.get a payload (width - 1))))

def encodeGroups (a : ByteAuth.Ops B) (payload : List B) (width : Nat) : List B :=
  (List.range width).map (fun i =>
    a.xor (OpenResult.get a payload i) (a.const (if i + 1 < width then 128 else 0)))

def encode (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) : List B :=
  encodeGroups a (groups s a word) width

def accepts (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) : B :=
  widthMask a (groups s a word) width

/-- Public lengths and field tags only. Ten steps suffice for uint64 values;
checked callers bound every length below 2^64. -/
def publicNatLoop (a : ByteAuth.Ops B) : Nat → Nat → List B
  | 0, _ => []
  | fuel + 1, value =>
    if value < 128 then [a.const value]
    else a.const (value % 128 + 128) :: publicNatLoop a fuel (value / 128)

def publicNat (a : ByteAuth.Ops B) (value : Nat) : List B := publicNatLoop a 10 value

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

include hs in
theorem pack_map (bytes : List B) :
    fw (pack s a bytes) = pack s' a' (bytes.map f) := by
  simp only [pack, hs.pack, OpenResult.get_map ha]

include hs in
theorem groups_map (word : W) : (groups s a word).map f = groups s' a' (fw word) := by
  simp only [groups, List.map_map, Function.comp_def, ha.and, hs.unpack, hs.shr, ha.const]

theorem widthMask_map (payload : List B) (width : Nat) :
    f (widthMask a payload width) = widthMask a' (payload.map f) width := by
  simp only [widthMask, ha.and, ByteAuth.equalMask_map ha, List.map_drop, List.map_replicate, ha.const]
  split <;> simp_all only [ha.const, ha.not, ByteAuth.zeroMask_map ha, OpenResult.get_map ha]

theorem encodeGroups_map (payload : List B) (width : Nat) :
    (encodeGroups a payload width).map f = encodeGroups a' (payload.map f) width := by
  simp only [encodeGroups, List.map_map, Function.comp_def, ha.xor, OpenResult.get_map ha, ha.const]

include hs in
theorem encode_map (word : W) (width : Nat) :
    (encode s a word width).map f = encode s' a' (fw word) width := by
  simp only [encode, encodeGroups_map ha, groups_map hs ha]

include hs in
theorem accepts_map (word : W) (width : Nat) :
    f (accepts s a word width) = accepts s' a' (fw word) width := by
  simp only [accepts, widthMask_map ha, groups_map hs ha]

theorem publicNatLoop_map (fuel value : Nat) :
    (publicNatLoop a fuel value).map f = publicNatLoop a' fuel value := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    simp only [publicNatLoop]
    split <;> simp_all only [List.map_cons, List.map_nil, ha.const]

theorem publicNat_map (value : Nat) : (publicNat a value).map f = publicNat a' value :=
  publicNatLoop_map ha 10 value

end Refinement

theorem encode_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) :
    (encode s a word width).length = width := by simp [encode, encodeGroups]

def canonicalGroups (payload : List (BitVec 8)) (width : Nat) : Prop :=
  payload.drop width = List.replicate (5 - width) 0 ∧
  (width = 1 ∨ OpenResult.get ByteAuth.concrete payload (width - 1) ≠ 0)

instance (payload : List (BitVec 8)) (width : Nat) : Decidable (canonicalGroups payload width) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem widthMask_value (payload : List (BitVec 8)) (width : Nat) :
    widthMask ByteAuth.concrete payload width = if canonicalGroups payload width then 255 else 0 := by
  have hc : ByteAuth.concrete.const 0 = (0 : BitVec 8) := rfl
  simp only [widthMask, hc, ByteAuth.equalMask_value, canonicalGroups]
  by_cases hw : width = 1
  · simp only [hw, if_true, true_or, and_true]
    split <;> rfl
  · simp only [if_neg hw, ByteAuth.zeroMask_value]
    by_cases hh : payload.drop width = List.replicate (5 - width) 0 <;>
      by_cases ht : OpenResult.get ByteAuth.concrete payload (width - 1) = 0 <;>
      simp only [hw, hh, ht, Ne, if_true, if_false, false_or, not_true_eq_false,
        not_false_eq_true, and_true, and_false] <;> rfl

theorem compiled_encode_correct (word : BVExpr 32) (width : Nat)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encode Sha256.symbolic ByteAuth.symbolic word width).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (encode Sha256.symbolic ByteAuth.symbolic word width))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (encode Sha256.symbolic ByteAuth.symbolic word width))).vec.get index hi)) =
      (ByteCircuit.joinValue (encode Sha256.concrete ByteAuth.concrete (word.eval assign) width)).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    encode_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.Varint
