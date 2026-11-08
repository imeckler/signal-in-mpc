import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.RelayEncoding

namespace TlsMpc.Signal.PrivateDecimal

def count (a : ByteAuth.Ops B) : List B → List B → List B
  | [],total => total
  | mask::rest,total => count a rest
    (PrivateBuffer.addLoop a total (mask::List.replicate 15 (a.const 0)) (List.range 16) (a.const 0)).1

def lengthBit (a : ByteAuth.Ops B) (masks : List B) (bit : Nat) : B :=
  (List.range 20).foldl (fun acc i => a.xor acc (a.and (OpenResult.get a masks i)
    (OpenResult.get a (PrivateBuffer.publicLength a (i+1)) bit))) (a.const 0)

def digitAt (d : RelayEncoding.DecimalOps B W) (a : ByteAuth.Ops B) (word : W) (masks : List B) (index : Nat) : B :=
  (List.range 20).foldl (fun acc i => a.xor acc
    (if index<i+1 then a.and (OpenResult.get a masks i) (d.digit word (i-index)) else a.const 0)) (a.const 0)

def encode (d : RelayEncoding.DecimalOps B W) (a : ByteAuth.Ops B) (word : W) : PrivateBuffer.Buffer B :=
  let masks := (List.range 20).map (fun i => RelayEncoding.decimalMask d a word (i+1))
  let selected := count a masks (PrivateBuffer.publicLength a 0)
  let unique := ByteAuth.equalMask a selected (PrivateBuffer.publicLength a 1)
  let bits := (List.range 16).map (lengthBit a masks)
  let raw := (List.range 20).map (digitAt d a word masks)
  PrivateProtobuf.gate a unique (PrivateBuffer.make a 20 bits raw)

section Refinement
variable {d : RelayEncoding.DecimalOps B W} {d' : RelayEncoding.DecimalOps B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hd : RelayEncoding.DecimalHom d d' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem count_map (masks total : List B) :
    (count a masks total).map f = count a' (masks.map f) (total.map f) := by
  induction masks generalizing total with
  | nil => rfl
  | cons mask rest ih =>
    simp only [count,List.map_cons,ih]
    have h := congrArg Prod.fst (PrivateBuffer.addLoop_map ha total
      (mask::List.replicate 15 (a.const 0)) (List.range 16) (a.const 0))
    simp only [List.map_cons,List.map_replicate,ha.const] at h
    rw [h]

theorem xorFold_map (is : List Nat) (g : Nat → B) (g' : Nat → B')
    (hg : ∀ i, f (g i)=g' i) (initial : B) :
    f (is.foldl (fun acc i => a.xor acc (g i)) initial) =
      is.foldl (fun acc i => a'.xor acc (g' i)) (f initial) := by
  induction is generalizing initial with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons,ih,ha.xor,hg]

theorem lengthBit_map (masks : List B) (bit : Nat) :
    f (lengthBit a masks bit) = lengthBit a' (masks.map f) bit := by
  unfold lengthBit
  rw [xorFold_map ha]
  · rw [ha.const]
  · intro i
    simp only [ha.and,OpenResult.get_map ha,PrivateBuffer.publicLength_map ha]
include hd

theorem digitAt_map (word : W) (masks : List B) (index : Nat) :
    f (digitAt d a word masks index) = digitAt d' a' (fw word) (masks.map f) index := by
  unfold digitAt
  rw [xorFold_map ha]
  · rw [ha.const]
  · intro i
    split <;> simp only [ha.and,OpenResult.get_map ha,hd.digit,ha.const]

theorem encode_map (word : W) :
    (encode d a word).map f = encode d' a' (fw word) := by
  simp only [encode,PrivateProtobuf.gate_map ha,PrivateBuffer.make_map ha,ByteAuth.equalMask_map ha,
    count_map ha,PrivateBuffer.publicLength_map ha,List.map_map,Function.comp_def,
    lengthBit_map ha,digitAt_map hd ha,RelayEncoding.decimalMask_map ha hd]

end Refinement
end TlsMpc.Signal.PrivateDecimal
