import TlsMpc.ByteAuth

/-!
Bounded final-block unpadding. All sixteen bytes, the acceptance mask, retained
length, and output bytes stay secret. The output is mask || length || 16 bytes;
reject produces eighteen zero bytes. All branches inspect public indices.
-/

namespace TlsMpc.Signal.Unpad

open Std.Tactic.BVDecide

def chooseByte (o : ByteAuth.Ops B) (mask yes no : B) : B :=
  o.xor (o.and mask (o.xor yes no)) no

def choose (o : ByteAuth.Ops B) (mask : B) (yes no : List B) : List B :=
  List.zipWith (chooseByte o mask) yes no

def caseMask (o : ByteAuth.Ops B) (block : List B) (count : Nat) : B :=
  ByteAuth.equalMask o (block.drop (16 - count)) (List.replicate count (o.const count))

def retained (o : ByteAuth.Ops B) (block : List B) (count : Nat) : List B :=
  [o.const 255, o.const (16 - count)] ++ block.take (16 - count) ++
    List.replicate count (o.const 0)

def decodeCases (o : ByteAuth.Ops B) (block : List B) : List Nat → List B
  | [] => List.replicate 18 (o.const 0)
  | count :: counts => choose o (caseMask o block count) (retained o block count)
      (decodeCases o block counts)

def decode (o : ByteAuth.Ops B) (block : List B) : List B :=
  decodeCases o block ((List.range 16).map (· + 1))

theorem chooseByte_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (mask yes no : B) :
    f (chooseByte a mask yes no) = chooseByte b (f mask) (f yes) (f no) := by
  simp only [chooseByte, h.xor, h.and]

theorem choose_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (mask : B) (yes no : List B) :
    (choose a mask yes no).map f = choose b (f mask) (yes.map f) (no.map f) := by
  induction yes generalizing no with
  | nil => rfl
  | cons y ys ih => cases no <;> simp [choose, chooseByte_map h, ih]

theorem caseMask_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (block : List B) (count : Nat) :
    f (caseMask a block count) = caseMask b (block.map f) count := by
  simp [caseMask, ByteAuth.equalMask_map h, h.const]

theorem retained_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (block : List B) (count : Nat) :
    (retained a block count).map f = retained b (block.map f) count := by
  simp [retained, h.const]

theorem decodeCases_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (block : List B) (counts : List Nat) :
    (decodeCases a block counts).map f = decodeCases b (block.map f) counts := by
  induction counts with
  | nil => simp [decodeCases, h.const]
  | cons count counts ih =>
    simp only [decodeCases, choose_map h, caseMask_map h, retained_map h, ih]

theorem decode_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (block : List B) :
    (decode a block).map f = decode b (block.map f) := by
  exact decodeCases_map h block _

theorem chooseByte_accept (yes no : BitVec 8) : chooseByte ByteAuth.concrete 255 yes no = yes := by
  change ((255 : BitVec 8) &&& (yes ^^^ no)) ^^^ no = yes
  have h : ((255 : BitVec 8) &&& (yes ^^^ no)) = (yes ^^^ no) := BitVec.allOnes_and
  rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem chooseByte_reject (yes no : BitVec 8) : chooseByte ByteAuth.concrete 0 yes no = no := by
  change ((0 : BitVec 8) &&& (yes ^^^ no)) ^^^ no = no
  have h : ((0 : BitVec 8) &&& (yes ^^^ no)) = 0 := BitVec.zero_and
  rw [h]
  exact BitVec.zero_xor

theorem choose_accept (yes no : List (BitVec 8)) (hlen : yes.length = no.length) :
    choose ByteAuth.concrete 255 yes no = yes := by
  induction yes generalizing no with
  | nil => rfl
  | cons y ys ih => cases no with
    | nil => simp at hlen
    | cons n ns =>
      have ht : ys.length = ns.length := Nat.succ.inj hlen
      change chooseByte ByteAuth.concrete 255 y n :: choose ByteAuth.concrete 255 ys ns = y :: ys
      rw [chooseByte_accept, ih ns ht]

theorem choose_reject (yes no : List (BitVec 8)) (hlen : yes.length = no.length) :
    choose ByteAuth.concrete 0 yes no = no := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all [choose]
  | cons y ys ih => cases no with
    | nil => rfl
    | cons n ns =>
      have ht : ys.length = ns.length := Nat.succ.inj hlen
      change chooseByte ByteAuth.concrete 0 y n :: choose ByteAuth.concrete 0 ys ns = n :: ns
      rw [chooseByte_reject, ih ns ht]

theorem retained_length (o : ByteAuth.Ops B) (block : List B) (hblock : block.length = 16)
    (count : Nat) (hcount : count ≤ 16) : (retained o block count).length = 18 := by
  simp only [retained, List.length_append, List.length_cons, List.length_nil,
    List.length_take, List.length_replicate, hblock]
  omega

theorem decodeCases_length (o : ByteAuth.Ops B) (block : List B) (hblock : block.length = 16)
    (counts : List Nat) (hcounts : ∀ count ∈ counts, count ≤ 16) :
    (decodeCases o block counts).length = 18 := by
  induction counts with
  | nil => simp [decodeCases]
  | cons count counts ih =>
    simp only [decodeCases, choose, List.length_zipWith,
      retained_length o block hblock count (hcounts count (by simp)),
      ih (by intro n hn; exact hcounts n (by simp [hn])), Nat.min_self]

theorem compiled_decode_correct (block : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (decode ByteAuth.symbolic block).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (decode ByteAuth.symbolic block))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (decode ByteAuth.symbolic block))).vec.get index hi)) =
      (ByteCircuit.joinValue (decode ByteAuth.concrete
        (block.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, decode_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.Unpad
