import TlsMpc.Sha256
import TlsMpc.ByteCircuit

/-!
A SHA-256 circuit backend whose 32-bit addition is an explicit ripple-carry
adder with ONE AND gate per bit:

  sum_i   = a_i ⊕ b_i ⊕ c_i
  c_(i+1) = c_i ⊕ ((a_i ⊕ c_i) ∧ (b_i ⊕ c_i))

The default backend uses the bit-vector `add` node, which the AIG compiler
expands to about three AND nodes per bit. Here the adder is written out bit by
bit, proved equal to bit-vector addition (`addValue_eq`, by induction against
the library's carry function; standard axioms only), and
packaged as a `Sha256.Ops` with a homomorphism to the concrete operations, so
every existing refinement theorem that is generic in the operations applies.
-/
namespace TlsMpc.Sha256Ripple
open Std.Tactic.BVDecide

/-! ### The adder on values -/

def carryValue (a b c : BitVec 1) : BitVec 1 := c ^^^ ((a ^^^ c) &&& (b ^^^ c))

/-- Low `n` sum bits and the carry into bit `n`. -/
def rippleValue : (n : Nat) → BitVec 32 → BitVec 32 → BitVec n × BitVec 1
  | 0, _, _ => (0#0, 0#1)
  | n + 1, x, y =>
      let previous := rippleValue n x y
      let a := x.extractLsb' n 1
      let b := y.extractLsb' n 1
      (((a ^^^ b ^^^ previous.2) ++ previous.1).cast (by omega), carryValue a b previous.2)

def addValue (x y : BitVec 32) : BitVec 32 := (rippleValue 32 x y).1

/-! Structural proof against the library's carry function (no SAT certificate). -/

theorem carryValue_ofBool (a b c : Bool) :
    carryValue (BitVec.ofBool a) (BitVec.ofBool b) (BitVec.ofBool c) =
      BitVec.ofBool (Bool.atLeastTwo a b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem sumBit_ofBool (a b c : Bool) :
    BitVec.ofBool a ^^^ BitVec.ofBool b ^^^ BitVec.ofBool c = BitVec.ofBool (a ^^ (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bit_ofBool (x : BitVec 32) (n : Nat) : x.extractLsb' n 1 = BitVec.ofBool (x.getLsbD n) := by
  ext i hi
  have zero : i = 0 := by omega
  subst zero
  simp

/-- After `n` steps: the low `n` bits of the sum, and the library's carry into bit `n`. -/
theorem rippleValue_spec (x y : BitVec 32) (n : Nat) (bound : n ≤ 32) :
    (rippleValue n x y).1 = (x + y).extractLsb' 0 n ∧
      (rippleValue n x y).2 = BitVec.ofBool (BitVec.carry n x y false) := by
  induction n with
  | zero =>
      constructor
      · ext i hi
        omega
      · simp [rippleValue, BitVec.carry_zero]
  | succ n ih =>
      obtain ⟨low, carry⟩ := ih (by omega)
      simp only [rippleValue]
      rw [low, carry, bit_ofBool, bit_ofBool, carryValue_ofBool, sumBit_ofBool]
      constructor
      · ext i hi
        by_cases below : i < n
        · simp [BitVec.getElem_append, below]
        · have last : i = n := by omega
          subst last
          simp [BitVec.getElem_append, BitVec.getLsbD_add (show i < 32 by omega)]
      · rw [BitVec.carry_succ]

theorem addValue_eq (x y : BitVec 32) : addValue x y = x + y := by
  rw [addValue, (rippleValue_spec x y 32 (by omega)).1]
  ext i hi
  simp

/-! ### The same adder as a circuit expression -/

def rippleExpr : (n : Nat) → BVExpr 32 → BVExpr 32 → BVExpr n × BVExpr 1
  | 0, _, _ => (.const 0#0, .const 0#1)
  | n + 1, x, y =>
      let previous := rippleExpr n x y
      let a : BVExpr 1 := .extract n 1 x
      let b : BVExpr 1 := .extract n 1 y
      let c := previous.2
      (.append (.bin (.bin a .xor b) .xor c) previous.1 (by omega),
        .bin c .xor (.bin (.bin a .xor c) .and (.bin b .xor c)))

def addExpr (x y : BVExpr 32) : BVExpr 32 := (rippleExpr 32 x y).1

theorem eval_append_cast (left : BVExpr l) (right : BVExpr r) (h : w = l + r)
    (assign : BVExpr.Assignment) :
    (BVExpr.append left right h).eval assign = (left.eval assign ++ right.eval assign).cast h.symm := by
  cases h
  rfl

theorem rippleExpr_eval (assign : BVExpr.Assignment) (x y : BVExpr 32) (n : Nat) :
    ((rippleExpr n x y).1.eval assign, (rippleExpr n x y).2.eval assign) =
      rippleValue n (x.eval assign) (y.eval assign) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have first := congrArg Prod.fst ih
      have second := congrArg Prod.snd ih
      simp only at first second
      simp only [rippleExpr, rippleValue, carryValue, eval_append_cast, BVExpr.eval, BVBinOp.eval,
        first, second]

theorem addExpr_eval (assign : BVExpr.Assignment) (x y : BVExpr 32) :
    (addExpr x y).eval assign = x.eval assign + y.eval assign := by
  have h := congrArg Prod.fst (rippleExpr_eval assign x y 32)
  simp only at h
  rw [addExpr, h]
  exact addValue_eq _ _

/-! ### Backend -/

def ops : Sha256.Ops (BVExpr 8) (BVExpr 32) :=
  { Sha256.symbolic with
    add := addExpr
    sum4 := fun a b c d => addExpr (addExpr (addExpr a b) c) d
    sum5 := fun a b c d e => addExpr (addExpr (addExpr (addExpr a b) c) d) e }

def evaluationHom (assign : BVExpr.Assignment) :
    Sha256.Hom ops Sha256.concrete (BVExpr.eval assign) (BVExpr.eval assign) :=
  let h := Sha256.evaluationHom assign
  { byteConst := h.byteConst, wordConst := h.wordConst, byteXor := h.byteXor, xor := h.xor, and := h.and,
    not := h.not, rotr := h.rotr, shr := h.shr, pack := h.pack, unpack := h.unpack
    add := fun x y => addExpr_eval assign x y
    sum4 := fun x y z t => by
      show (addExpr (addExpr (addExpr x y) z) t).eval assign = _
      simp only [addExpr_eval]
      rfl
    sum5 := fun x y z t u => by
      show (addExpr (addExpr (addExpr (addExpr x y) z) t) u).eval assign = _
      simp only [addExpr_eval]
      rfl }

/-- A compression compiled with this backend computes SHA-256's compression. -/
theorem compiled_compress_correct (state : Sha256.State (BVExpr 32)) (block : List (BVExpr 32))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (Sha256.digest Sha256.symbolic (Sha256.compress ops state block)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (Sha256.digest Sha256.symbolic (Sha256.compress ops state block)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (Sha256.digest Sha256.symbolic (Sha256.compress ops state block)))).vec.get index hi)) =
    (ByteCircuit.joinValue (Sha256.digest Sha256.concrete (Sha256.compress Sha256.concrete
      (state.map (BVExpr.eval assign)) (block.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, Sha256.digest_map (Sha256.evaluationHom assign),
    Sha256.compress_map (evaluationHom assign)]

#print axioms addValue_eq
#print axioms compiled_compress_correct

end TlsMpc.Sha256Ripple
