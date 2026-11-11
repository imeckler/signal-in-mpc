import TlsMpc.Signal.Word64

/-! A second circuit for `Word64.Ops`, with a cheaper `select`.

`Word64.symbolic.select` is `(m ∧ x) ⊕ (¬m ∧ y)`: two AND gates per bit.
`y ⊕ (m ∧ (x ⊕ y))` is the same function with one. Everything else is
`Word64.symbolic`. A circuit that runs a per-byte state machine over 64-bit
words (the TLS post-handshake framing) spends most of its gates in selects.

`evaluationHomMux` is the statement of `Word64.evaluationHom` for this circuit:
it refines the same `Word64.concrete`, so every theorem stated for a `Hom`
applies to it unchanged. -/
namespace TlsMpc.Signal.Word64
open Std.Tactic.BVDecide

theorem mux_eq (m x y : BitVec w) : y ^^^ (m &&& (x ^^^ y)) = (m &&& x) ^^^ (~~~m &&& y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases m.getLsbD i <;> cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

def symbolicMux : Ops (BVExpr 8) (BVExpr 64) :=
  { symbolic with
    select := fun mask x y =>
      let m : BVExpr 64 := .replicate 8 mask rfl
      BvConstruct.bin y .xor (BvConstruct.bin m .and (BvConstruct.bin x .xor y)) }

def evaluationHomMux (assign : BVExpr.Assignment) :
    Hom symbolicMux concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  have h := evaluationHom assign
  constructor
  · exact h.const
  · exact h.pack
  · exact h.unpack
  · exact h.add
  · exact h.sub
  · exact h.shift
  · exact h.band
  · exact h.ule
  · intro mask x y
    simp [symbolicMux, concrete, BVExpr.eval_replicate, mux_eq]

end TlsMpc.Signal.Word64
