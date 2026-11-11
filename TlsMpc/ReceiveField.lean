import TlsMpc.Signal.XEdDsaField
import TlsMpc.Signal.XEdDsaScalar
import TlsMpc.FieldDagMulti

/-!
Field program for receiving a first message: the torsion check of the
sender's base key that libsignal's PQXDH responder performs
(`rust/core/src/curve.rs`, `is_canonical` → `is_torsion_free`: the Montgomery
point is mapped to Edwards form with sign 0 and multiplied by the group order;
the result must be the identity). The range half of `is_canonical` is Boolean
(`ReceiveFirst.canonicalRange`).

* `torsion` — inputs 0, 1: the Edwards coordinates `x`, `y` that
  `xeddsa-recover` (`TlsMpc/EstablishField.lean`) returns for the base key's
  Montgomery `u` (either root; the check does not depend on the sign).
  Outputs: `X` and `Y − Z` of `[ℓ](x, y)` in extended coordinates, with the
  existing complete addition and the fixed public bits of
  `ℓ = 2^252 + 27742317777372353535851937790883648493`. The point is torsion
  free exactly when both outputs are zero (and `xeddsa-recover` reported a
  valid point). No division, so no input can make the runtime abort.

Reused as they are: `x25519-fast` (shared scalar · private point) for the
three agreements with our identity key and for the new ratchet key;
`xeddsa-recover` and `xeddsa-check` for the sender certificate's signature and
for the base key's Edwards coordinates. The agreements with our signed and
one-time prekeys have a PUBLIC scalar: they are the same ladder with the swap
bits supplied as public constants (`TlsMpc/X25519SwapBits.lean`); no new
program is defined for them here.

Proved: every accepted compilation computes this formula on every input
(`torsion_correct`). Not proved: that the formula is the Edwards group law or
agrees with curve25519-dalek (tested numerically by `check_receive_kernels.py`).
-/
namespace TlsMpc.ReceiveField
open FieldDag Signal

/-- The bits of the group order, most significant first. -/
def orderBits : List Bool := (List.range 253).reverse.map XEdDsaScalar.order.testBit

def torsionRun (o : X25519.Ops B) (input : Nat → B) : List B :=
  [(XEdDsaField.mul o (XEdDsaField.affine o (input 0) (input 1))
      (orderBits.map (fun bit => o.const (if bit then 1 else 0)))).x,
    o.sub (XEdDsaField.mul o (XEdDsaField.affine o (input 0) (input 1))
        (orderBits.map (fun bit => o.const (if bit then 1 else 0)))).y
      (XEdDsaField.mul o (XEdDsaField.affine o (input 0) (input 1))
        (orderBits.map (fun bit => o.const (if bit then 1 else 0)))).z]

theorem torsionRun_map {a : X25519.Ops B} {b : X25519.Ops C} {f : B → C} (h : X25519.Hom a b f) (input : Nat → B) :
    (torsionRun a input).map f = torsionRun b (f ∘ input) := by
  have hm := XEdDsaField.mul_map h (XEdDsaField.affine a (input 0) (input 1))
    (orderBits.map (fun bit => a.const (if bit then 1 else 0)))
  rw [XEdDsaField.affine_map h, List.map_map] at hm
  have hc : (f ∘ fun bit : Bool => a.const (if bit then 1 else 0)) = fun bit : Bool => b.const (if bit then 1 else 0) := by
    funext bit
    exact h.const _
  rw [hc] at hm
  have hx := congrArg XEdDsaField.Point.x hm
  have hy := congrArg XEdDsaField.Point.y hm
  have hz := congrArg XEdDsaField.Point.z hm
  simp only [XEdDsaField.Point.map] at hx hy hz
  simp only [torsionRun, List.map_cons, List.map_nil, h.sub, hx, hy, hz, Function.comp_def]

def torsion : List Expr := torsionRun X25519.symbolic Expr.input

theorem torsion_correct (artifact : MultiArtifact) (compiled : compileAll torsion = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) = torsionRun X25519.concrete input := by
  rw [compileAll_correct _ _ compiled]
  exact torsionRun_map (X25519.evaluationHom input) Expr.input

/-- Program named on the command line: input count, the inputs that must be
bits, and the output expressions. -/
def find : String → Option (Nat × List Nat × List Expr)
  | "receive-torsion" => some (2, [], torsion)
  | _ => none

#print axioms torsion_correct

end TlsMpc.ReceiveField
