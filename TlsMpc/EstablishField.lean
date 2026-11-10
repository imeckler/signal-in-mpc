import TlsMpc.Signal.XEdDsaField
import TlsMpc.FieldDagMulti

/-!
Field programs for verifying a prekey signature (XEdDSA) during session
establishment, as multi-output programs over p = 2^255 − 19. They are the
existing formulas of `TlsMpc/Signal/XEdDsaField.lean` (complete extended
Edwards addition, fixed double-and-add loops, Fermat inversions; no division,
so no input can make the runtime abort), exported together so that the
outputs share their common nodes.

* `recover` — input 0: the identity key's Montgomery `u`.
  Outputs: `valid` (1 or 0), `x` (a square root, sign not yet chosen), `y`.
* `check` — inputs: 0 `x`, 1 `y`, 2 `flip` (a bit), 3 + i: bit i of the
  challenge `h` (i < 256), 259 + i: bit i of the signature scalar `s`
  (i < 253). Outputs: the affine coordinates of `[s]B − [h]A`, where
  `A = (±x, y)` with the sign chosen by `flip`.

Proved: every accepted compilation of either program computes these formulas
on every input (`recover_correct`, `check_correct`). Not proved: that the
formulas are the Edwards group law or agree with the Rust implementation
(tested numerically in `SignalReference/XEdDsaWork`).
-/
namespace TlsMpc.EstablishField
open FieldDag Signal

def recover : List Expr := XEdDsaField.run X25519.symbolic true Expr.input

def check : List Expr := XEdDsaField.signedRun X25519.symbolic Expr.input

theorem recover_correct (artifact : MultiArtifact) (compiled : compileAll recover = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) = XEdDsaField.run X25519.concrete true input := by
  rw [compileAll_correct _ _ compiled]
  exact XEdDsaField.run_map (X25519.evaluationHom input) true Expr.input

theorem check_correct (artifact : MultiArtifact) (compiled : compileAll check = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) = XEdDsaField.signedRun X25519.concrete input := by
  rw [compileAll_correct _ _ compiled]
  exact XEdDsaField.signedRun_map (X25519.evaluationHom input) Expr.input

/-- Program named on the command line: input count, the inputs that must be
bits, and the output expressions. -/
def find : String → Option (Nat × List Nat × List Expr)
  | "xeddsa-recover" => some (1, [], recover)
  | "xeddsa-check" => some (512, (List.range 510).map (· + 2), check)
  | _ => none

#print axioms recover_correct
#print axioms check_correct

end TlsMpc.EstablishField
