import TlsMpc.ReceiveField
open TlsMpc

/-! CHECK ONLY: evaluate the field program `receive-torsion` (its Lean
definition on field values) for the coordinates given on the command line, so
that `check_receive_kernels.py` can compare it with an independent computation.
Run with `lake env lean --run`. -/
def main (args : List String) : IO Unit := do
  let [x, y] := args.filterMap String.toNat? | throw (IO.userError "EvalReceiveField X Y")
  let out := ReceiveField.torsionRun X25519.concrete (fun i => FieldDag.ofNat (if i = 0 then x else y))
  IO.println (" ".intercalate (out.map (fun value => toString value.val)))
