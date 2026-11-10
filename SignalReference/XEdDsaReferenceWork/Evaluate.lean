import XEdDsaReferenceWork.RecoveryInput
open Aeneas Aeneas.Std XEdDsaReference

def evaluate (ns : List Nat) : Except String (List Nat) := do
  if h : ns.length = 32 then
    if ns.all (fun n => n < 256) then
      let bytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize :=
        ⟨ns.map (fun n => ⟨BitVec.ofNat 8 n⟩), by simp [h]⟩
      match backend.serial.u64.field.FieldElement51.from_bytes bytes with
      | .ok limbs => return limbs.asNat :: (RecoveryInput.represented limbs).val :: limbs.val.map (·.val)
      | _ => throw "actual decoder did not return"
    else throw "invalid byte"
  else throw "requires 32 bytes"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result := do
      let ns ← Lean.Json.parse line >>= Lean.fromJson? (α := List Nat)
      evaluate ns
    match result with
    | .ok values => stdout.putStrLn ((Lean.toJson values).compress)
    | .error message => throw (IO.userError message)
