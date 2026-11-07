import Lean
import TlsMpc.AesInverse

/-! Unverified native serialization of the proved inverse-AES circuits. -/
namespace AesInverseExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson, Lean.FromJson, BEq

def image (name : String) (inputBytes : Nat) (output : List (BVExpr 8)) : Image :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr output)
  let outputs := Array.ofFn (fun (i : Fin (8 * output.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * output.length - 1 - i.val) (by omega)))
  { name, input_bits := 8 * inputBytes, input_widths := Array.replicate inputBytes 8,
    nodes := AigExport.exportNodes circuit.aig, outputs }

def variables (start count : Nat) : List (BVExpr 8) :=
  (List.range count).map (fun index => BVExpr.var (w := 8) (start + index))

def block (keyBytes nk rounds : Nat) : Image :=
  image s!"aes{8 * keyBytes}-decrypt-block" (keyBytes + 16)
    (AesInverse.decryptCore AesInverse.symbolic nk rounds
      (variables 0 keyBytes) (variables keyBytes 16))

def expanded (rounds : Nat) : Image :=
  let keyBytes := 16 * (rounds + 1)
  image s!"aes-decrypt-expanded-{rounds}" (keyBytes + 16)
    (AesInverse.decryptExpanded AesInverse.symbolic rounds
      (variables 0 keyBytes) (variables keyBytes 16))

end AesInverseExport

def main (args : List String) : IO Unit := do
  let image ← match args with
    | ["128"] => pure (AesInverseExport.block 16 4 10)
    | ["256"] => pure (AesInverseExport.block 32 8 14)
    | ["expanded128"] => pure (AesInverseExport.expanded 10)
    | ["expanded256"] => pure (AesInverseExport.expanded 14)
    | ["sbox"] => pure (AesInverseExport.image "inverse-sbox" 1
        [TlsMpc.AesInverse.invSboxExpr (.var 0)])
    | _ => throw (IO.userError "expected128,256,expanded128,expanded256 or sbox")
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := AesInverseExport.Image) with
  | .error error => throw (IO.userError error)
  | .ok decoded => unless decoded == image do throw (IO.userError "serialization changed artifact")
  (← IO.getStdout).putStrLn serialized
