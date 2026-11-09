import AesCtrBlockWork.FixsliceCircuitV1Work.Cipher16
import TlsMpc.Aes
import Lean
namespace FixsliceCost
open TlsMpc Std.Tactic.BVDecide
open LibSignalReference.Candidate.FixsliceCircuitV1
structure Image where
 format : String := "tls-mpc-aig-v1"
 «name» : String
 input_bits : Nat
 input_widths : Array Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson

def bytes (reference : Bool) (blocks repeats : Nat) : List (BVExpr 8) :=
 let key := fun i => (BVExpr.var i : BVExpr 8)
 let groups := keyGroupsExpression key
 let expanded := Aes.expandKey Aes.symbolic 8 14 (ByteCircuit.inputBytes 0 32)
 (List.range repeats).flatMap fun repetition =>
  let plain := fun i => (BVExpr.var (32 + 16 * blocks * repetition + i) : BVExpr 8)
  if reference then
   (List.range blocks).flatMap fun block =>
    Aes.encryptExpanded Aes.symbolic 14 expanded ((List.range 16).map (fun i => plain (16 * block + i)))
  else if blocks == 1 then expression16 ⟨0, by decide⟩ groups (singleInput plain)
  else expression64 groups (fun block byte => plain (16 * block + byte))

def artifact (reference : Bool) (blocks repeats : Nat) : Image :=
 let result := bytes reference blocks repeats
 let circuit := AigExport.compile (ByteCircuit.joinExpr result)
 let outputs := Array.ofFn (fun (i : Fin (8 * result.length)) =>
  AigExport.exportRef (circuit.vec.get (8 * result.length - 1 - i.val) (by omega)))
 let count := 32 + 16 * blocks * repeats
 { «name» := s!"aes256-{if reference then "ordinary" else "fixslice"}-{blocks}x{repeats}"
   input_bits := count * 8, input_widths := Array.replicate count 8
   nodes := AigExport.exportNodes circuit.aig, outputs }
end FixsliceCost

def main (args : List String) : IO Unit := do
 let reference := args[0]?.getD "candidate" == "reference"
 let blocks := (args[1]?.getD "1").toNat?.getD 0
 let repeats := (args[2]?.getD "1").toNat?.getD 0
 unless (blocks == 1 || blocks == 4) && (repeats == 1 || repeats == 2) do
  throw (IO.userError "public profile must be 1/4 blocks, 1/2 calls")
 (← IO.getStdout).putStrLn ((Lean.toJson (FixsliceCost.artifact reference blocks repeats)).compress)
