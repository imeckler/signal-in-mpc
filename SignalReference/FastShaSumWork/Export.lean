import Lean
import TlsMpc.Sha256CarrySave
open TlsMpc Std.Tactic.BVDecide
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure ShaImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  let [version,profile] := args | throw (IO.userError "expected legacy|carry profile")
  unless version="legacy" || version="carry" do throw (IO.userError "unknown version")
  let count ← match profile with
    | "double" => pure 4
    | "pair3" | "sum3" => pure 12
    | "sum4" => pure 16
    | "sum5" => pure 20
    | "round" => pure 36
    | "block-fixed" => pure 64
    | "block-state" => pure 96
    | _ => throw (IO.userError "unknown profile")
  let o := Sha256.symbolic
  let raw := ByteCircuit.inputBytes 0 count
  let words := Sha256.packWords o raw
  let get := fun i => words[i]?.getD (o.wordConst 0)
  let state : Sha256.State (BVExpr 32) := ⟨get 0,get 1,get 2,get 3,get 4,get 5,get 6,get 7⟩
  let unpack := fun word => (List.range 4).map (o.unpack word)
  let bytes ← match profile with
    | "double" => pure (unpack (o.add (get 0) (get 0)))
    | "pair3" =>
      let pair := Sha256CarrySave.three o (get 0) (get 1) (get 2)
      pure (unpack pair.1++unpack pair.2)
    | "sum3" => pure (unpack (if version="legacy" then o.add (o.add (get 0) (get 1)) (get 2)
        else Sha256CarrySave.sum3 o (get 0) (get 1) (get 2)))
    | "sum4" => pure (unpack (if version="legacy" then o.add (o.add (o.add (get 0) (get 1)) (get 2)) (get 3)
        else Sha256CarrySave.sum4 o (get 0) (get 1) (get 2) (get 3)))
    | "sum5" => pure (unpack (if version="legacy" then o.add (o.add (o.add (o.add (get 0) (get 1)) (get 2)) (get 3)) (get 4)
        else Sha256CarrySave.sum5 o (get 0) (get 1) (get 2) (get 3) (get 4)))
    | "round" => pure (Sha256.digest o (if version="legacy" then Sha256.round o 0x428a2f98 (get 8) state
        else Sha256CarrySave.round o 0x428a2f98 (get 8) state))
    | "block-fixed" => pure (Sha256.digest o (if version="legacy" then Sha256.compress o (Sha256.initial o) words
        else Sha256CarrySave.compress o (Sha256.initial o) words))
    | "block-state" => pure (Sha256.digest o (if version="legacy" then Sha256.compress o state (words.drop 8)
        else Sha256CarrySave.compress o state (words.drop 8)))
    | _ => throw (IO.userError "unreachable profile")
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let image : ShaImage := {
    name := s!"sha-{version}-{profile}"
    input_bits := 8*count
    input_widths := Array.replicate count 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
      (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
  (← IO.getStdout).putStrLn (Lean.toJson image).compress
