import Lean
import TlsMpc.Signal.SkippedKeys

/-! Unverified JSON/native transport for the separately proved store operations. -/
open TlsMpc TlsMpc.Signal.SkippedKeys Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def input (start : Nat) : Bytes (BVExpr 8) n := fun i => .var (start + i.val)

def slotsAt (start count : Nat) : List (Slot (BVExpr 8)) :=
  (List.range count).map fun i =>
    let base := start + 69 * i
    ⟨.var base, input (base+1), input (base+33), input (base+37)⟩

def main (args : List String) : IO Unit := do
  let (mode, count) ← match args with
    | [mode, count] => match count.toNat? with
      | some n => pure (mode,n)
      | none => throw (IO.userError "capacity must be a natural number")
    | _ => throw (IO.userError "expected lookup|consume|insert and public capacity0..64")
  if count > 64 then throw (IO.userError "export supports capacity0..64")
  let (inputs, bytes, description) ← match mode with
    | "lookup" => pure (36+69*count,
        lookupBytes ByteAuth.symbolic (input 0) (input 32) (slotsAt 36 count),
        "secret queryKey32,counterBE4,slots; slot=valid255,key32,counterBE4,seed32 newest first; output found255/0,seed32,candidateSlots; first match removed by stable compaction and empty tail; caller must authenticate before commit")
    | "consume" => pure (37+69*count,
        consumeBytes ByteAuth.symbolic (.var 0) (input 1) (input 33) (slotsAt 37 count),
        "secret authentication1,queryKey32,counterBE4,slots; slot=valid255,key32,counterBE4,seed32 newest first; output committed255/0,releasedSeed32,nextSlots; only auth255+hit commits; failure preserves exact slots and zeros seed")
    | "insert" => pure (68+69*count,
        storeBytes (insertFront ByteAuth.symbolic (input 0) (input 32) (input 36) (slotsAt 68 count)),
        "secret newKey32,counterBE4,seed32,slots; output fixed-capacity slots; prepend valid255, retain newest, drop last; no deduplication; slots and all identifiers remain shared")
    | _ => throw (IO.userError "expected lookup|consume|insert")
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega)))
  let image : Image := {
    name := s!"signal-skipped-{mode}-{count}"
    input_bits := 8*inputs
    input_widths := Array.replicate inputs 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := outputs
    input_description := description }
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == image do throw (IO.userError "JSON round-trip changed artifact")
  (← IO.getStdout).putStrLn serialized
