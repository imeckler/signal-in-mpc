import Lean
import TlsMpc.Signal.ReceiveAdvance

/-! Unverified JSON/native transport for the separately proved store operations. -/
open TlsMpc TlsMpc.Signal.SkippedKeys TlsMpc.Signal.ReceiveAdvance Std.Tactic.BVDecide

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

def counterAt (start : Nat) : BVExpr 32 :=
  Sha256.symbolic.pack (.var start) (.var (start+1)) (.var (start+2)) (.var (start+3))

def main (args : List String) : IO Unit := do
  let (mode, jump, count) ← match args with
    | [mode, jump, count] => match jump.toNat?, count.toNat? with
      | some j, some n => pure (mode,j,n)
      | _, _ => throw (IO.userError "jump and capacity must be natural numbers")
    | _ => throw (IO.userError "expected advance|committed maxJump capacity")
  if jump > 16 || count > 64 then throw (IO.userError "export supports maxJump0..16 capacity0..64")
  let offset := if mode == "committed" then 1 else 0
  let candidate ← match mode with
    | "advance" => pure (advance Sha256.symbolic ByteAuth.symbolic jump
        (input offset) (input (offset+32)) (counterAt (offset+64)) (counterAt (offset+68)) (slotsAt (offset+72) count))
    | "committed" => pure (committed Sha256.symbolic ByteAuth.symbolic jump (.var 0)
        (input offset) (input (offset+32)) (counterAt (offset+64)) (counterAt (offset+68)) (slotsAt (offset+72) count))
    | _ => throw (IO.userError "expected advance|committed")
  let inputs := offset+72+69*count
  let bytes := TlsMpc.Signal.ReceiveAdvance.bytes candidate
  let description := "secret auth1(committed only),ratchetKey32,chainKey32,currentBE4,targetBE4,slots69N; output found255/0,seed32,nextChain32,nextCounterBE4,candidateSlots; slot=valid1,key32,counterBE4,seed32; public maxJump and capacity; bounded advance excludes target=maxU32; failed auth/hit preserves exact old state"
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega)))
  let image : Image := {
    name := s!"signal-receive-{mode}-{jump}-{count}"
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
