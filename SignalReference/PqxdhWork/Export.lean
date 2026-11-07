import Lean
import TlsMpc.Signal.Pqxdh
import TlsMpc.X25519

/-! JSON transport for the separately proved field and Boolean stages. -/
open TlsMpc Std.Tactic.BVDecide

structure PqxdhImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def dhFieldNode (node : FieldDag.Node) : Lean.Json :=
  match node with
  | .input i => Lean.Json.mkObj [("op", Lean.toJson "input"), ("index", Lean.toJson i)]
  | .const x => Lean.Json.mkObj [("op", Lean.toJson "const"), ("value", Lean.toJson (toString x))]
  | .bin op x y => Lean.Json.mkObj [("op", Lean.toJson (match op with
      | .add => "add" | .sub => "sub" | .mul => "mul")),
      ("left", Lean.toJson x), ("right", Lean.toJson y)]

structure DhFieldImage where
  format : String := "tls-mpc-field-dag-v1"
  name : String := "x25519"
  modulus : String := toString FieldDag.modulus
  input_count : Nat := 257
  bit_inputs : Array Nat := (List.range 256).toArray
  nodes : Array Lean.Json
  outputs : Array Nat
  input_description : String := "secret 256 scalar bits in global LSB order, then peer u field element decoded from32 bytes with top bit masked; scalar clamping inside circuit; canonical shared field output feeds PQXDH agreement input slots via private conversion"
  deriving Lean.ToJson, Lean.FromJson, BEq

def dhEmit [Lean.ToJson A] [Lean.FromJson A] [BEq A] (value : A) : IO Unit := do
  let text := (Lean.toJson value).compress
  match Lean.Json.parse text >>= Lean.fromJson? (α := A) with
  | .error message => throw (IO.userError s!"JSON round-trip failed: {message}")
  | .ok decoded => unless decoded == value do throw (IO.userError "JSON round-trip changed artifact")
  (← IO.getStdout).putStrLn text

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-dh-field"] =>
      match FieldDag.compile X25519.expr with
      | none => throw (IO.userError "X25519 field compilation failed translation validation")
      | some artifact =>
          dhEmit ({ nodes := artifact.nodes.toArray.map dhFieldNode
                    outputs := #[artifact.output] } : DhFieldImage)
  | [profile] =>
      unless profile == "none" || profile == "present" do
        throw (IO.userError "expected none or present")
      let optional := if profile == "present" then 32 else 0
      let inputCount := 128 + optional
      let bytes := Signal.Pqxdh.deriveCore Sha256.symbolic
        (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)
        (ByteCircuit.inputBytes 64 32) (ByteCircuit.inputBytes 96 optional)
        (ByteCircuit.inputBytes (96 + optional) 32)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
        AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
      dhEmit ({
        name := "signal-pqxdh-" ++ profile
        input_bits := inputCount * 8
        input_widths := Array.replicate inputCount 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := outputs
        input_description := "secret DH1[32] || DH2[32] || DH3[32] || optionalDH4[0/32] || KyberSS[32]; presence public; output root[32] || chain[32] || initialPQR[32]; bytes are MSB-first wires; no agreement/KEM/identity validation in this KDF artifact; actual Rust wrapper equivalence unresolved" } : PqxdhImage)
  | _ => throw (IO.userError "expected none, present, or signal-dh-field")
