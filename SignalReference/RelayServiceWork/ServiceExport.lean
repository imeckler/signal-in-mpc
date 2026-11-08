import Lean
import TlsMpc.Signal.SealedRelay
open TlsMpc Std.Tactic.BVDecide
structure ServiceImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-private-sealed-relay"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  match args with
  | [certText,innerText,dw,rw,tw,iw] =>
    let some cert := certText.toNat? | throw (IO.userError "expected certificate bytes")
    let some inner := innerText.toNat? | throw (IO.userError "expected inner bytes")
    let some dw := dw.toNat? | throw (IO.userError "expected device digits")
    let some rw := rw.toNat? | throw (IO.userError "expected registration digits")
    let some tw := tw.toNat? | throw (IO.userError "expected timestamp digits")
    let some iw := iw.toNat? | throw (IO.userError "expected request id width")
    unless 0<cert ∧ cert≤1024 ∧ 0<inner ∧ inner≤4096 do throw (IO.userError "bounded sealed shape")
    let width := fun n => (Signal.Varint.publicNat ByteAuth.concrete n).length
    let usmc := 4 + width cert + cert + width inner + inner
    let sealedBytes := 92 + width (usmc+10) + usmc
    let shape : Signal.RelayRequest.Shape := ⟨sealedBytes,dw,rw,tw,iw⟩
    unless shape.valid do throw (IO.userError "invalid request shape")
    let bytes := Signal.SealedRelay.produce Aes.symbolic Sha256.symbolic Signal.RelayEncoding.decimalSymbolic
      Signal.Varint64.symbolic ByteAuth.symbolic shape
      (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32) (ByteCircuit.inputBytes 64 32)
      (ByteCircuit.inputBytes 96 32) (ByteCircuit.inputBytes 128 32)
      (ByteCircuit.inputBytes 160 cert) (ByteCircuit.inputBytes (160+cert) inner)
      (ByteCircuit.inputBytes (160+cert+inner) 32) (ByteCircuit.inputBytes (192+cert+inner) 57)
    unless bytes.length≤16384 do throw (IO.userError "private request requires fragmentation")
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : ServiceImage := {
      input_bits := 8 * (249 + cert + inner)
      input_widths := Array.replicate (249 + cert + inner) 8
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef
        (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    (← IO.getStdout).putStrLn (Lean.toJson image).compress
  | _ => throw (IO.userError "expected CERT_BYTES INNER_BYTES DEVICE_DIGITS REG_DIGITS TIMESTAMP_DIGITS ID_WIDTH")
