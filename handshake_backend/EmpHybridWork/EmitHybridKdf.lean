import Lean
import TlsMpc.HybridKdf
import TlsMpc.HybridSend
import TlsMpc.HybridService
import TlsMpc.HybridKernels
import TlsMpc.EstablishKernels
import TlsMpc.TlsRecord
import TlsMpc.TlsReceive
open TlsMpc Std.Tactic.BVDecide

/-! Export the key-derivation circuits that consume the X25519 word directly.
Variable 0 is the 255-bit word; variables 1..32 are bytes. Output `8*j + b` is
bit `b` (weight `2^b`) of output byte `j`, so inputs and outputs use one bit
order throughout. The JSON transport and the lowering are outside the theorems. -/

structure KdfImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat := 511
  input_widths : Array Nat := #[255] ++ Array.replicate 32 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson, Lean.FromJson, BEq

def image (name : String) (bytes : List (BVExpr 8)) : KdfImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let n := bytes.length
  { name, nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun k : Fin (8 * n) =>
      AigExport.exportRef (circuit.vec.get (8 * (n - 1 - k.val / 8) + k.val % 8) (by omega))) }

/-- Byte-input circuits: every variable is one byte. Same output order. -/
def byteImage (name : String) (inputBytes : Nat) (bytes : List (BVExpr 8)) : KdfImage :=
  { image name bytes with input_bits := 8 * inputBytes, input_widths := Array.replicate inputBytes 8 }

def emit (image : KdfImage) : IO Unit := do
  let encoded := (Lean.toJson image).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := KdfImage) with
    | .ok value => pure value | .error _ => throw (IO.userError "image decode")
  unless decoded == image do throw (IO.userError "image mismatch")
  (← IO.getStdout).putStrLn encoded

/-- A worker kernel with its named field layout (TlsMpc/HybridKernels.lean). -/
structure KernelImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_fields : Array (String × Nat)
  /-- name, bits, and 0 private / 1 public / 2 garbling party only / 3 evaluating party only -/
  output_fields : Array (String × Nat × Nat)
  deriving Lean.ToJson

def kernelImage (k : HybridKernel.Kernel) : Except String KernelImage := do
  let bytes := k.outputs.flatMap (·.value)
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let n := bytes.length
  let all := Array.ofFn (fun i : Fin (8 * n) =>
    AigExport.exportRef (circuit.vec.get (8 * (n - 1 - i.val / 8) + i.val % 8) (by omega)))
  let mut refs : Array (Nat × Nat) := #[]
  let mut offset := 0
  for field in k.outputs do
    unless field.bits ≤ 8 * field.value.length && 0 < field.bits do throw s!"output field {field.name} width"
    for bit in List.range field.bits do
      let some ref := all[8 * offset + bit]? | throw "output index"
      refs := refs.push ref
    offset := offset + field.value.length
  let names := k.inputs.map (·.1) ++ []
  unless names.eraseDups.length == names.length && ((k.outputs.map (·.name)).eraseDups.length == k.outputs.length) do
    throw "duplicate field name"
  pure { name := k.name
         input_bits := (k.inputs.map (·.2.bits)).foldl (· + ·) 0
         input_widths := (k.inputs.flatMap (fun f => match f.2 with
           | .bytes count => List.replicate count 8 | .word => [255])).toArray
         nodes := AigExport.exportNodes circuit.aig
         outputs := refs
         input_fields := (k.inputs.map (fun f => (f.1, f.2.bits))).toArray
         output_fields := (k.outputs.map (fun f =>
           (f.name, f.bits, if f.audience == 1 then 2 else if f.audience == 2 then 3 else if f.opened then 1 else 0))).toArray }

def main (args : List String) : IO Unit := do
  if let "kernel" :: rest := args then
    let some kernel := HybridKernel.find rest <|> EstablishKernel.find rest | throw (IO.userError "unknown kernel or shape")
    match kernelImage kernel with
    | .ok image => (← IO.getStdout).putStrLn (Lean.toJson image).compress
    | .error message => throw (IO.userError message)
    return
  if let ["signal-two-sends", size, pqSize, cw, pw, addresses] := args then
    let (some size, some pqSize, some cw, some pw) := (size.toNat?, pqSize.toNat?, cw.toNat?, pw.toNat?)
      | throw (IO.userError "signal-two-sends SIZE PQ_SIZE COUNTER_WIDTH PREVIOUS_WIDTH none|present")
    unless addresses == "none" || addresses == "present" do throw (IO.userError "none|present")
    let shape : Signal.Serialization.Shape := ⟨cw, pw, addresses == "present"⟩
    unless shape.valid do throw (IO.userError "counter widths must be 1..5")
    if size > 1024 || pqSize > 1024 then throw (IO.userError "payload sizes must be at most 1024")
    emit (byteImage "hybrid-signal-two-sends" (HybridSend.inputBytes shape size pqSize)
      (HybridSend.twoSends shape size pqSize))
    return
  if let ["tls-open-handshake", size] := args then
    let some size := size.toNat? | throw (IO.userError "tls-open-handshake WIRE_SIZE")
    if size < 22 || size > 16645 then throw (IO.userError "handshake wire size 22..16645")
    emit (byteImage "hybrid-tls-open-handshake" (36 + size) (HybridKdf.tlsOpenHandshake size))
    return
  if let ["tls-finish", certificate] := args then
    let some certificate := certificate.toNat? | throw (IO.userError "tls-finish CERTIFICATE_SIZE")
    if certificate > 64 then throw (IO.userError "client certificate message at most 64 bytes")
    emit (byteImage "hybrid-tls-finish" (156 + certificate) (HybridKdf.tlsFinish certificate))
    return
  if args == ["tls-verify-finished"] then
    emit (byteImage "hybrid-tls-verify-finished" 100 HybridKdf.tlsVerifyFinished)
    return
  if args == ["tls-update-traffic"] then
    emit (byteImage "hybrid-tls-update-traffic" 32 HybridKdf.tlsUpdateTraffic)
    return
  if let ["tls-open-application", size] := args then
    let some size := size.toNat? | throw (IO.userError "tls-open-application WIRE_SIZE")
    if size < 22 || size > 16406 then throw (IO.userError "wire size 22..16406")
    emit (byteImage "hybrid-tls-open-application" (47 + size) (HybridKdf.tlsOpenApplication size))
    return
  if let ["tls-seal-control", kind, size] := args then
    let (some kind, some size) := (kind.toNat?, size.toNat?) | throw (IO.userError "tls-seal-control KIND SIZE")
    unless (kind == 21 && size == 2) || (kind == 22 && size == 5) do
      throw (IO.userError "control records: alert (21, 2 bytes) or KeyUpdate (22, 5 bytes)")
    emit (byteImage "hybrid-tls-seal-control" (36 + size) (HybridKdf.tlsSeal size kind 0))
    return
  if args == ["tls-derive"] then
    emit (image "hybrid-tls-derive" HybridKdf.tlsDerive)
    return
  if let ["tls-seal-record", size, padding] := args then
    let (some size, some padding) := (size.toNat?, padding.toNat?) | throw (IO.userError "tls-seal-record SIZE PADDING")
    if size == 0 || size + 1 + padding > 16385 then throw (IO.userError "record size")
    emit (byteImage "hybrid-tls-seal-record" (36 + size)
      (TlsRecord.sealCore Gcm.symbolic (ByteCircuit.inputBytes 0 16) (ByteCircuit.inputBytes 16 12)
        (ByteCircuit.inputBytes 28 8) (ByteCircuit.inputBytes 36 size) 23 padding))
    return
  if let ["tls-open-record", size] := args then
    let some size := size.toNat? | throw (IO.userError "tls-open-record WIRE_SIZE")
    if size < 22 || size > 16406 then throw (IO.userError "wire size 22..16406")
    emit (byteImage "hybrid-tls-open-record" (36 + size)
      (TlsReceive.openCore Gcm.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)
        (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8) (ByteCircuit.inputBytes 36 size)))
    return
  let [mode] := args | throw (IO.userError "tls-handshake-secrets|signal-dh-ratchet")
  let image ← match mode with
    | "tls-handshake-secrets" => pure (image "hybrid-tls-handshake-secrets" HybridKdf.tlsHandshakeSecrets)
    | "signal-dh-ratchet" => pure (image "hybrid-signal-dh-ratchet" HybridKdf.signalDhRatchet)
    | _ => throw (IO.userError "unknown key-derivation circuit")
  let encoded := (Lean.toJson image).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := KdfImage) with
    | .ok value => pure value | .error _ => throw (IO.userError "kdf image decode")
  unless decoded == image do throw (IO.userError "kdf image mismatch")
  (← IO.getStdout).putStrLn encoded
