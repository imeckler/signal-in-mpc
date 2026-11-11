import TlsMpc.FlatLowering
import TlsMpc.MlKemFastKernels
open TlsMpc Std.Tactic.BVDecide

/-! The KEM kernels of `TlsMpc/MlKemFastKernels.lean` as flat gate lists, until
`MlKemFastKernel.find` is registered in `EmitFlatKernel.lean` (which this file
copies: `selection`, `layoutText` and `lowerKernel` are unchanged).

    kem_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]

prints `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. Two more commands run Lean
VALUES, no circuit, for `check_kem_kernels.py`:

    kem_kernel_emitter reference VARIANT KEY_HEX ENTROPY_HEX
    kem_kernel_emitter stages VARIANT KEY_HEX ENTROPY_A_HEX ENTROPY_B_HEX

`reference` is the existing specification `Signal.MlKem.encapsulate` on 32-bit
words (rank 4, η = 2, 11 and 5 bits, 224 candidate pairs); `stages` is the
composition of the value instances of the stage functions. Both print
`STATUS_HEX CIPHERTEXT_HEX SECRET_HEX`. -/

def selection (fields : List HybridKernel.Output) (byteCount : Nat) :
    Except String (Array (Fin (8 * byteCount))) := do
  let mut chosen : Array (Fin (8 * byteCount)) := #[]
  let mut offset := 0
  for field in fields do
    unless field.bits ≤ 8 * field.value.length && 0 < field.bits do
      throw s!"output field {field.name} width"
    for bit in List.range field.bits do
      let i := 8 * offset + bit
      if h : i < 8 * byteCount then
        chosen := chosen.push ⟨8 * (byteCount - 1 - i / 8) + i % 8, by omega⟩
      else throw "output index"
    offset := offset + field.value.length
  pure chosen

def fieldName (name : String) : Bool := !name.isEmpty && name.all Char.isAlphanum

def layoutText (k : HybridKernel.Kernel) : String :=
  let inputs := k.inputs.map fun f => s!"I {f.1} {f.2.bits}\n"
  let outputs := k.outputs.map fun f =>
    let opened := if f.audience == 1 then 2 else if f.audience == 2 then 3 else if f.opened then 1 else 0
    s!"O {f.name} {f.bits} {opened}\n"
  "EMP_HYBRID_KERNEL_LAYOUT_V1\n" ++ String.join inputs ++ String.join outputs

def lowerKernel (k : HybridKernel.Kernel) : Except String FlatLowering.Flat := do
  let bytes := k.outputs.flatMap (·.value)
  let chosen ← selection k.outputs bytes.length
  let widths := (k.inputs.flatMap fun f => match f.2 with
    | .bytes count => List.replicate count 8
    | .word => [255]).toArray
  let names := k.inputs.map (·.1)
  unless names.eraseDups.length == names.length &&
      (k.outputs.map (·.name)).eraseDups.length == k.outputs.length do
    throw "duplicate field name"
  unless names.all fieldName && k.outputs.all (fieldName ·.name) do throw "field name"
  let flat ← FlatLowering.lowerExpr (ByteCircuit.joinExpr bytes) widths chosen
  unless (k.inputs.map (·.2.bits)).foldl (· + ·) 0 == flat.inputs &&
      (k.outputs.map (·.bits)).foldl (· + ·) 0 == flat.outputs.size do
    throw "kernel layout"
  pure flat

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0

def fromHex : List Char → List (BitVec 8)
  | a :: b :: rest => BitVec.ofNat 8 (16 * hexDigit a + hexDigit b) :: fromHex rest
  | _ => []

def toHex (bytes : List (BitVec 8)) : String :=
  String.mk (bytes.flatMap fun b => [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])

open Signal in
/-- The stage functions on values, in the order of `TlsMpc/MlKemFastKernels.lean`. -/
def stagesValue (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) : List (List (BitVec 8)) :=
  let o := MlKemFast.concrete
  let a := ByteAuth.concrete
  let k := Keccak.concrete
  let hashed := MlKemFast.hashStage o a k kyber key entropyA entropyB
  let message := hashed.getD 0 []
  let kbar := hashed.getD 1 []
  let coins := hashed.getD 2 []
  let rhat := MlKemFast.nttStage o a k coins
  let rows := (List.range 4).map (fun i => MlKemFast.matrixStage o a k i key)
  let us := (List.range 4).flatMap (fun i => MlKemFast.uStage o a k i ((rows.getD i []).getD 0 []) rhat coins)
  let v := MlKemFast.vStage o a k key rhat coins message
  MlKemFast.finishStage a k kyber (us ++ v) kbar
    (rows.flatMap (fun row => row.getD 1 []) ++ hashed.getD 3 [])

def main (args : List String) : IO Unit := do
  match args with
  | ["reference", v, key, entropy] =>
      let some kyber := MlKemFastKernel.variant v | throw (IO.userError "variant")
      let result := Signal.MlKem.encapsulate Signal.MlKemArithmetic.concrete Signal.MlKemEncoding.concrete
        Sha256.concrete ByteAuth.concrete Signal.Word64.concrete Signal.Keccak.concrete 4 2 11 5 224 kyber
        (fromHex key.toList) (fromHex entropy.toList)
      IO.println s!"{toHex [result.success]} {toHex (result.bytes.take 1568)} {toHex (result.bytes.drop 1568)}"
  | ["stages", v, key, entropyA, entropyB] =>
      let some kyber := MlKemFastKernel.variant v | throw (IO.userError "variant")
      let out := stagesValue kyber (fromHex key.toList) (fromHex entropyA.toList) (fromHex entropyB.toList)
      IO.println s!"{toHex (out.getD 0 [])} {toHex (out.getD 1 [])} {toHex (out.getD 2 [])}"
  | flatPath :: layoutPath :: "kernel" :: rest =>
      let some kernel := MlKemFastKernel.find rest
        | throw (IO.userError "unknown kernel or shape")
      match lowerKernel kernel with
      | .error message => throw (IO.userError message)
      | .ok flat =>
          let handle ← IO.FS.Handle.mk flatPath .write
          flat.print handle.putStr
          handle.flush
          IO.FS.writeFile layoutPath (layoutText kernel)
          IO.println s!"{flat.inputs} {flat.outputs.size} {flat.andCount} {flat.opa.size}"
  | _ => throw (IO.userError "kem_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS] | reference ... | stages ...")
