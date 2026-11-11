import TlsMpc.FlatLowering
import TlsMpc.HybridKernels
import TlsMpc.EstablishKernels
import TlsMpc.ReceiveKernels
open TlsMpc Std.Tactic.BVDecide

/-! Worker kernels straight to the flat gate list, without the Python lowering.

    flat_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]

writes the `EMP_HYBRID_BOOL_V1` gate list and the `EMP_HYBRID_KERNEL_LAYOUT_V1` field
layout, and prints one line: `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. Kernels, bit order and
field layout are those of `hybrid_kdf_emitter kernel ...` followed by `hybrid_lowering.py`:
variable `v`, bit `b` (weight `2^b`) is wire `offset(v) + b`; a field's bit `b` of byte `j`
is its output `8 * j + b`.

The gate list is `FlatLowering.lowerExpr` of the kernel's joined output bytes, so
`FlatLowering.lowerExpr_correct` applies to it. Outside the theorems: `selection` (which bit
of the joined value each named output bit is), the layout rows, and the text. -/

/-- For every output bit, in field order, its bit index in the joined value. `byteCount` is
the number of output bytes of all fields together; byte 0 is the most significant byte of
the joined value. -/
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

def main (args : List String) : IO Unit := do
  let flatPath :: layoutPath :: "kernel" :: rest := args
    | throw (IO.userError "flat_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]")
  let some kernel := HybridKernel.find rest <|> EstablishKernel.find rest <|> ReceiveKernel.find rest
    | throw (IO.userError "unknown kernel or shape")
  match lowerKernel kernel with
  | .error message => throw (IO.userError message)
  | .ok flat =>
      let handle ← IO.FS.Handle.mk flatPath .write
      flat.print handle.putStr
      handle.flush
      IO.FS.writeFile layoutPath (layoutText kernel)
      IO.println s!"{flat.inputs} {flat.outputs.size} {flat.andCount} {flat.opa.size}"
