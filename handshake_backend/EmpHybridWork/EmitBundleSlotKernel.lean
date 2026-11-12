import TlsMpc.FlatLowering
import TlsMpc.BundleSlotKernels
open TlsMpc Std.Tactic.BVDecide

/-! The `bundle-slot` kernels of `TlsMpc/BundleSlotKernels.lean` as flat gate lists.

    bundle_slot_emitter FLAT_PATH LAYOUT_PATH kernel bundle-slot FIRST LAST ONETIME
    bundle_slot_emitter splice D R S P K        (the runtime's splice, for the checks)

The first prints `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. An executable of its own (as
`ceremony_kernel_emitter` is) so that adding these kernels does not change `flat_kernel_emitter`,
whose hash keys the cache of every other circuit; `selection`, `layoutText` and `lowerKernel` are
copied from `EmitFlatKernel.lean` unchanged. `circuit_cache.py` sends kernel names that start with
`bundle-slot` here. -/

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
  if let "splice" :: digits := args then
    let some [d, r, s, p, k] := digits.mapM (·.toNat?) | throw (IO.userError "splice D R S P K")
    let w : Signal.BundleResponse.Widths := ⟨d, r, s, p, k⟩
    unless w.ok do throw (IO.userError "widths out of range")
    for (zeros, copy) in Signal.BundleSlots.splice w do IO.println s!"{zeros} {copy}"
    return
  let flatPath :: layoutPath :: "kernel" :: rest := args
    | throw (IO.userError "bundle_slot_emitter FLAT_PATH LAYOUT_PATH kernel bundle-slot FIRST LAST ONETIME | splice D R S P K")
  let some kernel := BundleSlotKernel.find rest | throw (IO.userError "unknown kernel or shape")
  match lowerKernel kernel with
  | .error message => throw (IO.userError message)
  | .ok flat =>
      let handle ← IO.FS.Handle.mk flatPath .write
      flat.print handle.putStr
      handle.flush
      IO.FS.writeFile layoutPath (layoutText kernel)
      IO.println s!"{flat.inputs} {flat.outputs.size} {flat.andCount} {flat.opa.size}"
