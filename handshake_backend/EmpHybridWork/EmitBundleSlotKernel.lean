import TlsMpc.FlatLowering
import TlsMpc.FlatKernelLayout
import TlsMpc.BundleSlotKernels
open TlsMpc Std.Tactic.BVDecide
open TlsMpc.FlatKernelLayout (lowerKernel layoutText)

/-! The `bundle-slot` kernels of `TlsMpc/BundleSlotKernels.lean` as flat gate lists.

    bundle_slot_emitter FLAT_PATH LAYOUT_PATH kernel bundle-slot FIRST LAST ONETIME
    bundle_slot_emitter splice D R S P K        (the runtime's splice, for the checks)

The first prints `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. An executable of its own (as
`ceremony_kernel_emitter` is) so that adding these kernels does not change `flat_kernel_emitter`,
whose hash keys the cache of every other circuit; `lowerKernel` and `layoutText` are the shared
ones of `TlsMpc/FlatKernelLayout.lean` (they were copies; same output, now with
`FlatKernelLayout.lowerKernel_loaded`). `circuit_cache.py` sends kernel names that start with
`bundle-slot` here. -/

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
