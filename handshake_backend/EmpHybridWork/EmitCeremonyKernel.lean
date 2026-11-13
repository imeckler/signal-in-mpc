import TlsMpc.FlatLowering
import TlsMpc.FlatKernelLayout
import TlsMpc.CeremonyKernels
open TlsMpc Std.Tactic.BVDecide
open TlsMpc.FlatKernelLayout (lowerKernel layoutText)

/-! The ceremony kernels of `TlsMpc/CeremonyKernels.lean` as flat gate lists.

    ceremony_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]

prints `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. An executable of its own (as
`EmitKemKernel.lean` was) so that adding these kernels does not change `flat_kernel_emitter`,
whose hash keys the cache of every other circuit; `lowerKernel` and `layoutText` are the shared
ones of `TlsMpc/FlatKernelLayout.lean` (they were copies; same output, now with
`FlatKernelLayout.lowerKernel_loaded`). `circuit_cache.py` sends kernel names that start with
`ceremony-` here. -/

def main (args : List String) : IO Unit := do
  let flatPath :: layoutPath :: "kernel" :: rest := args
    | throw (IO.userError "ceremony_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]")
  let some kernel := CeremonyKernel.find rest | throw (IO.userError "unknown kernel or shape")
  match lowerKernel kernel with
  | .error message => throw (IO.userError message)
  | .ok flat =>
      let handle ← IO.FS.Handle.mk flatPath .write
      flat.print handle.putStr
      handle.flush
      IO.FS.writeFile layoutPath (layoutText kernel)
      IO.println s!"{flat.inputs} {flat.outputs.size} {flat.andCount} {flat.opa.size}"
