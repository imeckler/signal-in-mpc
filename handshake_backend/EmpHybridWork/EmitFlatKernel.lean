import TlsMpc.FlatLowering
import TlsMpc.FlatKernelLayout
import TlsMpc.HybridKernels
import TlsMpc.EstablishKernels
import TlsMpc.ReceiveKernels
import TlsMpc.BundleKernels
import TlsMpc.MlKemFastKernels
import TlsMpc.RecordClassKernels
import TlsMpc.BundleItemKernels
import TlsMpc.TypedOpenKernels
open TlsMpc Std.Tactic.BVDecide
open TlsMpc.FlatKernelLayout (lowerKernel layoutText)

/-! Worker kernels straight to the flat gate list, without the Python lowering.

    flat_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]

writes the `EMP_HYBRID_BOOL_V1` gate list and the `EMP_HYBRID_KERNEL_LAYOUT_V1` field
layout, and prints one line: `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. Kernels, bit order and
field layout are those of `hybrid_kdf_emitter kernel ...` followed by `hybrid_lowering.py`:
variable `v`, bit `b` (weight `2^b`) is wire `offset(v) + b`; a field's bit `b` of byte `j`
is its output `8 * j + b`.

The gate list is `FlatLowering.lowerExpr` of the kernel's joined output bytes, the text is what
`Flat.print` writes and the layout is `FlatKernelLayout.layoutText` (shared with the other kernel
emitters; `TlsMpc/FlatKernelLayout.lean`): `FlatKernelLayout.lowerKernel_loaded` proves that the
written circuit parses back to the gate list, that the layout parses back to the kernel's fields
and open marks, and (with `FlatLowering.lowerExpr_loaded`) what every output wire computes.
Outside the theorems: `selection` (which bit of the joined value each named output bit is). -/

def main (args : List String) : IO Unit := do
  if let ["layout", maskPath] := args then
    -- CHECK ONLY: `Signal.BundleResponse.layout?` on opened punctuation flags (a file of `0`/`1`
    -- characters), printed as the `bundle-device` parameter lists, or `none`.
    let mask := (← IO.FS.readFile maskPath).trimAscii.toString.toList.map (· == '1')
    match Signal.BundleResponse.layout? mask with
    | some ws => for row in BundleKernel.arguments mask.length ws do IO.println (" ".intercalate row)
    | none => IO.println "none"
    return
  let flatPath :: layoutPath :: "kernel" :: rest := args
    | throw (IO.userError "flat_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]")
  let some kernel := HybridKernel.find rest <|> EstablishKernel.find rest <|> ReceiveKernel.find rest
      <|> BundleKernel.find rest <|> MlKemFastKernel.find rest <|> RecordClassKernel.find rest
      <|> BundleItemKernel.find rest <|> TypedOpenKernel.find rest
    | throw (IO.userError "unknown kernel or shape")
  match lowerKernel kernel with
  | .error message => throw (IO.userError message)
  | .ok flat =>
      let handle ← IO.FS.Handle.mk flatPath .write
      flat.print handle.putStr
      handle.flush
      IO.FS.writeFile layoutPath (layoutText kernel)
      IO.println s!"{flat.inputs} {flat.outputs.size} {flat.andCount} {flat.opa.size}"
