import TlsMpc.FlatLowering
import TlsMpc.FlatKernelLayout
import TlsMpc.MlKemFastKernels
open TlsMpc Std.Tactic.BVDecide
open TlsMpc.FlatKernelLayout (lowerKernel layoutText)

/-! The KEM kernels of `TlsMpc/MlKemFastKernels.lean` as flat gate lists, until
`MlKemFastKernel.find` is registered in `EmitFlatKernel.lean`; `lowerKernel` and
`layoutText` are the shared ones of `TlsMpc/FlatKernelLayout.lean` (they were copies;
same output, now with `FlatKernelLayout.lowerKernel_loaded`).

    kem_kernel_emitter FLAT_PATH LAYOUT_PATH kernel NAME [PARAMETERS]

prints `INPUT_BITS OUTPUT_BITS AND_GATES GATES`. Two more commands run Lean
VALUES, no circuit, for `check_kem_kernels.py`:

    kem_kernel_emitter reference VARIANT KEY_HEX ENTROPY_HEX
    kem_kernel_emitter stages VARIANT KEY_HEX ENTROPY_A_HEX ENTROPY_B_HEX

`reference` is the existing specification `Signal.MlKem.encapsulate` on 32-bit
words (rank 4, η = 2, 11 and 5 bits, 224 candidate pairs); `stages` is the
composition of the value instances of the stage functions. Both print
`STATUS_HEX CIPHERTEXT_HEX SECRET_HEX`. -/

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
