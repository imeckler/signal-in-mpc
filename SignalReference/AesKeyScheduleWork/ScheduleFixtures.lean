import Lean
import AesKeyScheduleWork.PublicInputs
import TlsMpc.Signal.AesKeyCopy

/-! Public fixture outputs evaluated from the actual translated entrypoint. -/

structure ScheduleFixture where
  input : List Nat
  output : List Nat
  deriving Lean.ToJson

def main : IO Unit := do
  let mut fixtures : List ScheduleFixture := []
  for seed in List.range 16 do
    let key := AesKeySchedulePublicCheck.key seed
    match RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule key with
    | .ok result =>
      let inputBytes := key.val.map (fun x => x.bv.toNat)
      let outputBytes := (TlsMpc.Signal.AesKeyCopy.encode (result.val.map Aeneas.Std.UScalar.bv)).map BitVec.toNat
      fixtures := fixtures ++ [⟨inputBytes, outputBytes⟩]
    | .fail _ | .div => throw (IO.userError "actual key schedule fixture failed")
  (← IO.getStdout).putStrLn (Lean.toJson fixtures).compress
