import AesKeyScheduleWork.PublicInputs
import AesKeyScheduleWork.Generated.Funs
import TlsMpc.Signal.AesMixPhases
import TlsMpc.Signal.AesKeySchedule

/-! Public differential fixtures only. These do not establish the schedule
equivalence; they check the proposed representation used in its proof. -/

namespace AesKeySchedulePublicCheck

open Aeneas Aeneas.Std TlsMpc


def expected (key : Aeneas.Std.Array U8 32#usize) : List (BitVec 64) :=
  let expanded := Aes.expandKey Aes.concrete 8 14 (key.val.map UScalar.bv)
  (List.range 15).flatMap fun round =>
    let input := fun (_ : Nat) index =>
      expanded[16 * round + Signal.AesRemainingLinear.shiftIndex
        (if round = 14 then 0 else 4 - round % 4) index]?.getD 0
    let words := Signal.AesLayout.network input
    (List.range 8).map fun plane =>
      let word := words.at plane
      if round > 0 ∧ (plane = 0 ∨ plane = 1 ∨ plane = 5 ∨ plane = 6) then ~~~word else word

def check (seed : Nat) : Bool :=
  match RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule (key seed) with
  | .ok result =>
    let bytes := (key seed).val.map UScalar.bv
    let first := Signal.AesLayout.network (fun _ index => bytes[index]?.getD 0)
    let second := Signal.AesLayout.network (fun _ index => bytes[16 + index]?.getD 0)
    result.val.map UScalar.bv == expected (key seed) &&
      result.val.map UScalar.bv == Signal.AesKeySchedule.scheduleCore
        Signal.AesKeySchedule.concrete first.list second.list
  | _ => false

end AesKeySchedulePublicCheck

def main : IO Unit := do
  for seed in List.range 16 do
    unless AesKeySchedulePublicCheck.check seed do
      match RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule (AesKeySchedulePublicCheck.key seed) with
      | .ok result =>
        let pairs := (result.val.map Aeneas.Std.UScalar.bv).zip (AesKeySchedulePublicCheck.expected (AesKeySchedulePublicCheck.key seed))
        for (actual, expected) in pairs do
          unless actual == expected do IO.println s!"word mismatch: {actual.toNat} / {expected.toNat}"
      | .fail error => IO.println s!"actual operation failed: {repr error}"
      | .div => IO.println "actual operation returned div"
      throw (IO.userError s!"actual AES key schedule disagrees at public fixture {seed}")
  IO.println "16 public AES256 schedule representation fixtures passed; the separate complete equivalence proof is audited by check_schedule.py."
