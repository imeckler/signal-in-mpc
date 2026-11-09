import Lean
import TlsMpc.Signal.PrivateReusableOutboxV1
open TlsMpc TlsMpc.Signal PrivateReusableOutboxV1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def byte (n : Nat) : BitVec 8 := BitVec.ofNat 8 n
private def gen (n : Nat) : List (BitVec 8) := (List.range 8).map fun i => byte (n / 256^(7-i))
private def cell (n : Nat) : List (BitVec 8) :=
 [255,255,0,1] ++ [byte n] ++ List.replicate 1289 0 ++ gen n ++ gen n
private def run (ordinal : Nat) (q ds new : List (BitVec 8)) (generation : Nat) (valid : BitVec 8 := 255) :=
 replace ByteAuth.concrete ordinal ([valid]++q++ds++new++gen generation)
private def expect (ok : Bool) : IO Unit := if !ok then throw (IO.userError "reusable-outbox fixture mismatch") else pure ()
def main : IO Unit := do
 let mut count := 0
 let mut q := List.replicate queueBytes (byte 0)
 let mut ds := List.replicate 4 (byte 0)
 for generation in List.range 12 do
  let ordinal := generation % 4
  let n := generation+1
  let old := q
  let output := run ordinal q ds (cell n) n
  expect (output.length==5245 && output.head! ==255)
  q := (output.drop 1).take queueBytes
  ds := (output.drop (1+queueBytes)).take 4
  for other in List.range 4 do
   if other != ordinal then
    expect (PrivateAccountAdmissionV2.slice q (other*cellBytes) cellBytes == PrivateAccountAdmissionV2.slice old (other*cellBytes) cellBytes)
  ds := ds.set ordinal 3
  count := count+1
 for ordinal in List.range 4 do
  for disposition in [1,2,4,5] do
   let rejected := run ordinal q (ds.set ordinal (byte disposition)) (cell 99) 99
   expect (rejected.head! ==0 && rejected.all (·==0))
   count := count+1
  expect ((run ordinal q ds (cell 99) 98).head! ==0)
  expect ((run ordinal q ds (cell 99) 99 0).head! ==0)
  let oldGeneration := 9+ordinal
  expect ((run ordinal q ds (cell oldGeneration) oldGeneration).head! ==0)
  count := count+3
 expect ((run 4 q ds (cell 99) 99).head! ==0)
 expect ((run 0 q ds ((cell 99).set 1293 1) 99).head! ==0)
 count := count+2
 (← IO.getStdout).putStrLn s!"reusable outbox passed {count} cases"
#print axioms eligible_value
#print axioms eligible_preserves_pending
#print axioms candidate_preserves_rest
#print axioms replace_map
#print axioms compiled_replace_correct
