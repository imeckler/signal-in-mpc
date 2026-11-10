import PreKeyReferenceWork.Proofs
open Aeneas Aeneas.Std PreKeyReference PreKeyReference.Proofs

def key : libsignal_core.curve.PublicKey :=
  ⟨.DjbPublicKey ⟨List.replicate 32 0#u8, by simp⟩⟩
def pqKey : kem.Key kem.Public :=
  ⟨.Kyber1024, ⟨⟨List.replicate 1568 0#u8, by simp only [List.length_replicate]; scalar_tac⟩, ()⟩⟩
def u32 (n : Nat) : Std.U32 := ⟨BitVec.ofNat 32 n⟩
def emptySig : alloc.vec.Vec Std.U8 := ⟨[], by simp⟩
def optionalId (n : Nat) : Nat := [0,1,2147483648,4294967295][n % 4]!
def signedId (n : Nat) : Nat := [4294967295,2147483648,1,0][n % 4]!
def selected {A : Type} (n i : Nat) (a : A) : Option A :=
  if n.testBit i then some a else none

def fixture (n : Nat) : state.bundle.PreKeyBundleContent :=
  ⟨selected n 0 (u32 (n*1048577)), selected n 1 (⟨127#u8, by decide⟩),
   selected n 2 (u32 (optionalId n)), selected n 3 key,
   selected n 4 (u32 (signedId n)), selected n 5 key, selected n 6 emptySig,
   selected n 7 ⟨key⟩, selected n 8 (u32 (n*65537)), selected n 9 pqKey,
   selected n 10 emptySig⟩

def row (n : Nat) : List Nat :=
  match actual (fixture n) with
  | .ok (.Ok b) => [0,if b.pre_key_id.isSome then 1 else 0,
      b.registration_id.val,b.device_id.val.val,
      b.pre_key_id.map (·.val) |>.getD 0,b.ec_signed_pre_key.id.val,b.kyber_pre_key.id.val]
  | .ok (.Err e) => [errorCode (.Err e) |>.toNat,0,0,0,0,0,0]
  | _ => [254]

def main : IO Unit := do
  let out ← IO.getStdout
  for n in [:2048] do
    out.putStrLn ((Lean.toJson (row n)).compress)
