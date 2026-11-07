import TlsMpc.Signal.Pqxdh

open TlsMpc TlsMpc.Signal.Pqxdh

def nibble (c : Char) : Nat :=
  if c ≥ '0' && c ≤ '9' then c.toNat - '0'.toNat
  else c.toNat - 'a'.toNat + 10

def fromHex (s : String) : List (BitVec 8) :=
  let chars := s.toList.toArray
  (List.range (chars.size / 2)).map fun i =>
    BitVec.ofNat 8 (16 * nibble chars[2*i]! + nibble chars[2*i+1]!)

def main (args : List String) : IO Unit := do
  match args with
  | [a,b,c,d,k] =>
      let dh1 := fromHex a
      let dh2 := fromHex b
      let dh3 := fromHex c
      let oneTime := fromHex d
      let kem := fromHex k
      match deriveChecked Sha256.concrete dh1 dh2 dh3 oneTime kem with
      | none => IO.println "none"
      | some output =>
          IO.println (output.map BitVec.toNat)
          IO.println ((initialState Sha256.concrete dh1 dh2 dh3 oneTime kem).map BitVec.toNat)
  | _ => throw (IO.userError "expected five hex agreement strings")
