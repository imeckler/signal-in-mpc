import TlsMpc.Signal.PrivateTextNotification
open TlsMpc.Signal

/-! CHECK ONLY (used by check_send_size_classes.py; not a build target, no circuit):

    lake env lean --run handshake_backend/EmpHybridWork/BuildPublicText.lean TEXTHEX:TIMESTAMP ...

prints, per argument, what the controllers' notify path computes for that public text and
timestamp with `PrivateTextNotification.buildPublic 4`: `CLASS BUILTHEX`, or `none`. -/

def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def fromHex (text : String) : List (BitVec 8) :=
  let rec go : List Char → List (BitVec 8)
    | high :: low :: rest => BitVec.ofNat 8 (16 * hexValue high + hexValue low) :: go rest
    | _ => []
  go text.toList

def toHex (bytes : List (BitVec 8)) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
  String.ofList (bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

def main (args : List String) : IO Unit := do
  for arg in args do
    match arg.splitOn ":" with
    | [text, timestamp] =>
      let stamp := timestamp.toNat!
      let time := (List.range 8).map fun i => BitVec.ofNat 8 (stamp / 2 ^ (8 * (7 - i)))
      match PrivateTextNotification.buildPublic 4 (fromHex text) time with
      | some (classes, built) => IO.println s!"{classes} {toHex built}"
      | none => IO.println "none"
    | _ => throw (IO.userError "TEXTHEX:TIMESTAMP")
