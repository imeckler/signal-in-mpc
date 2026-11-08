import TlsMpc.Signal.ProtoParse
open TlsMpc TlsMpc.Signal

def hexDigit (n : Nat) : String := String.singleton (Char.ofNat (if n < 10 then 48+n else 87+n))
def hexByte (x : BitVec 8) : String := hexDigit (x.toNat / 16) ++ hexDigit (x.toNat % 16)
def fromHex (s : String) : List (BitVec 8) :=
  let chars := s.toList
  (List.range (chars.length / 2)).map fun i =>
    let digit := fun c => if c ≥ '0' && c ≤ '9' then c.toNat-48 else c.toNat-87
    BitVec.ofNat 8 (16 * digit (chars[2*i]!) + digit (chars[2*i+1]!))
def viewField (body : List (BitVec 8)) (state : ProtoParse.State (BitVec 8) (BitVec 64)) (i : Nat) : String :=
  let f := ProtoParse.getField Word64.concrete ByteAuth.concrete state i
  if f.present ≠ 255 then "-" else
    if i = 1 ∨ i = 2 then toString (f.scalar.toNat % 2^32)
    else String.join ((body.drop f.offset.toNat).take f.length.toNat |>.map hexByte)
def viewBody (body : List (BitVec 8)) : String :=
  let state := ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete body
  let status := if ProtoParse.completeMask Word64.concrete ByteAuth.concrete body.length state = 255 then "ok" else "err"
  String.intercalate "|" ([status,toString state.next.toNat] ++ (List.range 6).map (viewField body state))
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    output.putStrLn (viewBody (fromHex line.trimAscii.toString))
