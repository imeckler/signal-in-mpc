import TlsMpc.Node.Local.Edwards

/-!
Test vectors of the local curve arithmetic (`TlsMpc/Node/Local/Edwards.lean`, stage S11), computed
by the Lean definitions themselves, for `node_worker/tests/s11_curve.rs`, which recomputes every
line with curve25519-dalek (the vendored crate; no libsodium binding is available offline). Not part
of the library; nothing imports it.

    lake env lean --run node_worker/tests/lean/S11Curve.lean   # stdout → node_worker/tests/s11_curve_vectors.txt

The run also prints `time …` lines (interpreted timings of the local work per message, plan risk
R2); they are not part of the vector file.

Format (hex is lowercase; points are 32-byte compressed Edwards encodings, field elements 32-byte
little-endian):
  basemul K_HEX P_HEX          k·B (k < 2^256 little-endian)
  add P Q R                    R = P + Q
  sub P Q R                    R = P − Q
  mul K_HEX P R                R = k·P (P in the prime-order subgroup)
  mont P U                     U = (1 + y)/(1 − y)
  valid P 0|1                  libsodium's is_valid_point (on curve, not small order, ℓ·P = 0)
  decode BYTES 0|1             whether the bytes decode to a point (canonical y, on the curve)
  liftu U P|none               the point with Montgomery u and even x
-/

open TlsMpc.Node.Local.Edwards
open TlsMpc.Node.Local.Field
open TlsMpc.FieldDag (ofNat F)

namespace S11Curve

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b => String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)])
def le32 (n : Nat) : List UInt8 := TlsMpc.Node.Engine.le 32 n

def scalars : List Nat :=
  [1, 2, 3, 8, 255, 65537, 2 ^ 128 + 7, 2 ^ 251 + 12345, 2 ^ 252 - 1, ell - 1, ell, ell + 1,
   2 ^ 254 + 2 ^ 200 + 8 * 4421, 2 ^ 255 - 20]

def pts : List Value := (List.range 8).map fun i => mul ((i + 2) * 1000003 ^ 7 % ell) base

def lines : List String :=
  let bm := scalars.map fun k => s!"basemul {hex (le32 k)} {hex (encode (mul k base))}"
  let ad := (pts.zip (pts.drop 1)).map fun e => s!"add {hex (encode e.1)} {hex (encode e.2)} {hex (encode (add e.1 e.2))}"
  let sb := (pts.zip (pts.drop 2)).map fun e => s!"sub {hex (encode e.1)} {hex (encode e.2)} {hex (encode (sub e.1 e.2))}"
  let mu := (pts.zip scalars).map fun e => s!"mul {hex (le32 e.2)} {hex (encode e.1)} {hex (encode (mul e.2 e.1))}"
  let mo := (base :: pts).map fun p => s!"mont {hex (encode p)} {hex (toBytes (montU p))}"
  let cand : List Value := [base, torsion8, add base torsion8, neutral, mul 4 torsion8] ++ pts.take 3
  let va := cand.map fun p => s!"valid {hex (encode p)} {if isValid p then 1 else 0}"
  let nonCanon : List UInt8 := le32 (2 ^ 255 - 19 + 1)
  let offCurve : List UInt8 := le32 2
  let decs : List (List UInt8) := [encode base, nonCanon, offCurve, le32 3, le32 4, encode (mul 77 base), torsionBytes]
  let de := decs.map fun b => s!"decode {hex b} {if (decode b).isSome then 1 else 0}"
  let us : List F := [ofNat 9, ofNat 2, ofNat 3, ofNat 4, montU (mul 5 base), montU (mul 1234567 base), 0 - ofNat 1]
  let li := us.map fun u => s!"liftu {hex (toBytes u)} {match liftU u with | some p => hex (encode p) | none => "none"}"
  bm ++ ad ++ sb ++ mu ++ mo ++ va ++ de ++ li

/-- Interpreted timings (plan R2). Inputs depend on the clock so nothing is hoisted; each result is
printed before the clock is read again. -/
def timings (reps : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let z := t0 % 1
  let mut acc : Nat := 0
  let a0 ← IO.monoNanosNow
  for i in [0:reps] do
    acc := acc + (mul (2 ^ 251 + 12345 + i + z) base).1.val % 7
  let a1 ← IO.monoNanosNow
  IO.println s!"time scalar-mult {(a1 - a0) / reps / 1000} us (check {acc})"
  let m := randomPoint (777 + z) 3
  let zP := mul (99 + z) base
  let b0 ← IO.monoNanosNow
  for _ in [0:reps] do
    acc := acc + ((hints .a zP m).map List.length).getD 1
  let b1 ← IO.monoNanosNow
  IO.println s!"time hints-per-point {(b1 - b0) / reps / 1000} us (check {acc})"
  let c0 ← IO.monoNanosNow
  for i in [0:reps] do
    acc := acc + ((root (ofNat (1234567 + i + z))).map (fun r => r.2.val % 3)).getD 5
  let c1 ← IO.monoNanosNow
  IO.println s!"time lift-root {(c1 - c0) / reps / 1000} us (check {acc})"
  let d0 ← IO.monoNanosNow
  for i in [0:reps] do
    acc := acc + (if isValid (mul (5 + i + z) base) then 1 else 0)
  let d1 ← IO.monoNanosNow
  IO.println s!"time validity {(d1 - d0) / reps / 1000} us (check {acc})"
  let e0 ← IO.monoNanosNow
  for i in [0:reps] do
    acc := acc + (randomPoint (2 ^ 250 + i + z) (i + z)).2.val % 5
  let e1 ← IO.monoNanosNow
  IO.println s!"time mask-point {(e1 - e0) / reps / 1000} us (check {acc})"
  let f0 ← IO.monoNanosNow
  for _ in [0:reps] do
    acc := acc + (torsionHint .a zP m).1.val % 5
  let f1 ← IO.monoNanosNow
  IO.println s!"time torsion-hint {(f1 - f0) / reps / 1000} us (check {acc})"
  let g0 ← IO.monoNanosNow
  for _ in [0:reps] do
    acc := acc + ((publicTable zP).map List.length).getD 1
  let g1 ← IO.monoNanosNow
  IO.println s!"time public-table {(g1 - g0) / reps / 1000} us (check {acc})"
  let h0 ← IO.monoNanosNow
  for i in [0:reps] do
    acc := acc + ((recoverPublic (ofNat (9 + i + z))).headD 0).val % 3
  let h1 ← IO.monoNanosNow
  IO.println s!"time recover {(h1 - h0) / reps / 1000} us (check {acc})"

end S11Curve

def main : IO Unit := do
  let t ← IO.asTask (do
    for l in S11Curve.lines do IO.println l
    S11Curve.timings 3) (prio := .dedicated)
  match t.get with
  | .ok _ => pure ()
  | .error e => IO.println s!"error {e}"
