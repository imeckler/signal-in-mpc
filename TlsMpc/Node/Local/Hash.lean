import TlsMpc.TlsWire

/-!
# SHA-256 on machine words, for the runner's `hash`

`TlsWire.hash` (the runner's `Env.hash`: every commitment, and the challenge expansion of the mask
pool's two permutations, about 130 blocks per pool generation) evaluates `Sha256.hash` on
`Sha256.concrete`, whose words are `BitVec 32`: every addition and rotation goes through `Nat`
arithmetic with powers of two built at run time. About 6 ms of the controller's time per message
(PERFORMANCE.md, "third round"). `Sha256.hash` is generic in its operations; `fast` instantiates it on
`UInt8` / `UInt32`, and `fast_hom` is a `Sha256.Hom` from `fast` onto `concrete` (`UInt*.toBitVec`
commutes with every primitive), so `Sha256.hash_map` gives **`hashFast_eq`: `hashFast = TlsWire.hash`**
on every input. The runner uses `hashFast` (`Runner.start`); every script takes the hash as a
parameter and every theorem is about any hash, so nothing a script computes, opens or sends changes.
Not in any emitter's import closure (a module under `TlsMpc.Node`).
-/

namespace TlsMpc.Node.Local.Hash

open TlsMpc.Sha256

/-- Rotate right on `UInt32` with `BitVec.rotateRight`'s convention (the amount modulo 32). -/
def rotr32 (x : UInt32) (n : Nat) : UInt32 :=
  if n % 32 = 0 then x else (x >>> (n % 32).toUInt32) ||| (x <<< (32 - n % 32).toUInt32)

/-- The SHA-256 primitives on machine words. -/
def fast : Ops UInt8 UInt32 where
  byteConst n := UInt8.ofNat n
  wordConst n := UInt32.ofNat n
  byteXor := (· ^^^ ·)
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~ ·)
  add := (· + ·)
  rotr := rotr32
  shr x n := if n < 32 then x >>> n.toUInt32 else 0
  pack a b c d := a.toUInt32 * 16777216 + b.toUInt32 * 65536 + c.toUInt32 * 256 + d.toUInt32
  unpack w i := (w >>> (8 * (3 - i)).toUInt32).toUInt8

theorem toNat_small (k : Nat) (h : k < 32) : (k.toUInt32).toNat = k := by
  simp [Nat.toUInt32]; omega

theorem rotr32_spec (x : UInt32) (n : Nat) : (rotr32 x n).toBitVec = x.toBitVec.rotateRight n := by
  apply BitVec.eq_of_toNat_eq
  have hm : n % 32 < 32 := Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_rotateRight]
  unfold rotr32
  by_cases h : n % 32 = 0
  · rw [if_pos h, h]
    have hx := x.toNat_lt
    simp [Nat.shiftLeft_eq, Nat.mul_mod_left]
  · rw [if_neg h]
    have h1 := toNat_small (n % 32) hm
    have h2 := toNat_small (32 - n % 32) (by omega)
    simp only [UInt32.toNat_toBitVec, UInt32.toNat_or, UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft, h1, h2]
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (show 32 - n % 32 < 32 by omega)]

theorem shr_spec (x : UInt32) (n : Nat) :
    (if n < 32 then x >>> n.toUInt32 else 0).toBitVec = x.toBitVec >>> n := by
  apply BitVec.eq_of_toNat_eq
  split
  · next h =>
    simp only [UInt32.toNat_toBitVec, UInt32.toNat_shiftRight, BitVec.toNat_ushiftRight, toNat_small n h]
    rw [Nat.mod_eq_of_lt h]
  · next h =>
    have hx := x.toNat_lt
    simp only [UInt32.toNat_toBitVec, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have : x.toNat < 2 ^ n := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt this]
    rfl

theorem pack_spec (a b c d : UInt8) :
    (a.toUInt32 * 16777216 + b.toUInt32 * 65536 + c.toUInt32 * 256 + d.toUInt32).toBitVec =
      (a.toBitVec ++ b.toBitVec) ++ (c.toBitVec ++ d.toBitVec) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have orShift : ∀ (x y n : Nat), y < 2 ^ n → x <<< n ||| y = x * 2 ^ n + y := fun x y n hy => by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hy x, Nat.shiftLeft_eq]
  simp only [UInt32.toNat_toBitVec, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32,
    BitVec.toNat_append, UInt8.toNat_toBitVec, UInt32.reduceToNat]
  rw [orShift c.toNat d.toNat 8 hd, orShift a.toNat b.toNat 8 hb,
    orShift _ _ 16 (by simp only [Nat.reducePow]; omega)]
  simp only [Nat.reducePow]
  omega

theorem unpack_spec (w : UInt32) (i : Nat) :
    ((w >>> (8 * (3 - i)).toUInt32).toUInt8).toBitVec = w.toBitVec.extractLsb' (8 * (3 - i)) 8 := by
  apply BitVec.eq_of_toNat_eq
  have hk : 8 * (3 - i) < 32 := by omega
  simp only [UInt8.toNat_toBitVec, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, toNat_small _ hk,
    BitVec.extractLsb'_toNat, UInt32.toNat_toBitVec]
  rw [Nat.mod_eq_of_lt hk]

/-- **`fast` refines `concrete`**: `toBitVec` commutes with every primitive. -/
theorem fast_hom : Hom fast concrete UInt8.toBitVec UInt32.toBitVec where
  byteConst n := rfl
  wordConst n := rfl
  byteXor x y := by simp [fast, concrete]
  xor x y := by simp [fast, concrete]
  and x y := by simp [fast, concrete]
  not x := by simp [fast, concrete]
  add x y := by simp [fast, concrete]
  rotr x n := rotr32_spec x n
  shr x n := shr_spec x n
  pack x y z t := pack_spec x y z t
  unpack x n := unpack_spec x n
  sum4 x y z t := by simp [fast, concrete]
  sum5 x y z t u := by simp [fast, concrete]

/-- `TlsWire.hash` on machine words (`hashFast_eq`). -/
def hashFast (bytes : TlsWire.Bytes) : TlsWire.Bytes := Sha256.hash fast bytes

/-- **`hashFast` is `TlsWire.hash`.** -/
theorem hashFast_eq (bytes : TlsWire.Bytes) : hashFast bytes = TlsWire.hash bytes := by
  have h := Sha256.hash_map fast_hom bytes
  unfold TlsWire.hash hashFast
  have hin : bytes.map (fun b => BitVec.ofNat 8 b.toNat) = bytes.map UInt8.toBitVec := by
    apply List.map_congr_left; intro b _
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt b.toNat_lt]
  rw [hin, ← h, List.map_map]
  conv => lhs; rw [← List.map_id (Sha256.hash fast bytes)]
  apply List.map_congr_left
  intro b _
  simp

end TlsMpc.Node.Local.Hash
