import TlsMpc.Signal.Word64

/-! `Word64.concrete` for values in the clear, computed faster.

The controllers run the parsers on revealed bytes with `Word64.concrete`. Its
`select` replicates the mask byte into a 64-bit word and complements it, its
`unpack` and constants take `2 ^ n` as an arbitrary-precision power, and its
`ule` subtracts 65-bit values: every one of these allocates big numbers at run
time, and the response parser does several hundred of them per byte.

`fast` is the same record of operations (`fast_eq : fast = concrete`), with
those four computed directly. Anything proved about `concrete` holds for it by
rewriting with `fast_eq`. -/
namespace TlsMpc.Signal.Word64

def fastConst (n : Nat) : BitVec 64 :=
  BitVec.ofFin ⟨n % 18446744073709551616, Nat.mod_lt n (by decide)⟩

theorem fastConst_eq (n : Nat) : fastConst n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [fastConst]

def fastUnpack (x : BitVec 64) (i : Nat) : BitVec 8 :=
  BitVec.ofFin ⟨(x.toNat >>> (8 * (7 - i))) % 256, Nat.mod_lt _ (by decide)⟩

theorem fastUnpack_eq (x : BitVec 64) (i : Nat) : fastUnpack x i = x.extractLsb' (8 * (7 - i)) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [fastUnpack, BitVec.extractLsb'_toNat]

def fastUle (x y : BitVec 64) : BitVec 8 := if x.toNat ≤ y.toNat then 255 else 0

theorem fastUle_eq (x y : BitVec 64) : fastUle x y = concrete.ule x y := (ule_value x y).symm

def fastSelect (mask : BitVec 8) (x y : BitVec 64) : BitVec 64 :=
  if mask = 255 then x else if mask = 0 then y else concrete.select mask x y

theorem fastSelect_eq (mask : BitVec 8) (x y : BitVec 64) : fastSelect mask x y = concrete.select mask x y := by
  unfold fastSelect
  split
  · next h => rw [h, select_accept]
  · split
    · next h => rw [h, select_reject]
    · rfl

/-- Eight bytes, most significant first, as one word: by multiplication instead of seven appends. -/
def fastPack (bytes : List (BitVec 8)) : BitVec 64 :=
  match bytes with
  | [a, b, c, d, e, f, g, h] =>
      BitVec.ofFin ⟨(((((((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat) * 256 + e.toNat) * 256
        + f.toNat) * 256 + g.toNat) * 256 + h.toNat) % 18446744073709551616, Nat.mod_lt _ (by decide)⟩
  | _ => concrete.pack bytes

private theorem append_toNat (x : BitVec n) (y : BitVec m) : (x ++ y).toNat = x.toNat * 2 ^ m + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem fastPack_eq (bytes : List (BitVec 8)) : fastPack bytes = concrete.pack bytes := by
  unfold fastPack
  split
  · next a b c d e f g h =>
      have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
      have he := e.isLt; have hf := f.isLt; have hg := g.isLt; have hh := h.isLt
      apply BitVec.eq_of_toNat_eq
      simp only [concrete, Varint64.pack, Varint64.concrete, OpenResult.get, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, append_toNat, BitVec.toNat_ofFin]
      omega
  · rfl

def fast : Ops (BitVec 8) (BitVec 64) :=
  { concrete with const := fastConst, pack := fastPack, unpack := fastUnpack, ule := fastUle, select := fastSelect }

theorem fast_eq : fast = concrete := by
  have hc : fastConst = BitVec.ofNat 64 := funext fastConst_eq
  have hp : fastPack = concrete.pack := funext fastPack_eq
  have hu : fastUnpack = (fun (x : BitVec 64) (i : Nat) => x.extractLsb' (8 * (7 - i)) 8) :=
    funext fun x => funext fun i => fastUnpack_eq x i
  have hl : fastUle = concrete.ule := funext fun x => funext fun y => fastUle_eq x y
  have hs : fastSelect = concrete.select := funext fun m => funext fun x => funext fun y => fastSelect_eq m x y
  unfold fast
  rw [hc, hp, hu, hl, hs]
  rfl

end TlsMpc.Signal.Word64
