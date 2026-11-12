import TlsMpc.Signal.Unpad
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.ByContra

/-!
# `Unpad.decode` is PKCS#7 unpadding of the final 16-byte block

The receive kernels (`CbcOpen.openCore`, through `Signal.Unpad.decode`) remove the padding of the
last AES-CBC block. `TlsMpc/KernelSpecs/ReceiveAccept.lean` proves only that the status byte is 0 or
255 (`isMask_decode`) and lists "that the unpadding is PKCS#7" as not proved. Here, for the
concrete byte operations and a 16-byte block:

* `PaddedWith block p`: PKCS#7 padding of length `p`: `1 ≤ p ≤ 16` and the last `p` bytes all
  equal `p`. At most one `p` qualifies (`paddedWith_unique`: the last byte is `p`).
* `decode_padded`: if the block is padded with `p`, `decode` returns
  `[255, 16 − p] ++ (the first 16 − p bytes) ++ (p zero bytes)` (accept, retained length, retained
  bytes, zero fill).
* `decode_unpadded`: if no `p` qualifies, `decode` returns eighteen zero bytes (reject).
* `decode_accepts_iff`: the status byte is 255 exactly when the block carries valid PKCS#7
  padding, and 0 otherwise.

Only `TlsMpc.Signal.Unpad` (and `ByteAuth`, `ByteCircuit`, `Sha256`, `AigExport`, `BvConstruct`) is
compiled from the main package. The multi-byte counter value (`varintValue`) and `canonicalRange`
live in `TlsMpc.Signal.ReceiveFirst`, whose imports are 52 main-package modules (about 9,400 lines:
AES, TLS, Signal sessions); they are not compiled into this package and their value forms are not
stated here.
-/

namespace TlsMpcProofs.UnpadSpec
open TlsMpc TlsMpc.Signal

/-- PKCS#7 padding of length `p` on a 16-byte block: `1 ≤ p ≤ 16` and the last `p` bytes are `p`. -/
def PaddedWith (block : List (BitVec 8)) (p : ℕ) : Prop :=
  1 ≤ p ∧ p ≤ 16 ∧ block.drop (16 - p) = List.replicate p (BitVec.ofNat 8 p)

/-- What an accepted block decodes to: accept byte, retained length, retained bytes, zero fill. -/
def accepted (block : List (BitVec 8)) (p : ℕ) : List (BitVec 8) :=
  [255, BitVec.ofNat 8 (16 - p)] ++ block.take (16 - p) ++ List.replicate p 0

theorem caseMask_value (block : List (BitVec 8)) (c : ℕ) :
    Unpad.caseMask ByteAuth.concrete block c =
      if block.drop (16 - c) = List.replicate c (BitVec.ofNat 8 c) then 255 else 0 := by
  rw [Unpad.caseMask, ByteAuth.equalMask_value]
  rfl

theorem retained_eq (block : List (BitVec 8)) (p : ℕ) :
    Unpad.retained ByteAuth.concrete block p = accepted block p :=
  rfl

/-- **At most one padding length:** the last byte of the block is `p`. -/
theorem paddedWith_unique {block : List (BitVec 8)} (hlen : block.length = 16) {p q : ℕ}
    (hp : PaddedWith block p) (hq : PaddedWith block q) : p = q := by
  obtain ⟨hp1, hp16, hpd⟩ := hp
  obtain ⟨hq1, hq16, hqd⟩ := hq
  have last : ∀ c, 1 ≤ c → c ≤ 16 → block.drop (16 - c) = List.replicate c (BitVec.ofNat 8 c) →
      block.getLast? = some (BitVec.ofNat 8 c) := by
    intro c h1 h16 hd
    have h := congrArg List.getLast? hd
    rw [List.getLast?_drop, List.getLast?_replicate] at h
    simp only [hlen] at h
    rw [if_neg (by omega), if_neg (by omega)] at h
    exact h
  have h := (last p hp1 hp16 hpd).symm.trans (last q hq1 hq16 hqd)
  have hv := congrArg BitVec.toNat (Option.some.inj h)
  simp only [BitVec.toNat_ofNat] at hv
  omega

theorem decodeCases_length (block : List (BitVec 8)) (hlen : block.length = 16) (cs : List ℕ)
    (hcs : ∀ c ∈ cs, c ≤ 16) : (Unpad.decodeCases ByteAuth.concrete block cs).length = 18 :=
  Unpad.decodeCases_length _ block hlen cs hcs

theorem decodeCases_padded {block : List (BitVec 8)} (hlen : block.length = 16) {p : ℕ}
    (hp : PaddedWith block p) :
    ∀ cs : List ℕ, (∀ c ∈ cs, 1 ≤ c ∧ c ≤ 16) → p ∈ cs →
      Unpad.decodeCases ByteAuth.concrete block cs = accepted block p := by
  intro cs
  induction cs with
  | nil => intro _ h; exact absurd h List.not_mem_nil
  | cons c rest ih =>
    intro hcs hmem
    have hc := hcs c (List.mem_cons_self ..)
    have hrest : ∀ d ∈ rest, 1 ≤ d ∧ d ≤ 16 := fun d hd => hcs d (List.mem_cons_of_mem _ hd)
    have hlenR : (Unpad.retained ByteAuth.concrete block c).length =
        (Unpad.decodeCases ByteAuth.concrete block rest).length := by
      rw [Unpad.retained_length _ block hlen c hc.2,
        decodeCases_length block hlen rest (fun d hd => (hrest d hd).2)]
    rw [Unpad.decodeCases, caseMask_value]
    by_cases h : block.drop (16 - c) = List.replicate c (BitVec.ofNat 8 c)
    · have hcp : c = p := paddedWith_unique hlen ⟨hc.1, hc.2, h⟩ hp
      rw [if_pos h, Unpad.choose_accept _ _ hlenR, retained_eq, hcp]
    · rw [if_neg h, Unpad.choose_reject _ _ hlenR]
      apply ih hrest
      rcases List.mem_cons.mp hmem with hpc | hpr
      · subst hpc; exact absurd hp.2.2 h
      · exact hpr

theorem decodeCases_unpadded {block : List (BitVec 8)} (hlen : block.length = 16) :
    ∀ cs : List ℕ, (∀ c ∈ cs, c ≤ 16) →
      (∀ c ∈ cs, block.drop (16 - c) ≠ List.replicate c (BitVec.ofNat 8 c)) →
      Unpad.decodeCases ByteAuth.concrete block cs = List.replicate 18 0 := by
  intro cs
  induction cs with
  | nil => intro _ _; rfl
  | cons c rest ih =>
    intro hcs hnot
    have hrest : ∀ d ∈ rest, d ≤ 16 := fun d hd => hcs d (List.mem_cons_of_mem _ hd)
    have hlenR : (Unpad.retained ByteAuth.concrete block c).length =
        (Unpad.decodeCases ByteAuth.concrete block rest).length := by
      rw [Unpad.retained_length _ block hlen c (hcs c (List.mem_cons_self ..)),
        decodeCases_length block hlen rest hrest]
    rw [Unpad.decodeCases, caseMask_value, if_neg (hnot c (List.mem_cons_self ..)),
      Unpad.choose_reject _ _ hlenR]
    exact ih hrest (fun d hd => hnot d (List.mem_cons_of_mem _ hd))

theorem mem_counts (c : ℕ) : c ∈ (List.range 16).map (· + 1) ↔ 1 ≤ c ∧ c ≤ 16 := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨c - 1, by omega, by omega⟩

/-- **A block with PKCS#7 padding of length `p` decodes to accept, `16 − p`, its first `16 − p`
bytes and `p` zero bytes.** **K-fn** (`Unpad.decode`, part of `CbcOpen.openCore`). -/
theorem decode_padded {block : List (BitVec 8)} (hlen : block.length = 16) {p : ℕ}
    (hp : PaddedWith block p) : Unpad.decode ByteAuth.concrete block = accepted block p :=
  decodeCases_padded hlen hp _ (fun c hc => (mem_counts c).mp hc) ((mem_counts p).mpr ⟨hp.1, hp.2.1⟩)

/-- **A block without valid PKCS#7 padding decodes to eighteen zero bytes (reject).** **K-fn**. -/
theorem decode_unpadded {block : List (BitVec 8)} (hlen : block.length = 16)
    (h : ∀ p, ¬ PaddedWith block p) : Unpad.decode ByteAuth.concrete block = List.replicate 18 0 :=
  decodeCases_unpadded hlen _ (fun c hc => ((mem_counts c).mp hc).2)
    (fun c hc hd => h c ⟨((mem_counts c).mp hc).1, ((mem_counts c).mp hc).2, hd⟩)

/-- **The status byte is 255 exactly when the block is PKCS#7-padded** (and 0 otherwise). **K-fn**. -/
theorem decode_accepts_iff {block : List (BitVec 8)} (hlen : block.length = 16) :
    (Unpad.decode ByteAuth.concrete block).head? = some 255 ↔ ∃ p, PaddedWith block p := by
  constructor
  · intro h
    by_contra hnone
    rw [decode_unpadded hlen (fun p hp => hnone ⟨p, hp⟩)] at h
    exact absurd (Option.some.inj h) (by decide)
  · rintro ⟨p, hp⟩
    rw [decode_padded hlen hp]
    rfl

end TlsMpcProofs.UnpadSpec
