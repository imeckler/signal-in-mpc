import TlsMpc.SealCtrProofs
import TlsMpc.GhashField

/-!
The kernels that produce XOR shares of the GHASH key powers (`gcmKeyShare`,
`gcmMultiply`, TlsMpc/HybridKernels.lean), and the schedule that turns their
outputs into shares of `H, H², …, Hⁿ`.

* `gcmKeyShare_spec`, `gcmMultiply_spec`: the kernels' outputs on values, for
  every assignment, as the repository's concrete AES and GHASH multiplication.
* `gcmKeyShare_reshare`, `gcmMultiply_reshare`: the same on field elements: the
  pair (mask, opened value) is a sharing of `H`, respectively of the product of
  the two shared inputs (`Schedule.reshare`).
* `Schedule.ensure`: a pure model of the order of operations of
  `GcmShares::ensure` in handshake_backend/EmpHybridWork/gcm_shares.h: the
  first share from one key-share step, power `2m` by each party squaring its
  own share of power `m`, odd power `k` by a re-shared product of the shared
  power `k − 1` and the shared `H`.
* `Schedule.ensure_descending`: for any multiplication satisfying the field
  laws and any masks, the first `count` shares of that schedule, reversed, XOR
  to `GhashShares.descending` (hypothesis (2) of `shared_halves_are_ghash`).
* `shared_halves_are_ghash_proved`: `shared_halves_are_ghash` with the field
  laws discharged (`GhashField.laws`).
* `scheduled_halves_are_ghash`: both hypotheses discharged: the two local tags
  computed from the scheduled shares XOR to GCM's GHASH value.

Outside these theorems: that the C++ in gcm_shares.h follows `Schedule.ensure`
(its `gf_multiply` being `Ghash.multiply Ghash.concrete` on packed blocks, its
inputs to the kernels being the shares the model names, and its `half` being
`GhashShares.localTag` over `Gcm.authInput`), and everything about what a
deviating party can do (see TlsMpc/GhashShares.lean for that).
-/
namespace TlsMpc.HybridKernel
open Std.Tactic.BVDecide
open Signal

/-! ### The kernels on values -/

/-- `masked` is `AES_K(0¹⁶) ⊕ mask`, `K` the key bytes of the traffic block. -/
theorem gcmKeyShare_spec (assign : BVExpr.Assignment) :
    gcmKeyShare.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [Aes.addRoundKey Gcm.concrete.aes
        (Aes.encryptExpanded Gcm.concrete.aes 10 (expandedOf (inputValue assign 0 60)) (Gcm.zeros Gcm.concrete 16))
        (inputValue assign 60 16)] := by
  have hT : lookup [("traffic", Shape.bytes 60), ("mask", .bytes 16)] "traffic" =
      ByteCircuit.inputBytes 0 60 := by simp [lookup, lookupFrom]
  have hM : lookup [("traffic", Shape.bytes 60), ("mask", .bytes 16)] "mask" =
      ByteCircuit.inputBytes 60 16 := by simp [lookup, lookupFrom, Shape.variables]
  simp only [gcmKeyShare, toParty, List.map_cons, List.map_nil, hT, hM, xorBytes_eval,
    Aes.encryptExpanded_map (Gcm.evaluationHom assign).aes, gcmExpanded_eval,
    Gcm.zeros_map (Gcm.evaluationHom assign)]

/-- `masked` is `unpack(pack(leftA ⊕ leftB) · pack(rightA ⊕ rightB)) ⊕ mask`. -/
theorem gcmMultiply_spec (assign : BVExpr.Assignment) :
    gcmMultiply.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [Aes.addRoundKey Gcm.concrete.aes
        (Gcm.concrete.unpack (Ghash.multiply Gcm.concrete.field
          (Gcm.concrete.pack (Aes.addRoundKey Gcm.concrete.aes (inputValue assign 0 16) (inputValue assign 16 16)))
          (Gcm.concrete.pack (Aes.addRoundKey Gcm.concrete.aes (inputValue assign 32 16) (inputValue assign 48 16)))))
        (inputValue assign 64 16)] := by
  have hLA : lookup [("leftA", Shape.bytes 16), ("leftB", .bytes 16), ("rightA", .bytes 16), ("rightB", .bytes 16),
      ("mask", .bytes 16)] "leftA" = ByteCircuit.inputBytes 0 16 := by simp [lookup, lookupFrom]
  have hLB : lookup [("leftA", Shape.bytes 16), ("leftB", .bytes 16), ("rightA", .bytes 16), ("rightB", .bytes 16),
      ("mask", .bytes 16)] "leftB" = ByteCircuit.inputBytes 16 16 := by simp [lookup, lookupFrom, Shape.variables]
  have hRA : lookup [("leftA", Shape.bytes 16), ("leftB", .bytes 16), ("rightA", .bytes 16), ("rightB", .bytes 16),
      ("mask", .bytes 16)] "rightA" = ByteCircuit.inputBytes 32 16 := by simp [lookup, lookupFrom, Shape.variables]
  have hRB : lookup [("leftA", Shape.bytes 16), ("leftB", .bytes 16), ("rightA", .bytes 16), ("rightB", .bytes 16),
      ("mask", .bytes 16)] "rightB" = ByteCircuit.inputBytes 48 16 := by simp [lookup, lookupFrom, Shape.variables]
  have hM : lookup [("leftA", Shape.bytes 16), ("leftB", .bytes 16), ("rightA", .bytes 16), ("rightB", .bytes 16),
      ("mask", .bytes 16)] "mask" = ByteCircuit.inputBytes 64 16 := by simp [lookup, lookupFrom, Shape.variables]
  simp only [gcmMultiply, toParty, List.map_cons, List.map_nil, hLA, hLB, hRA, hRB, hM, xorBytes_eval,
    (Gcm.evaluationHom assign).unpack, Ghash.multiply_map (Gcm.evaluationHom assign).field,
    (Gcm.evaluationHom assign).pack]

/-! ### The schedule of `GcmShares::ensure`, on abstract shares -/

namespace Schedule
open GhashShares

/-- The garbling party keeps the mask; the other party is opened
`value ⊕ mask`. -/
def reshare (mask value : W) : W × W := (mask, value ^^^ mask)

/-- Each party squares its own share. -/
def square (mul : W → W → W) (s : W × W) : W × W := (mul s.1 s.1, mul s.2 s.2)

/-- What the multiply kernel computes from two shared values. -/
def product (mul : W → W → W) (left right : W × W) : W := mul (left.1 ^^^ left.2) (right.1 ^^^ right.2)

/-- One iteration of the loop in `GcmShares::ensure`: `shares` holds the pairs
for powers `1 … shares.length`, in that order; the next power is appended.
`mask k` is the garbling party's fresh mask for power `k`. -/
def extend (mul : W → W → W) (mask : Nat → W) (shares : List (W × W)) : List (W × W) :=
  if (shares.length + 1) % 2 = 0 then
    shares ++ [square mul (shares.getD ((shares.length + 1) / 2 - 1) (0, 0))]
  else
    shares ++ [reshare (mask (shares.length + 1))
      (product mul (shares.getD (shares.length - 1) (0, 0)) (shares.getD 0 (0, 0)))]

/-- The pairs of shares of powers `1 … count`, in that order, after
`GcmShares::ensure` with key `h` (first step: one key-share kernel run). -/
def ensure (mul : W → W → W) (h : W) (mask : Nat → W) : Nat → List (W × W)
  | 0 => []
  | 1 => [reshare (mask 1) h]
  | count + 2 => extend mul mask (ensure mul h mask (count + 1))

/-- Every pair XORs to the power at its position. -/
def Good (mul : W → W → W) (h : W) (shares : List (W × W)) : Prop :=
  ∀ k s, shares[k]? = some s → s.1 ^^^ s.2 = power mul h k

theorem xor_unmask (a b : W) : a ^^^ (b ^^^ a) = b := by
  ext i
  simp only [BitVec.getElem_xor]
  cases a[i] <;> cases b[i] <;> rfl

theorem reshare_value (mask value : W) : (reshare mask value).1 ^^^ (reshare mask value).2 = value :=
  xor_unmask mask value

theorem square_value (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (s : W × W) :
    (square mul s).1 ^^^ (square mul s).2 = mul (s.1 ^^^ s.2) (s.1 ^^^ s.2) :=
  (square_additive mul laws additive s.1 s.2).symm

/-- `hⁱ⁺¹ · hʲ⁺¹ = hⁱ⁺ʲ⁺²`. -/
theorem power_mul (mul : W → W → W) (laws : Laws mul) (h : W) (i j : Nat) :
    mul (power mul h i) (power mul h j) = power mul h (i + j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show mul (power mul h i) (mul (power mul h j) h) = mul (power mul h (i + j + 1)) h
      rw [← laws.assoc, ih]

theorem getD_spec {α : Type} (l : List α) (k : Nat) (d : α) (hk : k < l.length) :
    l[k]? = some (l.getD k d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem good_snoc (mul : W → W → W) (h : W) (shares : List (W × W)) (e : W × W)
    (good : Good mul h shares) (he : e.1 ^^^ e.2 = power mul h shares.length) :
    Good mul h (shares ++ [e]) := by
  intro k s hs
  by_cases hk : k < shares.length
  · rw [List.getElem?_append_left hk] at hs
    exact good k s hs
  · by_cases hk' : k = shares.length
    · subst hk'
      simp at hs
      subst hs
      exact he
    · have none : (shares ++ [e])[k]? = none := by
        apply List.getElem?_eq_none
        simp only [List.length_append, List.length_singleton]
        omega
      rw [none] at hs
      cases hs

theorem extend_length (mul : W → W → W) (mask : Nat → W) (shares : List (W × W)) :
    (extend mul mask shares).length = shares.length + 1 := by
  unfold extend
  split <;> simp

theorem extend_good (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (h : W)
    (mask : Nat → W) (shares : List (W × W)) (pos : 0 < shares.length) (good : Good mul h shares) :
    Good mul h (extend mul mask shares) := by
  unfold extend
  split
  · rename_i even
    apply good_snoc mul h shares _ good
    have v := good _ _ (getD_spec shares ((shares.length + 1) / 2 - 1) (0, 0) (by omega))
    have e : (shares.length + 1) / 2 - 1 + ((shares.length + 1) / 2 - 1) + 1 = shares.length := by omega
    rw [square_value mul laws additive, v, power_mul mul laws, e]
  · rename_i odd
    apply good_snoc mul h shares _ good
    obtain ⟨m, hm⟩ : ∃ m, shares.length = m + 1 := ⟨shares.length - 1, by omega⟩
    have vl := good m _ (getD_spec shares m (0, 0) (by omega))
    have vr := good 0 _ (getD_spec shares 0 (0, 0) pos)
    have idx : shares.length - 1 = m := by omega
    rw [reshare_value, product, idx, vl, vr, hm]
    rfl

theorem ensure_length (mul : W → W → W) (h : W) (mask : Nat → W) :
    ∀ count, (ensure mul h mask count).length = count
  | 0 => rfl
  | 1 => rfl
  | count + 2 => by
      show (extend mul mask (ensure mul h mask (count + 1))).length = count + 2
      rw [extend_length, ensure_length mul h mask (count + 1)]

theorem ensure_good (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (h : W) (mask : Nat → W) :
    ∀ count, Good mul h (ensure mul h mask count)
  | 0 => by intro k s hs; simp [ensure] at hs
  | 1 => good_snoc mul h [] _ (by intro k s hs; simp at hs) (reshare_value _ _)
  | count + 2 => by
      show Good mul h (extend mul mask (ensure mul h mask (count + 1)))
      exact extend_good mul laws additive h mask _ (by rw [ensure_length]; omega)
        (ensure_good mul laws additive h mask (count + 1))

theorem good_take (mul : W → W → W) (h : W) (shares : List (W × W)) (count : Nat)
    (good : Good mul h shares) : Good mul h (shares.take count) := by
  intro k s hs
  rw [List.getElem?_take] at hs
  split at hs
  · exact good k s hs
  · cases hs

theorem good_values (mul : W → W → W) (h : W) (shares : List (W × W)) (good : Good mul h shares) :
    shares.map (fun s => s.1 ^^^ s.2) = (List.range shares.length).map (power mul h) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < shares.length
  · have at_k := getD_spec shares k (0, 0) hk
    have v := good k _ at_k
    rw [List.getElem?_map, List.getElem?_map, at_k, List.getElem?_range hk]
    exact congrArg some v
  · have ge : shares.length ≤ k := by omega
    simp [ge]

theorem descending_eq (mul : W → W → W) (h : W) (n : Nat) :
    descending mul h n = ((List.range n).map (power mul h)).reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descending, List.range_succ, ih]

theorem zip_fst_snd (l : List (W × W)) :
    List.zipWith (· ^^^ ·) (l.map Prod.fst) (l.map Prod.snd) = l.map (fun s => s.1 ^^^ s.2) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

/-- Shares that are good at every position, cut to `count` powers and put in
the order the tag polynomial uses them (highest power first), XOR to the
descending powers. -/
theorem good_descending (mul : W → W → W) (h : W) (shares : List (W × W)) (good : Good mul h shares)
    (count : Nat) (enough : count ≤ shares.length) :
    List.zipWith (· ^^^ ·) ((shares.take count).reverse.map Prod.fst) ((shares.take count).reverse.map Prod.snd) =
      descending mul h count := by
  have len : (shares.take count).length = count := by
    rw [List.length_take]
    omega
  rw [zip_fst_snd, List.map_reverse, good_values mul h _ (good_take mul h shares count good), len, descending_eq]

/-- Hypothesis (2) of `shared_halves_are_ghash` for the schedule of
`GcmShares::ensure`: with shares of `available` powers, the `count` a record
needs, highest power first, XOR to the descending powers of the key. For any
masks. -/
theorem ensure_descending (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (h : W)
    (mask : Nat → W) (available count : Nat) (enough : count ≤ available) :
    List.zipWith (· ^^^ ·)
        (((ensure mul h mask available).take count).reverse.map Prod.fst)
        (((ensure mul h mask available).take count).reverse.map Prod.snd) =
      descending mul h count :=
  good_descending mul h _ (ensure_good mul laws additive h mask available) count
    (by rw [ensure_length]; exact enough)

end Schedule

/-! ### GHASH from the scheduled shares -/

/-- `shared_halves_are_ghash` without the field-law hypothesis. -/
theorem shared_halves_are_ghash_proved
    (traffic aad ciphertext : List (BitVec 8)) (first second : List (BitVec 128))
    (same : first.length = second.length)
    (shares : List.zipWith (· ^^^ ·) first second =
      GhashShares.descending (Ghash.multiply Ghash.concrete) (hashKeyOf traffic)
        (Gcm.authInput Gcm.concrete aad ciphertext).length) :
    Aes.addRoundKey Gcm.concrete.aes
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext) first))
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext) second)) =
      ghashOf traffic aad ciphertext :=
  shared_halves_are_ghash GhashField.laws traffic aad ciphertext first second same shares

/-- With the shares the schedule produces from the key `H = AES_K(0)` (any
masks, any number `available` of prepared powers that covers the record), the
bytes of the two parties' local tags XOR to GCM's GHASH value. No hypothesis on
the multiplication or on the shares remains. -/
theorem scheduled_halves_are_ghash (traffic aad ciphertext : List (BitVec 8)) (mask : Nat → BitVec 128)
    (available : Nat) (enough : (Gcm.authInput Gcm.concrete aad ciphertext).length ≤ available) :
    Aes.addRoundKey Gcm.concrete.aes
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext)
          (((Schedule.ensure (Ghash.multiply Ghash.concrete) (hashKeyOf traffic) mask available).take
            (Gcm.authInput Gcm.concrete aad ciphertext).length).reverse.map Prod.fst)))
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext)
          (((Schedule.ensure (Ghash.multiply Ghash.concrete) (hashKeyOf traffic) mask available).take
            (Gcm.authInput Gcm.concrete aad ciphertext).length).reverse.map Prod.snd))) =
      ghashOf traffic aad ciphertext :=
  shared_halves_are_ghash_proved traffic aad ciphertext _ _
    (by simp only [List.length_map])
    (Schedule.ensure_descending _ GhashField.laws GhashShares.multiply_key_additive _ mask available _ enough)

/-! ### The kernels on field elements

`Gcm.concrete.pack` of 16 bytes is the field element the runtime's byte blocks
stand for. On these, the two kernels are exactly the model's `reshare`. -/

theorem join_xor_bit : ∀ (x y : List (BitVec 8)), x.length = y.length → ∀ j,
    (ByteCircuit.joinValue (List.zipWith (· ^^^ ·) x y)).getLsbD j =
      ((ByteCircuit.joinValue x).getLsbD j ^^ (ByteCircuit.joinValue y).getLsbD j)
  | [], [], _, j => by simp [ByteCircuit.joinValue]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: x, b :: y, h, j => by
      have len : x.length = y.length := by simpa using h
      have ih := join_xor_bit x y len
      simp only [List.zipWith_cons_cons, ByteCircuit.joinValue, BitVec.getLsbD_cast, BitVec.getLsbD_append,
        List.length_zipWith, ih, len, Nat.min_self, BitVec.getLsbD_xor]
      by_cases c : j < 8 * y.length <;> simp [c]

/-- Packing is additive on byte strings of equal length. -/
theorem pack_xor (x y : List (BitVec 8)) (same : x.length = y.length) :
    Gcm.concrete.pack (Aes.addRoundKey Gcm.concrete.aes x y) = Gcm.concrete.pack x ^^^ Gcm.concrete.pack y := by
  show (ByteCircuit.joinValue (List.zipWith (· ^^^ ·) x y)).setWidth 128 =
    (ByteCircuit.joinValue x).setWidth 128 ^^^ (ByteCircuit.joinValue y).setWidth 128
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, join_xor_bit x y same]
  simp [hj]

/-- The bytes of a word, most significant first, built from the low end. -/
def bytesOf (w : BitVec 128) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => w.extractLsb' (8 * n) 8 :: bytesOf w n

theorem bytesOf_length (w : BitVec 128) : ∀ n, (bytesOf w n).length = n
  | 0 => rfl
  | n + 1 => by simp only [bytesOf, List.length_cons, bytesOf_length w n]

theorem bytesOf_eq (w : BitVec 128) (n : Nat) :
    (List.range n).map (fun i => w.extractLsb' (8 * (n - 1 - i)) 8) = bytesOf w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have e2 : ∀ i, n + 1 - 1 - (i + 1) = n - 1 - i := by intro i; omega
      have e1 : n + 1 - 1 - 0 = n := by omega
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def, Nat.succ_eq_add_one,
        e1, e2, ih, bytesOf]

theorem join_bytesOf (w : BitVec 128) : ∀ (n j : Nat),
    (ByteCircuit.joinValue (bytesOf w n)).getLsbD j = (decide (j < 8 * n) && w.getLsbD j)
  | 0, j => by simp [bytesOf, ByteCircuit.joinValue]
  | n + 1, j => by
      simp only [bytesOf, ByteCircuit.joinValue, BitVec.getLsbD_cast, BitVec.getLsbD_append, join_bytesOf w n,
        bytesOf_length, BitVec.getLsbD_extractLsb']
      by_cases c : j < 8 * n
      · have c' : j < 8 * (n + 1) := by omega
        simp [c, c']
      · have back : 8 * n + (j - 8 * n) = j := by omega
        have same : decide (j - 8 * n < 8) = decide (j < 8 * (n + 1)) := by
          rw [decide_eq_decide]
          omega
        simp only [c, ↓reduceIte, back, same]

/-- Packing the bytes of a field element gives the element back. -/
theorem pack_unpack (w : BitVec 128) : Gcm.concrete.pack (Gcm.concrete.unpack w) = w := by
  have e : Gcm.concrete.unpack w = bytesOf w 16 := bytesOf_eq w 16
  rw [e]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  show ((ByteCircuit.joinValue (bytesOf w 16)).setWidth 128).getLsbD j = w.getLsbD j
  rw [BitVec.getLsbD_setWidth, join_bytesOf]
  simp [hj]

/-- One `gcmKeyShare` run: (the mask, the opened value), as field elements, is
the model's sharing of `H = AES_K(0)`. -/
theorem gcmKeyShare_reshare (assign : BVExpr.Assignment) (masked : List (BitVec 8))
    (out : gcmKeyShare.outputs.map (fun field => field.value.map (BVExpr.eval assign)) = [masked]) :
    (Gcm.concrete.pack (inputValue assign 60 16), Gcm.concrete.pack masked) =
      Schedule.reshare (Gcm.concrete.pack (inputValue assign 60 16)) (hashKeyOf (inputValue assign 0 60)) := by
  rw [gcmKeyShare_spec] at out
  simp only [List.cons.injEq, and_true] at out
  subst out
  rw [pack_xor]
  · rfl
  · rw [Aes.encryptExpanded_length _ 10 _ _ (expandedOf_length _ (inputValue_length assign 0 60))]
    simp [ByteCircuit.inputBytes]

/-- One `gcmMultiply` run: (the mask, the opened value), as field elements, is
the model's sharing of the product of the two shared inputs. -/
theorem gcmMultiply_reshare (assign : BVExpr.Assignment) (masked : List (BitVec 8))
    (out : gcmMultiply.outputs.map (fun field => field.value.map (BVExpr.eval assign)) = [masked]) :
    (Gcm.concrete.pack (inputValue assign 64 16), Gcm.concrete.pack masked) =
      Schedule.reshare (Gcm.concrete.pack (inputValue assign 64 16))
        (Schedule.product (Ghash.multiply Ghash.concrete)
          (Gcm.concrete.pack (inputValue assign 0 16), Gcm.concrete.pack (inputValue assign 16 16))
          (Gcm.concrete.pack (inputValue assign 32 16), Gcm.concrete.pack (inputValue assign 48 16))) := by
  rw [gcmMultiply_spec] at out
  simp only [List.cons.injEq, and_true] at out
  subst out
  rw [pack_xor, pack_xor, pack_xor, pack_unpack]
  · rfl
  all_goals simp [Ghash.unpackValue, Gcm.concrete, ByteCircuit.inputBytes]

#print axioms gcmKeyShare_spec
#print axioms gcmMultiply_spec
#print axioms gcmKeyShare_reshare
#print axioms gcmMultiply_reshare
#print axioms Schedule.ensure_descending
#print axioms shared_halves_are_ghash_proved
#print axioms scheduled_halves_are_ghash

end TlsMpc.HybridKernel
