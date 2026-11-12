import TlsMpcProofs.OffsetAgreementDist
import TlsMpcProofs.Prime25519
import TlsMpcProofs.Hiding
import TlsMpc.Signal.XEdDsaScalar
import Mathlib.Data.Fintype.BigOperators

/-!
# The deployed offset sampling: statistical distance, primality of `ℓ`, several messages

`OffsetAgreementDist` proves the published key `initial·B + offset·B` independent of the initial
scalar when the offset is uniform in `ZMod ℓ`. The deployed offset is not: per message
(`handshake_backend/EmpHybridWork/service_kernels.h`, `seal_open` and `ephemeral`) each party draws
32 bytes `mine` from `emp::PRG`, commits with `SHA256(mine)`, the commitments are exchanged, then
the values; a party aborts unless the peer's value matches its commitment and the two commitments
differ. The offset is `mine XOR peer` byte by byte, and `OffsetAgreement::step` /
`step_inputs` (`edwards_points.h`) clear the top four bits (`offset[31] &= 15`), so as a
little-endian integer the offset is `(mine XOR peer) mod 2²⁵²`, an integer in `[0, 2²⁵²)`; the
key is `K₀ + offset·B` (`crypto_scalarmult_ed25519_base_noclamp`, no reduction needed since
`2²⁵² < ℓ`). Here `mine` and `peer` are `BitVec 256` whose `toNat` is that little-endian integer.

**Model.** The honest party's `mine` is uniform; the peer's value is a fixed `peer` (any value),
i.e. independent of `mine` — what the commitment provides (`idealCommit`, a hypothesis, not proved
about SHA-256). `G` is any finite commutative group of order `ℓ` (H-GROUP stays a hypothesis);
scalars act by `k ↦ k.val • B`.

Closeness: `EventClose p q δ` says every event has probability under `p` at most its probability
under `q` plus `δ`; `StatClose` is both directions, i.e. total-variation distance `≤ δ`.

* `deployedOffset_uniform`: the offset is exactly uniform on `[0, 2²⁵²)` (`Fin (2²⁵²)`), whatever
  `peer` is.
* `offset_cast_close_uniform`: as an element of `ZMod ℓ` it is within `(ℓ − 2²⁵²)/ℓ` of uniform
  (for any `ℓ ≥ 2²⁵²`).
* `deployed_key_close`: the published key's distributions for any two initial scalars are within
  `(ℓ − 2²⁵²)/2²⁵²` (not `/ℓ`: the two shifted ranges differ in up to `ℓ − 2²⁵²` points, each of
  mass `2⁻²⁵²`; with `ℓ` prime and `B ≠ 0` this is attained).
* `deployed_key_close_ideal`, `deployed_key_close_uniform`: within `(ℓ − 2²⁵²)/ℓ` of the key with
  a uniform offset, and (ℓ prime, `B ≠ 0`) of the uniform distribution on `G`.
* `prime_order`: `ℓ = 2²⁵² + 27742317777372353535851937790883648493` (the main package's
  `Signal.XEdDsaScalar.order`) is prime, by a Pocklington chain (`Prime25519.pocklington`).
* `order_gap_lt`: `(ℓ − 2²⁵²)/2²⁵² < 2⁻¹²⁷` (so also `(ℓ − 2²⁵²)/ℓ < 2⁻¹²⁷`).
* Several messages: `offset_public_keys_independent` / `offset_public_keys_uniform` (offsets
  uniform in `ZMod ℓ`: the joint distribution of the `k` keys does not depend on the initial
  scalar; uniform on `G^k`, i.e. independent uniform keys, for `ℓ` prime and `B ≠ 0`), and
  `deployed_keys_close` (deployed offsets, `k` messages: within `k·(ℓ − 2²⁵²)/2²⁵²`).

Not modelled: the two aborts that depend only on the offsets (`peer_commit == commit`, i.e.
`mine = peer`, probability `2⁻²⁵⁶`; `crypto_scalarmult_ed25519_base_noclamp` refusing the offset
`0`, probability `2⁻²⁵²`): they do not depend on the initial scalar; a peer that chooses its value
after seeing `mine` (excluded by `idealCommit`); a peer choosing `peer` adaptively across messages
(the several-message theorems take a fixed vector of peer values).
-/

namespace TlsMpcProofs.OffsetSampling
open PMF Function TlsMpcProofs.OffsetAgreement

/-! ## Closeness of distributions -/

/-- Every event has probability under `p` at most its probability under `q` plus `δ`. -/
def EventClose {α : Type*} (p q : PMF α) (δ : ENNReal) : Prop :=
  ∀ s : Set α, p.toOuterMeasure s ≤ q.toOuterMeasure s + δ

/-- Total-variation distance at most `δ` (both directions of `EventClose`). -/
def StatClose {α : Type*} (p q : PMF α) (δ : ENNReal) : Prop :=
  EventClose p q δ ∧ EventClose q p δ

/-- Post-processing does not increase the distance. -/
theorem eventClose_map {α β : Type*} {p q : PMF α} {δ : ENNReal} (h : EventClose p q δ)
    (f : α → β) : EventClose (p.map f) (q.map f) δ := by
  intro s
  rw [toOuterMeasure_map_apply, toOuterMeasure_map_apply]
  exact h _

theorem statClose_map {α β : Type*} {p q : PMF α} {δ : ENNReal} (h : StatClose p q δ)
    (f : α → β) : StatClose (p.map f) (q.map f) δ :=
  ⟨eventClose_map h.1 f, eventClose_map h.2 f⟩

theorem eventClose_mono {α : Type*} {p q : PMF α} {δ ε : ENNReal} (h : EventClose p q δ)
    (hle : δ ≤ ε) : EventClose p q ε := fun s =>
  (h s).trans (by gcongr)

/-! ## Counting -/

theorem frac_le {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d ≤ b * c) :
    (a : ENNReal) / b ≤ (c : ENNReal) / d := by
  have hb' : (b : ENNReal) ≠ 0 := by exact_mod_cast hb
  have hd' : (d : ENNReal) ≠ 0 := by exact_mod_cast hd
  rw [← ENNReal.mul_div_mul_right (a : ENNReal) (b : ENNReal) hd' (ENNReal.natCast_ne_top d),
    ← ENNReal.mul_div_mul_left (c : ENNReal) (d : ENNReal) hb' (ENNReal.natCast_ne_top b)]
  apply ENNReal.div_le_div_right
  exact_mod_cast h

theorem div_lt_div_of_lt {a c x : ℕ} (hx : x ≠ 0) (h : a < c) :
    (a : ENNReal) / x < (c : ENNReal) / x := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top x))
    (ENNReal.inv_ne_top.mpr (by exact_mod_cast hx)) (by exact_mod_cast h)

open Classical in
/-- The probability of an event under a uniform distribution pushed through `e`. -/
theorem prob_map_uniform {R Z : Type*} [Fintype R] [Nonempty R] (e : R → Z) (s : Set Z) :
    (map e (uniformOfFintype R)).toOuterMeasure s =
      ((Finset.univ.filter (fun r => e r ∈ s)).card : ENNReal) / Fintype.card R := by
  rw [toOuterMeasure_map_apply, toOuterMeasure_uniformOfFintype_apply, Fintype.card_subtype]
  rfl

open Classical in
theorem filter_card_eq_image {R Z : Type*} [Fintype R] (e : R → Z) (he : Injective e) (s : Set Z) :
    (Finset.univ.filter (fun r => e r ∈ s)).card = ((Finset.univ.image e).filter (· ∈ s)).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ he]

open Classical in
/-- Two injections of `R` into `Z` hit an event in numbers that differ by at most `|Z| − |R|`. -/
theorem count_le_of_injective {R Z : Type*} [Fintype R] [Fintype Z] (e1 e2 : R → Z)
    (h1 : Injective e1) (h2 : Injective e2) (s : Set Z) :
    (Finset.univ.filter (fun r => e1 r ∈ s)).card ≤
      (Finset.univ.filter (fun r => e2 r ∈ s)).card + (Fintype.card Z - Fintype.card R) := by
  rw [filter_card_eq_image e1 h1, filter_card_eq_image e2 h2]
  have hsub : (Finset.univ.image e1).filter (· ∈ s) ⊆
      (Finset.univ.image e2).filter (· ∈ s) ∪ (Finset.univ \ Finset.univ.image e2) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    by_cases h : z ∈ Finset.univ.image e2
    · exact Or.inl ⟨h, hz.2⟩
    · exact Or.inr ⟨Finset.mem_univ z, h⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_univ_sdiff, Finset.card_image_of_injective _ h2, Finset.card_univ]

/-- **Two injections, uniform input:** the pushed-forward distributions are
`(|Z| − |R|)/|R|`-close (one direction; swap `e1`, `e2` for the other). **gen**. -/
theorem eventClose_injective {R Z : Type*} [Fintype R] [Nonempty R] [Fintype Z] (e1 e2 : R → Z)
    (h1 : Injective e1) (h2 : Injective e2) :
    EventClose (map e1 (uniformOfFintype R)) (map e2 (uniformOfFintype R))
      (((Fintype.card Z - Fintype.card R : ℕ) : ENNReal) / Fintype.card R) := by
  classical
  intro s
  rw [prob_map_uniform, prob_map_uniform, ENNReal.div_add_div_same]
  apply ENNReal.div_le_div_right
  exact_mod_cast count_le_of_injective e1 e2 h1 h2 s

/-- **An injection of a uniform `R` into `Z` is `(|Z| − |R|)/|Z|`-close to uniform on `Z`**, both
directions (total variation). **gen**. -/
theorem statClose_uniform {R Z : Type*} [Fintype R] [Nonempty R] [Fintype Z] [Nonempty Z]
    (e : R → Z) (he : Injective e) :
    StatClose (map e (uniformOfFintype R)) (uniformOfFintype Z)
      (((Fintype.card Z - Fintype.card R : ℕ) : ENNReal) / Fintype.card Z) := by
  classical
  have hZ : (map id (uniformOfFintype Z)) = uniformOfFintype Z := PMF.map_id _
  have hRZ : Fintype.card R ≤ Fintype.card Z := Fintype.card_le_of_injective e he
  have hR0 : Fintype.card R ≠ 0 := Fintype.card_ne_zero
  have hZ0 : Fintype.card Z ≠ 0 := Fintype.card_ne_zero
  obtain ⟨d, hd⟩ : ∃ d, Fintype.card Z = Fintype.card R + d := ⟨_, (Nat.add_sub_of_le hRZ).symm⟩
  have hsub : Fintype.card Z - Fintype.card R = d := by omega
  constructor
  · intro s
    rw [← hZ, prob_map_uniform, prob_map_uniform, ENNReal.div_add_div_same, ← Nat.cast_add]
    apply frac_le hR0 hZ0
    -- k·|Z| ≤ |R|·(m + d) from k ≤ m and k ≤ |R|
    have hkm : (Finset.univ.filter (fun r => e r ∈ s)).card ≤
        (Finset.univ.filter (fun z => id z ∈ s)).card := by
      apply Finset.card_le_card_of_injOn e
      · intro r hr
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and, id] at hr ⊢
        exact hr
      · exact he.injOn
    have hkR : (Finset.univ.filter (fun r => e r ∈ s)).card ≤ Fintype.card R :=
      (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])
    rw [hsub, hd]
    nlinarith
  · intro s
    rw [← hZ, prob_map_uniform, prob_map_uniform]
    have hm : (Finset.univ.filter (fun z => id z ∈ s)).card ≤
        (Finset.univ.filter (fun r => e r ∈ s)).card + d := by
      have h := count_le_of_injective (R := Z) (Z := Z) id id injective_id injective_id s
      -- the image of `e` and its complement
      have hsub2 : Finset.univ.filter (fun z => id z ∈ s) ⊆
          (Finset.univ.image e).filter (· ∈ s) ∪ (Finset.univ \ Finset.univ.image e) := by
        intro z hz
        rw [Finset.mem_filter] at hz
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
        by_cases h : z ∈ Finset.univ.image e
        · exact Or.inl ⟨h, hz.2⟩
        · exact Or.inr ⟨Finset.mem_univ z, h⟩
      clear h
      calc _ ≤ _ := Finset.card_le_card hsub2
        _ ≤ _ := Finset.card_union_le _ _
        _ = _ := by
          rw [Finset.card_univ_sdiff, Finset.card_image_of_injective _ he, Finset.card_univ,
            filter_card_eq_image e he, hsub]
    calc _ ≤ (((Finset.univ.filter (fun r => e r ∈ s)).card + d : ℕ) : ENNReal) / Fintype.card Z :=
          ENNReal.div_le_div_right (by exact_mod_cast hm) _
      _ = ((Finset.univ.filter (fun r => e r ∈ s)).card : ENNReal) / Fintype.card Z +
            (d : ENNReal) / Fintype.card Z := by
          rw [ENNReal.div_add_div_same, Nat.cast_add]
      _ ≤ _ := by
          rw [hsub]
          gcongr

/-! ## The deployed offset is uniform on `[0, 2²⁵²)` -/

/-- Pushing the uniform distribution on `α × β` to `β`. -/
theorem map_snd_uniform {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [DecidableEq β] : map Prod.snd (uniformOfFintype (α × β)) = uniformOfFintype β :=
  map_uniform_of_fiber_card Prod.snd (Fintype.card α)
    (fun b => by
      rw [show Finset.univ.filter (fun p : α × β => p.2 = b) = Finset.univ ×ˢ {b} by
        ext ⟨x, y⟩; simp [eq_comm]]
      simp)
    (by rw [Fintype.card_prod])

/-- The deployed offset: `(mine XOR peer) mod 2²⁵²` (bytes XORed, `offset[31] &= 15`). -/
def deployedOffset (mine peer : BitVec 256) : Fin (2 ^ 252) :=
  ⟨(mine ^^^ peer).toNat % 2 ^ 252, Nat.mod_lt _ (by positivity)⟩

/-- A 256-bit word as (top 4 bits, low 252 bits). -/
def splitEquiv : BitVec 256 ≃ Fin 16 × Fin (2 ^ 252) :=
  (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ : BitVec 256 ≃ Fin (2 ^ 256)).trans
    ((finCongr (by norm_num : 2 ^ 256 = 16 * 2 ^ 252)).trans finProdFinEquiv.symm)

theorem deployedOffset_eq (peer : BitVec 256) :
    (fun mine => deployedOffset mine peer) = Prod.snd ∘ ((xorEquiv peer).trans splitEquiv) := by
  funext m
  rfl

/-- **The deployed offset is exactly uniform on `[0, 2²⁵²)`** for a uniform `mine`, whatever the
peer's value. **M** (`idealCommit`: `peer` does not depend on `mine`). -/
theorem deployedOffset_uniform (peer : BitVec 256) :
    map (fun mine => deployedOffset mine peer) (uniformOfFintype (BitVec 256)) =
      uniformOfFintype (Fin (2 ^ 252)) := by
  rw [deployedOffset_eq, ← map_comp, map_uniform_equiv, map_snd_uniform]

/-! ## One message -/

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- The deployed key for the initial scalar and an offset below `2²⁵²`: `initial·B + offset·B`. -/
def deployedKey {ℓ : ℕ} (B : G) (initial : ZMod ℓ) (offset : Fin (2 ^ 252)) : G :=
  initial.val • B + offset.val • B

/-- The offset as a scalar modulo `ℓ`. -/
def castOffset (ℓ : ℕ) (offset : Fin (2 ^ 252)) : ZMod ℓ := (offset.val : ZMod ℓ)

theorem castOffset_injective {ℓ : ℕ} (hℓ : 2 ^ 252 ≤ ℓ) : Injective (castOffset ℓ) := by
  intro x y hxy
  have hx := ZMod.val_natCast_of_lt (n := ℓ) (lt_of_lt_of_le x.isLt hℓ)
  have hy := ZMod.val_natCast_of_lt (n := ℓ) (lt_of_lt_of_le y.isLt hℓ)
  apply Fin.ext
  rw [← hx, ← hy]
  exact congrArg ZMod.val hxy

variable {ℓ : ℕ} [NeZero ℓ]

omit [NeZero ℓ] in
/-- The deployed key is the ideal one (`OffsetAgreementDist.publicKey`) at the offset's residue. -/
theorem deployedKey_eq_publicKey (hℓ : Fintype.card G = ℓ) (B : G) (initial : ZMod ℓ)
    (offset : Fin (2 ^ 252)) : deployedKey B initial offset = publicKey B initial (castOffset ℓ offset) := by
  have h := nsmul_mod_card B offset.val
  rw [hℓ] at h
  simp only [deployedKey, publicKey, castOffset, ZMod.val_natCast, h]

/-- … and a function of the scalar `initial + offset`. -/
theorem deployedKey_eq_scalar (hℓ : Fintype.card G = ℓ) (B : G) (initial : ZMod ℓ) :
    deployedKey B initial = (fun z : ZMod ℓ => z.val • B) ∘ (fun x => initial + castOffset ℓ x) := by
  funext x
  rw [deployedKey_eq_publicKey hℓ, Function.comp_apply, val_add_nsmul hℓ]
  rfl

/-- **The offset modulo `ℓ` is `(ℓ − 2²⁵²)/ℓ`-close to uniform in `ZMod ℓ`** (both directions),
for any `ℓ ≥ 2²⁵²`, through the deployed sampling. **M**. -/
theorem offset_cast_close_uniform (hN : 2 ^ 252 ≤ ℓ) (peer : BitVec 256) :
    StatClose (map (fun mine => castOffset ℓ (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (uniformOfFintype (ZMod ℓ)) (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / (ℓ : ENNReal)) := by
  have h := statClose_uniform (castOffset ℓ) (castOffset_injective hN)
  rw [ZMod.card, Fintype.card_fin] at h
  have hc : (fun mine => castOffset ℓ (deployedOffset mine peer)) =
      castOffset ℓ ∘ (fun mine => deployedOffset mine peer) := rfl
  rw [hc, ← map_comp, deployedOffset_uniform]
  exact h

/-- **The published key, deployed sampling, any two initial scalars:** for every event,
`Pr[key(initial) ∈ s] ≤ Pr[key(other) ∈ s] + (ℓ − 2²⁵²)/2²⁵²` (by symmetry also the other way).
Any `ℓ ≥ 2²⁵²`, any finite commutative group of order `ℓ` (H-GROUP), any `B`, any peer value.
**M**. -/
theorem deployed_key_close (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G) (peer : BitVec 256)
    (initial other : ZMod ℓ) :
    EventClose
      (map (fun mine => deployedKey B initial (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (map (fun mine => deployedKey B other (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal)) := by
  have hshift : ∀ a : ZMod ℓ, Injective (fun x => a + castOffset ℓ x) := fun a x y hxy =>
    castOffset_injective hN (add_left_cancel hxy)
  have h := eventClose_map (eventClose_injective _ _ (hshift initial) (hshift other))
    (fun z : ZMod ℓ => z.val • B)
  rw [ZMod.card, Fintype.card_fin, map_comp, map_comp, ← deployedKey_eq_scalar hℓ,
    ← deployedKey_eq_scalar hℓ] at h
  have hc : ∀ a : ZMod ℓ, (fun mine => deployedKey B a (deployedOffset mine peer)) =
      deployedKey B a ∘ (fun mine => deployedOffset mine peer) := fun a => rfl
  rw [hc, hc, ← map_comp, ← map_comp, deployedOffset_uniform]
  exact h

/-- **The deployed key is `(ℓ − 2²⁵²)/ℓ`-close to the key with a uniform offset** (both
directions). **M**. -/
theorem deployed_key_close_ideal (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G)
    (peer : BitVec 256) (initial : ZMod ℓ) :
    StatClose
      (map (fun mine => deployedKey B initial (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (map (publicKey B initial) (uniformOfFintype (ZMod ℓ)))
      (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / (ℓ : ENNReal)) := by
  have h := statClose_map (offset_cast_close_uniform hN peer) (publicKey B initial)
  rw [map_comp] at h
  have hc : (fun mine => deployedKey B initial (deployedOffset mine peer)) =
      publicKey B initial ∘ (fun mine => castOffset ℓ (deployedOffset mine peer)) := by
    funext mine
    exact deployedKey_eq_publicKey hℓ B initial _
  rw [hc]
  exact h

/-- **With `ℓ` prime and `B ≠ 0`: the deployed key is `(ℓ − 2²⁵²)/ℓ`-close to uniform on `G`**
(both directions). **M**. -/
theorem deployed_key_close_uniform [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ)
    (B : G) (hB : B ≠ 0) (peer : BitVec 256) (initial : ZMod ℓ) :
    StatClose
      (map (fun mine => deployedKey B initial (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (uniformOfFintype G) (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / (ℓ : ENNReal)) := by
  haveI : Nonempty G := ⟨0⟩
  rw [← offset_public_key_uniform hℓ B hB initial]
  exact deployed_key_close_ideal hℓ hN B peer initial

/-! ## Several messages -/

section Several
variable {k : ℕ}

/-- The keys of `k` messages of one conversation (one initial scalar, one offset per message). -/
def publicKeys (B : G) (initial : ZMod ℓ) (offsets : Fin k → ZMod ℓ) : Fin k → G :=
  fun i => publicKey B initial (offsets i)

theorem publicKey_shift (hℓ : Fintype.card G = ℓ) (B : G) (initial other offset : ZMod ℓ) :
    publicKey B initial offset = publicKey B other (offset + (initial - other)) := by
  simp only [publicKey]
  have h := val_add_nsmul hℓ B (offset + (initial - other)) other
  rw [show offset + (initial - other) + other = offset + initial by ring] at h
  rw [val_add_nsmul hℓ B offset initial] at h
  rw [add_comm (initial.val • B), h]
  abel

/-- **Several messages, offsets uniform in `ZMod ℓ`:** the joint distribution of the `k` keys
is the same for any two initial scalars (H-GROUP as "finite commutative group of order `ℓ`").
**M**. -/
theorem offset_public_keys_independent (hℓ : Fintype.card G = ℓ) (B : G) (initial other : ZMod ℓ) :
    map (publicKeys (k := k) B initial) (uniformOfFintype (Fin k → ZMod ℓ)) =
      map (publicKeys B other) (uniformOfFintype (Fin k → ZMod ℓ)) :=
  hiding_of_bijection (fun s o => publicKeys B s o) initial other
    (Equiv.addRight (fun _ => initial - other)) (fun o => by
      funext i
      simp only [publicKeys, Equiv.coe_addRight, Pi.add_apply]
      exact publicKey_shift hℓ B initial other (o i))

/-- **… and, with `ℓ` prime and `B ≠ 0`, uniform on `G^k`**: `k` independent uniform keys,
whatever the initial scalar (so the keys are independent of it and of each other). **M**. -/
theorem offset_public_keys_uniform [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (B : G) (hB : B ≠ 0)
    (initial : ZMod ℓ) :
    map (publicKeys (k := k) B initial) (uniformOfFintype (Fin k → ZMod ℓ)) =
      uniformOfFintype (Fin k → G) := by
  haveI : Nonempty G := ⟨0⟩
  apply uniform_of_bijective
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => funext fun i => ?_, by simp [ZMod.card, hℓ]⟩
  have h := congrFun hab i
  simp only [publicKeys, publicKey] at h
  exact val_nsmul_injective hℓ B hB (add_left_cancel h)

/-- Pushing the uniform distribution on `Fin k → R` to one coordinate. -/
theorem map_eval_uniform {R : Type*} [Fintype R] [Nonempty R] [DecidableEq R] (i : Fin k) :
    map (fun x : Fin k → R => x i) (uniformOfFintype (Fin k → R)) = uniformOfFintype R := by
  have h : (fun x : Fin k → R => x i) = Prod.snd ∘ ((Equiv.funSplitAt i R).trans (Equiv.prodComm _ _)) := by
    funext x
    rfl
  rw [h, ← map_comp, map_uniform_equiv, map_snd_uniform]

open Classical in
/-- Two injections: the points of `R` whose first image misses the second's range number at most
`|Z| − |R|`. -/
theorem bad_card_le {R Z : Type*} [Fintype R] [Fintype Z] (e1 e2 : R → Z) (h1 : Injective e1)
    (h2 : Injective e2) :
    (Finset.univ.filter (fun r => e1 r ∉ Set.range e2)).card ≤ Fintype.card Z - Fintype.card R := by
  calc _ ≤ (Finset.univ \ Finset.univ.image e2).card := by
        apply Finset.card_le_card_of_injOn e1
        · intro r hr
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Set.mem_range,
            not_exists] at hr
          simp only [Finset.coe_sdiff, Finset.coe_univ, Finset.coe_image, Set.mem_sdiff, Set.mem_univ,
            Set.mem_image, true_and, not_exists]
          exact hr
        · exact h1.injOn
    _ = _ := by rw [Finset.card_univ_sdiff, Finset.card_image_of_injective _ h2, Finset.card_univ]

open Classical in
/-- Two injections, uniform input: the first pushed-forward distribution exceeds the second on any
event by at most the probability that the first image misses the second's range. -/
theorem count_le_bad {R Z : Type*} [Fintype R] [Fintype Z] (e1 e2 : R → Z) (h1 : Injective e1)
    (h2 : Injective e2) (s : Set Z) :
    (Finset.univ.filter (fun r => e1 r ∈ s)).card ≤
      (Finset.univ.filter (fun r => e2 r ∈ s)).card +
        (Finset.univ.filter (fun r => e1 r ∉ Set.range e2)).card := by
  have hsub : Finset.univ.filter (fun r => e1 r ∈ s) ⊆
      Finset.univ.filter (fun r => e1 r ∈ s ∧ e1 r ∈ Set.range e2) ∪
        Finset.univ.filter (fun r => e1 r ∉ Set.range e2) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hr ⊢
    by_cases h : e1 r ∈ Set.range e2
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr h
  have hgood : (Finset.univ.filter (fun r => e1 r ∈ s ∧ e1 r ∈ Set.range e2)).card ≤
      (Finset.univ.filter (fun r => e2 r ∈ s)).card := by
    rw [filter_card_eq_image e2 h2]
    apply Finset.card_le_card_of_injOn e1
    · intro r hr
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Set.mem_range] at hr
      obtain ⟨hs, y, hy⟩ := hr
      simp only [Finset.coe_filter, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨⟨y, hy⟩, hs⟩
    · exact h1.injOn
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right hgood _

/-- **Two injections, uniform input, with a bad event:** `map e1` exceeds `map e2` on any event by
at most `Pr[e1 r ∉ range e2]`. **gen**. -/
theorem eventClose_injective_bad {R Z : Type*} [Fintype R] [Nonempty R] [Fintype Z] (e1 e2 : R → Z)
    (h1 : Injective e1) (h2 : Injective e2) :
    EventClose (map e1 (uniformOfFintype R)) (map e2 (uniformOfFintype R))
      ((uniformOfFintype R).toOuterMeasure {r | e1 r ∉ Set.range e2}) := by
  classical
  intro s
  have hbad : (uniformOfFintype R).toOuterMeasure {r | e1 r ∉ Set.range e2} =
      ((Finset.univ.filter (fun r => e1 r ∉ Set.range e2)).card : ENNReal) / Fintype.card R := by
    rw [toOuterMeasure_uniformOfFintype_apply, Fintype.card_subtype]
    rfl
  rw [prob_map_uniform, prob_map_uniform, hbad, ENNReal.div_add_div_same]
  apply ENNReal.div_le_div_right
  exact_mod_cast count_le_bad e1 e2 h1 h2 s

/-- The bad event of `eventClose_injective_bad` has probability at most `(|Z| − |R|)/|R|`. -/
theorem prob_bad_le {R Z : Type*} [Fintype R] [Nonempty R] [Fintype Z] (e1 e2 : R → Z)
    (h1 : Injective e1) (h2 : Injective e2) :
    (uniformOfFintype R).toOuterMeasure {r | e1 r ∉ Set.range e2} ≤
      ((Fintype.card Z - Fintype.card R : ℕ) : ENNReal) / Fintype.card R := by
  classical
  have hbad : (uniformOfFintype R).toOuterMeasure {r | e1 r ∉ Set.range e2} =
      ((Finset.univ.filter (fun r => e1 r ∉ Set.range e2)).card : ENNReal) / Fintype.card R := by
    rw [toOuterMeasure_uniformOfFintype_apply, Fintype.card_subtype]
    rfl
  rw [hbad]
  apply ENNReal.div_le_div_right
  exact_mod_cast bad_card_le e1 e2 h1 h2

/-- The deployed offsets of `k` messages (one honest `mine` and one peer value per message). -/
def deployedOffsets (peers mines : Fin k → BitVec 256) : Fin k → Fin (2 ^ 252) :=
  fun i => deployedOffset (mines i) (peers i)

/-- **The `k` deployed offsets are independent and uniform on `[0, 2²⁵²)`** for independent
uniform `mine`s, whatever the (fixed) peer values. **M**. -/
theorem deployedOffsets_uniform (peers : Fin k → BitVec 256) :
    map (deployedOffsets peers) (uniformOfFintype (Fin k → BitVec 256)) =
      uniformOfFintype (Fin k → Fin (2 ^ 252)) := by
  have h : deployedOffsets peers = Prod.snd ∘
      ((Equiv.piCongrRight (fun i => (xorEquiv (peers i)).trans splitEquiv)).trans
        (Equiv.arrowProdEquivProdArrow _ (fun _ => Fin 16) (fun _ => Fin (2 ^ 252)))) := by
    funext mines
    rfl
  rw [h, ← map_comp, map_uniform_equiv, map_snd_uniform]

/-- The deployed keys of `k` messages. -/
def deployedKeys (B : G) (initial : ZMod ℓ) (offsets : Fin k → Fin (2 ^ 252)) : Fin k → G :=
  fun i => deployedKey B initial (offsets i)

/-- **Several messages, deployed sampling:** the joint distribution of the `k` published keys
for any two initial scalars: every event's probability differs by at most
`k·(ℓ − 2²⁵²)/2²⁵²` (any `ℓ ≥ 2²⁵²`; H-GROUP as "finite commutative group of order `ℓ`"; fixed
peer values, `idealCommit`). **M**. -/
theorem deployed_keys_close (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G)
    (peers : Fin k → BitVec 256) (initial other : ZMod ℓ) :
    EventClose
      (map (fun mines => deployedKeys B initial (deployedOffsets peers mines))
        (uniformOfFintype (Fin k → BitVec 256)))
      (map (fun mines => deployedKeys B other (deployedOffsets peers mines))
        (uniformOfFintype (Fin k → BitVec 256)))
      (k * (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal))) := by
  classical
  let shift : ZMod ℓ → Fin (2 ^ 252) → ZMod ℓ := fun a x => a + castOffset ℓ x
  have hshift : ∀ a, Injective (shift a) := fun a x y hxy =>
    castOffset_injective hN (add_left_cancel hxy)
  let lift : ZMod ℓ → (Fin k → Fin (2 ^ 252)) → (Fin k → ZMod ℓ) := fun a x i => shift a (x i)
  have hlift : ∀ a, Injective (lift a) := fun a x y hxy =>
    funext fun i => hshift a (congrFun hxy i)
  have hkeys : ∀ a, deployedKeys B a = (fun z : Fin k → ZMod ℓ => fun i => (z i).val • B) ∘ lift a := by
    intro a
    funext x i
    simp only [deployedKeys, Function.comp_apply, lift, shift]
    rw [deployedKey_eq_scalar hℓ]
    rfl
  have hc : ∀ a : ZMod ℓ, (fun mines => deployedKeys B a (deployedOffsets peers mines)) =
      deployedKeys B a ∘ deployedOffsets peers := fun a => rfl
  rw [hc, hc, ← map_comp, ← map_comp, deployedOffsets_uniform, hkeys, hkeys, ← map_comp, ← map_comp]
  apply eventClose_map
  apply eventClose_mono (eventClose_injective_bad _ _ (hlift initial) (hlift other))
  -- the bad event: some coordinate misses the other shift's range
  have hsub : {x : Fin k → Fin (2 ^ 252) | lift initial x ∉ Set.range (lift other)} ⊆
      ⋃ i, (fun x : Fin k → Fin (2 ^ 252) => x i) ⁻¹' {r | shift initial r ∉ Set.range (shift other)} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_range] at hnot
    push Not at hnot
    apply hx
    exact ⟨fun i => (hnot i).choose, funext fun i => (hnot i).choose_spec⟩
  have hone : (uniformOfFintype (Fin (2 ^ 252))).toOuterMeasure
      {r | shift initial r ∉ Set.range (shift other)} ≤
        ((ℓ - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal) := by
    have h := prob_bad_le (shift initial) (shift other) (hshift initial) (hshift other)
    rw [ZMod.card, Fintype.card_fin] at h
    exact h
  calc _ ≤ _ := MeasureTheory.measure_mono hsub
    _ ≤ _ := MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin k, ((ℓ - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← toOuterMeasure_map_apply, map_eval_uniform]
        exact hone
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Several

/-! ## Ed25519: `ℓ` is prime, and the numbers -/

/-- `1257559732178653 − 1 = 2² · 3 · 7 · 23 · 531581 · 1224481`. -/
theorem prime_1257559732178653 : Nat.Prime 1257559732178653 :=
  pocklington _ [(531581, 1, 2), (1224481, 1, 2)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl) <;> norm_num)

/-- `4434155615661930479 − 1 = 2 · 41 · 43 · 1257559732178653`. -/
theorem prime_4434155615661930479 : Nat.Prime 4434155615661930479 :=
  pocklington _ [(1257559732178653, 1, 2)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c rfl; exact prime_1257559732178653)

/-- `172054593956031949258510691 − 1 = 2 · 5 · 1361 · 2851 · 4434155615661930479`. -/
theorem prime_172054593956031949258510691 : Nat.Prime 172054593956031949258510691 :=
  pocklington _ [(4434155615661930479, 1, 2)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c rfl; exact prime_4434155615661930479)

/-- `19757330305831588566944191468367130476339 − 1 = 2 · 269 · 213441916511 ·
172054593956031949258510691`. -/
theorem prime_19757330305831588566944191468367130476339 :
    Nat.Prime 19757330305831588566944191468367130476339 :=
  pocklington _ [(172054593956031949258510691, 1, 2)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c rfl
        exact prime_172054593956031949258510691)

/-- `276602624281642239937218680557139826668747 − 1 = 2 · 7 ·
19757330305831588566944191468367130476339`. -/
theorem prime_276602624281642239937218680557139826668747 :
    Nat.Prime 276602624281642239937218680557139826668747 :=
  pocklington _ [(19757330305831588566944191468367130476339, 1, 2)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c rfl
        exact prime_19757330305831588566944191468367130476339)

/-- **`ℓ = 2²⁵² + 27742317777372353535851937790883648493` (the main package's
`Signal.XEdDsaScalar.order`, the Ed25519 group order) is prime.** Pocklington with
`ℓ − 1 = 2² · 3 · 11 · 198211423230930754013084525763697 · 276602624281642239937218680557139826668747`,
certified by the 138-bit factor alone (its square exceeds `ℓ`), base 2. -/
theorem prime_order : Nat.Prime TlsMpc.Signal.XEdDsaScalar.order :=
  pocklington _ [(276602624281642239937218680557139826668747, 1, 2)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c rfl
        exact prime_276602624281642239937218680557139826668747)

instance fact_prime_order : Fact (Nat.Prime TlsMpc.Signal.XEdDsaScalar.order) := ⟨prime_order⟩

instance neZero_order : NeZero TlsMpc.Signal.XEdDsaScalar.order := ⟨prime_order.ne_zero⟩

theorem order_eq : TlsMpc.Signal.XEdDsaScalar.order = 2 ^ 252 + 27742317777372353535851937790883648493 :=
  rfl

theorem two_pow_252_le_order : 2 ^ 252 ≤ TlsMpc.Signal.XEdDsaScalar.order := by
  rw [order_eq]
  exact Nat.le_add_right _ _

/-- `ℓ − 2²⁵² = 27742317777372353535851937790883648493` (about `2^124.4`). -/
theorem order_gap : TlsMpc.Signal.XEdDsaScalar.order - 2 ^ 252 = 27742317777372353535851937790883648493 := by
  rw [order_eq, Nat.add_sub_cancel_left]

theorem frac_lt {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d < b * c) :
    (a : ENNReal) / b < (c : ENNReal) / d := by
  have hb' : (b : ENNReal) ≠ 0 := by exact_mod_cast hb
  have hd' : (d : ENNReal) ≠ 0 := by exact_mod_cast hd
  rw [← ENNReal.mul_div_mul_right (a : ENNReal) (b : ENNReal) hd' (ENNReal.natCast_ne_top d),
    ← ENNReal.mul_div_mul_left (c : ENNReal) (d : ENNReal) hb' (ENNReal.natCast_ne_top b)]
  exact_mod_cast div_lt_div_of_lt (Nat.mul_ne_zero hb hd) h

/-- **`(ℓ − 2²⁵²)/2²⁵² < 2⁻¹²⁷`.** -/
theorem order_gap_lt :
    ((TlsMpc.Signal.XEdDsaScalar.order - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal) <
      1 / ((2 ^ 127 : ℕ) : ENNReal) := by
  rw [← Nat.cast_one]
  apply frac_lt (by positivity) (by positivity)
  rw [order_gap]
  norm_num

/-- **`(ℓ − 2²⁵²)/ℓ ≤ (ℓ − 2²⁵²)/2²⁵²`**, so it is `< 2⁻¹²⁷` too. -/
theorem order_gap_div_order_le :
    ((TlsMpc.Signal.XEdDsaScalar.order - 2 ^ 252 : ℕ) : ENNReal) /
        (TlsMpc.Signal.XEdDsaScalar.order : ENNReal) ≤
      ((TlsMpc.Signal.XEdDsaScalar.order - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal) :=
  ENNReal.div_le_div_left (by exact_mod_cast two_pow_252_le_order) _

/-- **Ed25519, one message, deployed sampling:** for any two initial scalars and every event `s`,
`Pr[key(initial) ∈ s] ≤ Pr[key(other) ∈ s] + 2⁻¹²⁷` (exact bound: `deployed_key_close`).
H-GROUP as "`G` is a finite commutative group of order `ℓ`"; `idealCommit` for the peer value. **M**. -/
theorem ed25519_key_close (hℓ : Fintype.card G = TlsMpc.Signal.XEdDsaScalar.order) (B : G)
    (peer : BitVec 256) (initial other : ZMod TlsMpc.Signal.XEdDsaScalar.order) :
    EventClose
      (map (fun mine => deployedKey B initial (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (map (fun mine => deployedKey B other (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (1 / ((2 ^ 127 : ℕ) : ENNReal)) :=
  eventClose_mono (deployed_key_close hℓ two_pow_252_le_order B peer initial other) order_gap_lt.le

/-- **Ed25519, one message: the deployed key is within `2⁻¹²⁷` (total variation) of uniform on
`G`** for `B ≠ 0` (`ℓ` prime is proved). **M**. -/
theorem ed25519_key_close_uniform (hℓ : Fintype.card G = TlsMpc.Signal.XEdDsaScalar.order) (B : G)
    (hB : B ≠ 0) (peer : BitVec 256) (initial : ZMod TlsMpc.Signal.XEdDsaScalar.order) :
    StatClose
      (map (fun mine => deployedKey B initial (deployedOffset mine peer)) (uniformOfFintype (BitVec 256)))
      (uniformOfFintype G) (1 / ((2 ^ 127 : ℕ) : ENNReal)) := by
  have h := deployed_key_close_uniform hℓ two_pow_252_le_order B hB peer initial
  have hle := order_gap_div_order_le.trans order_gap_lt.le
  exact ⟨eventClose_mono h.1 hle, eventClose_mono h.2 hle⟩

/-- **Ed25519, `k` messages of one conversation, deployed sampling:** every event's probability
for the joint keys differs between any two initial scalars by at most `k·2⁻¹²⁷`. **M**. -/
theorem ed25519_keys_close {k : ℕ} (hℓ : Fintype.card G = TlsMpc.Signal.XEdDsaScalar.order) (B : G)
    (peers : Fin k → BitVec 256) (initial other : ZMod TlsMpc.Signal.XEdDsaScalar.order) :
    EventClose
      (map (fun mines => deployedKeys B initial (deployedOffsets peers mines))
        (uniformOfFintype (Fin k → BitVec 256)))
      (map (fun mines => deployedKeys B other (deployedOffsets peers mines))
        (uniformOfFintype (Fin k → BitVec 256)))
      (k * (1 / ((2 ^ 127 : ℕ) : ENNReal))) :=
  eventClose_mono (deployed_keys_close hℓ two_pow_252_le_order B peers initial other)
    (mul_le_mul_right order_gap_lt.le _)

end TlsMpcProofs.OffsetSampling
