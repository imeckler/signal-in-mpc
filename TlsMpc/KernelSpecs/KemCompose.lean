import TlsMpc.KernelSpecs.KemSample

/-!
# KEM kernels: the six stages together are Kyber-1024 encapsulation

The kernels `kem-hash`, `kem-ntt`, `kem-matrix 0..3`, `kem-u 0..3`, `kem-v`, `kem-finish`
(`TlsMpc/MlKemFastKernels.lean`) compute, on values, the stage functions of
`TlsMpc/Signal/MlKemFast.lean` (`kemHash_spec` … `kemFinish_spec` in `MlKemFastProofs`).
`pipeline` wires those stage functions by name exactly as the worker wires the kernels
(`kernels_compose` restates this on `Kernel.values`). Against the repository's specification
`Signal.MlKem.encapsulate … 4 2 11 5 224` (rank 4, η = 2, d_u = 11, d_v = 5, 224 byte-triples
of matrix budget; `kyber := true` is round-3 Kyber as libsignal key type 8):

* `pipeline_valid`: for a key whose 1024 encoded coefficients are all below q (`KeyValid`),
  the kernels' three outputs (status, ciphertext, secret) are the specification's success
  byte and its output bytes, each gated by the success byte (as `MlKem.run` gates them).
  In particular when the specification succeeds the status is 255 and the ciphertext and
  secret are exactly the specification's (`pipeline_valid_accept`), and otherwise (matrix
  sampling exhausted its budget) everything is zero (`pipeline_valid_reject`). Holds for both
  variants (`kyber`; for `kyber := false` the two entropy inputs must be 32 bytes).
* `kernels_compose`: the same on the kernels' `Kernel.values`, when each kernel's named inputs
  carry the named outputs of the earlier kernels.
* `pipeline_invalid`: for any other key every output byte is zero (the kernels refuse;
  the specification itself has no such check and would encapsulate anyway).

What `MlKem.encapsulate` itself is checked against is NOT a theorem here: it is compared with
the pinned libcrux on test vectors by `scripts/check_lean_signal_mlkem.py` and, through the
kernels, by `handshake_backend/EmpHybridWork/check_kem_kernels.py`. No FIPS 203 transcription
theorem exists.
-/
namespace TlsMpc.KernelSpecs.KemCompose
open TlsMpc.Signal

local notation "FO" => MlKemFast.concrete
local notation "BA" => ByteAuth.concrete
local notation "KC" => Keccak.concrete
local notation "SH" => Sha256.concrete
local notation "AR" => MlKemArithmetic.concrete
local notation "EN" => MlKemEncoding.concrete
local notation "WO" => Word64.concrete

/-! ### Lengths -/

theorem forward_length (p : List (BitVec 12)) : (MlKemFast.forward FO p).length = 256 := by
  rw [MlKemFast.forward, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp [MlKemFast.forwardLayer]

theorem inverse_length (p : List (BitVec 12)) : (MlKemFast.inverse FO p).length = 256 := by
  rw [MlKemFast.inverse, List.length_map, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp [MlKemFast.inverseLayer]

theorem add_length (x y : List (BitVec 12)) : (MlKemFast.add FO x y).length = min x.length y.length := by
  simp [MlKemFast.add]

/-! ### Validity of the key -/

/-- Every encoded coefficient of the key's four polynomials is below q (FIPS 203 §7.2). -/
def KeyValid (key : List (BitVec 8)) : Prop :=
  ∀ i, i < 4 → ∀ x ∈ MlKemPke.decode SH BA 4 key i, x.toNat < 3329

theorem specDecode_eq (key : List (BitVec 8)) (i : Nat) :
    MlKemPke.decode SH BA 4 key i = (MlKemFast.polyAt FO key (i % 4)).map MlKemFast.wide := by
  simp only [MlKemPke.decode, MlKemFast.polyAt, KemEncoding.decode12_refines]

theorem polyAt_canon (key : List (BitVec 8)) (h : KeyValid key) (i : Nat) :
    MlKemFast.Canon (MlKemFast.polyAt FO key (i % 4)) := by
  intro x hx
  have := h (i % 4) (Nat.mod_lt _ (by decide)) (MlKemFast.wide x) (by
    rw [specDecode_eq, Nat.mod_mod]; exact List.mem_map_of_mem hx)
  rwa [MlKemFast.wide_toNat] at this

theorem big_getElem? (key : List (BitVec 8)) (i m : Nat) (hi : i < 4) (hm : m < 256) :
    (MlKemFast.decode12 FO 1024 (key.take 1536))[256 * i + m]? = (MlKemFast.polyAt FO key i)[m]? := by
  simp only [MlKemFast.polyAt, MlKemFast.decode12, List.getElem?_map, List.getElem?_range (show 256 * i + m < 1024 by omega),
    List.getElem?_range hm, Option.map_some]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [KemEncoding.decode12_coeff_getLsbD, KemEncoding.decode12_coeff_getLsbD]
  by_cases h12 : j < 12
  · simp only [h12, decide_true, Bool.true_and, KemEncoding.bitAt]
    have e1 : (12 * (256 * i + m) + j) / 8 = 384 * i + (12 * m + j) / 8 := by omega
    have e2 : (12 * (256 * i + m) + j) % 8 = (12 * m + j) % 8 := by omega
    rw [e1, e2, List.getElem?_take, if_pos (by omega), List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  · simp [h12]

theorem big_mem (key : List (BitVec 8)) (x : BitVec 12) :
    x ∈ MlKemFast.decode12 FO 1024 (key.take 1536) ↔ ∃ i, i < 4 ∧ x ∈ MlKemFast.polyAt FO key i := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hx
    have hlt : n < 1024 := by
      rcases Nat.lt_or_ge n 1024 with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [KemEncoding.decode12_length]; exact h)] at hn; exact absurd hn (by simp)
    refine ⟨n / 256, by omega, List.mem_iff_getElem?.mpr ⟨n % 256, ?_⟩⟩
    rw [← big_getElem? key (n / 256) (n % 256) (by omega) (by omega), show 256 * (n / 256) + n % 256 = n by omega, hn]
  · intro ⟨i, hi, hx⟩
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hx
    have hlt : m < 256 := by
      rcases Nat.lt_or_ge m 256 with h | h
      · exact h
      · rw [List.getElem?_eq_none (by simp [MlKemFast.polyAt, KemEncoding.decode12_length]; exact h)] at hm
        exact absurd hm (by simp)
    exact List.mem_iff_getElem?.mpr ⟨256 * i + m, by rw [big_getElem? key i m hi hlt, hm]⟩

theorem and1_eq : ∀ x y : BitVec 1, MlKemFast.concrete.and x y = if x = 1#1 ∧ y = 1#1 then 1#1 else 0#1 := by
  decide

theorem foldl_and1 : ∀ (l : List (BitVec 1)) (acc : BitVec 1),
    l.foldl MlKemFast.concrete.and acc = if acc = 1#1 ∧ ∀ b ∈ l, b = 1#1 then 1#1 else 0#1
  | [], acc => by rcases KemSample.bv1 acc with rfl | rfl <;> decide
  | b :: l, acc => by
      rw [List.foldl_cons, foldl_and1 l, and1_eq]
      have h01 : ¬ (0#1 : BitVec 1) = 1#1 := by decide
      by_cases ha : acc = 1#1 <;> by_cases hb : b = 1#1 <;> simp [ha, hb, h01]

theorem allBelow_value (poly : List (BitVec 12)) :
    MlKemFast.allBelow FO poly = if ∀ x ∈ poly, x.toNat < 3329 then 1#1 else 0#1 := by
  rw [MlKemFast.allBelow, foldl_and1]
  have hone : MlKemFast.concrete.one = 1#1 := rfl
  rw [hone]
  have iff : (∀ b ∈ poly.map MlKemFast.concrete.ltQ, b = 1#1) ↔ ∀ x ∈ poly, x.toNat < 3329 := by
    rw [List.forall_mem_map]
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro _
    rw [KemSample.ltQ_value]
    by_cases h : x.toNat < 3329
    · simp [KemSample.accB, h]
    · simp [KemSample.accB, h]
  by_cases h : ∀ x ∈ poly, x.toNat < 3329
  · rw [if_pos ⟨rfl, iff.mpr h⟩, if_pos h]
  · rw [if_neg (fun c => h (iff.mp c.2)), if_neg h]

theorem keyValid_iff (key : List (BitVec 8)) :
    (∀ x ∈ MlKemFast.decode12 FO 1024 (key.take 1536), x.toNat < 3329) ↔ KeyValid key := by
  constructor
  · intro h i hi x hx
    rw [specDecode_eq, Nat.mod_eq_of_lt hi] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [MlKemFast.wide_toNat]
    exact h y ((big_mem key y).mpr ⟨i, hi, hy⟩)
  · intro h x hx
    obtain ⟨i, hi, hxi⟩ := (big_mem key x).mp hx
    have := polyAt_canon key h i
    rw [Nat.mod_eq_of_lt hi] at this
    exact this x hxi

/-- The `keyValid` byte of `kem-hash` is 255 for a valid key … -/
theorem keyValid_byte_valid (key : List (BitVec 8)) (h : KeyValid key) :
    MlKemFast.maskByte FO (MlKemFast.allBelow FO (MlKemFast.decode12 FO 1024 (key.take 1536))) = 255 := by
  rw [allBelow_value, KemSample.maskByte_value, if_pos ((keyValid_iff key).mpr h), if_pos rfl]

/-- … and 0 for any other key. -/
theorem keyValid_byte_invalid (key : List (BitVec 8)) (h : ¬ KeyValid key) :
    MlKemFast.maskByte FO (MlKemFast.allBelow FO (MlKemFast.decode12 FO 1024 (key.take 1536))) = 0 := by
  rw [allBelow_value, KemSample.maskByte_value, if_neg (fun c => h ((keyValid_iff key).mp c)), if_neg (by decide)]

/-! ### The polynomials -/

theorem dot_congr (rank : Nat) (l l' r r' : Nat → List (BitVec 12))
    (h : ∀ j, j < rank → l j = l' j ∧ r j = r' j) :
    MlKemFast.dot FO rank l r = MlKemFast.dot FO rank l' r' := by
  have hmap : (List.range rank).map (fun j => MlKemFast.baseMultiply FO (l j) (r j)) =
      (List.range rank).map (fun j => MlKemFast.baseMultiply FO (l' j) (r' j)) :=
    List.map_congr_left (fun j hj => by rw [List.mem_range] at hj; rw [(h j hj).1, (h j hj).2])
  unfold MlKemFast.dot
  rw [hmap]

theorem specDot_congr (rank : Nat) (l l' r r' : Nat → List (BitVec 32))
    (h : ∀ j, j < rank → l j = l' j ∧ r j = r' j) :
    MlKemPke.dot AR SH rank l r = MlKemPke.dot AR SH rank l' r' := by
  have hmap : (List.range rank).map (fun j => MlKemNtt.baseMultiply AR SH (l j) (r j)) =
      (List.range rank).map (fun j => MlKemNtt.baseMultiply AR SH (l' j) (r' j)) :=
    List.map_congr_left (fun j hj => by rw [List.mem_range] at hj; rw [(h j hj).1, (h j hj).2])
  unfold MlKemPke.dot
  rw [hmap]

/-- The kernels' NTT of secret polynomial `j`. -/
def kHat (coins : List (BitVec 8)) (j : Nat) : List (BitVec 12) := MlKemFast.forward FO (MlKemFast.noise FO BA KC coins j)
/-- The specification's. -/
def sHat (coins : List (BitVec 8)) (j : Nat) : List (BitVec 32) :=
  MlKemNtt.forward AR SH (MlKemPke.noise AR SH BA KC 2 coins j)

theorem kHat_refines (coins : List (BitVec 8)) (j : Nat) :
    (kHat coins j).map MlKemFast.wide = sHat coins j ∧ MlKemFast.Canon (kHat coins j) := by
  have r := MlKemFast.forward_refines _ (KemEncoding.noise_canon coins j)
  rw [KemEncoding.noise_refines] at r
  exact r

theorem polyAt_rhat (coins : List (BitVec 8)) (j : Nat) (hj : j < 4) :
    MlKemFast.polyAt FO (MlKemFast.nttStage FO BA KC coins) j = kHat coins j :=
  KemEncoding.polyAt_flatMap_encode (kHat coins) (fun _ => forward_length _) j hj

/-- The kernels' matrix entry `(i, j)` (row `i` of the transposed matrix). -/
def kEntry (key : List (BitVec 8)) (i j : Nat) : List (BitVec 12) :=
  (MlKemFast.entry FO KC (((key.drop 1536).take 32) ++ [ByteAuth.concrete.const i, ByteAuth.concrete.const j])).2

/-- The specification's matrix (transposed, as encryption uses it). -/
def sMat (key : List (BitVec 8)) : MlKemPke.Matrix (BitVec 8) (BitVec 32) :=
  MlKemPke.matrix SH BA WO KC 4 224 true ((key.drop 1536).take 32)

theorem polyAt_row (key : List (BitVec 8)) (i j : Nat) (hj : j < 4) :
    MlKemFast.polyAt FO ((MlKemFast.matrixStage FO BA KC i key).getD 0 []) j = kEntry key i j := by
  simp only [MlKemFast.matrixStage, List.getD_cons_zero, List.flatMap_map]
  exact KemEncoding.polyAt_flatMap_encode (kEntry key i) (fun _ => KemSample.entry_length _) j hj

theorem sMat_entry (key : List (BitVec 8)) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    (sMat key).entries i j = (kEntry key i j).map MlKemFast.wide := by
  have h16 : i * 4 + j < 4 * 4 := by omega
  unfold sMat MlKemPke.matrix
  dsimp only
  rw [List.getElem?_map, List.getElem?_range h16, Option.map_some, Option.getD_some, if_pos rfl,
    show (i * 4 + j) / 4 = i by omega, show (i * 4 + j) % 4 = j by omega]
  exact KemSample.entry_refines _

/-- The kernels' polynomial `u_i` before compression. -/
def kU (key coins : List (BitVec 8)) (i : Nat) : List (BitVec 12) :=
  MlKemFast.add FO (MlKemFast.inverse FO (MlKemFast.dot FO 4
    (MlKemFast.polyAt FO ((MlKemFast.matrixStage FO BA KC i key).getD 0 []))
    (MlKemFast.polyAt FO (MlKemFast.nttStage FO BA KC coins)))) (MlKemFast.noise FO BA KC coins (4 + i))

/-- The specification's. -/
def sU (key coins : List (BitVec 8)) (i : Nat) : List (BitVec 32) :=
  MlKemPke.add AR SH (MlKemNtt.inverse AR SH (MlKemPke.dot AR SH 4 ((sMat key).entries i) (sHat coins)))
    (MlKemPke.noise AR SH BA KC 2 coins (4 + i))

theorem kU_refines (key coins : List (BitVec 8)) (i : Nat) (hi : i < 4) :
    (kU key coins i).map MlKemFast.wide = sU key coins i ∧ MlKemFast.Canon (kU key coins i) ∧
      (kU key coins i).length = 256 := by
  have congr1 : MlKemFast.dot FO 4 (MlKemFast.polyAt FO ((MlKemFast.matrixStage FO BA KC i key).getD 0 []))
      (MlKemFast.polyAt FO (MlKemFast.nttStage FO BA KC coins)) = MlKemFast.dot FO 4 (kEntry key i) (kHat coins) :=
    dot_congr 4 _ _ _ _ (fun j hj => ⟨polyAt_row key i j hj, polyAt_rhat coins j hj⟩)
  obtain ⟨d1, d2⟩ := MlKemFast.dot_refines 4 (kEntry key i) (kHat coins)
    (fun j => KemSample.entry_canon _) (fun j => (kHat_refines coins j).2)
  have d1' : (MlKemFast.dot FO 4 (kEntry key i) (kHat coins)).map MlKemFast.wide =
      MlKemPke.dot AR SH 4 ((sMat key).entries i) (sHat coins) := by
    rw [d1]
    exact specDot_congr 4 _ _ _ _ (fun j hj => ⟨(sMat_entry key i j hi hj).symm, (kHat_refines coins j).1⟩)
  obtain ⟨n1, n2⟩ := MlKemFast.inverse_refines _ d2
  obtain ⟨a1, a2⟩ := MlKemFast.add_refines _ _ n2 (KemEncoding.noise_canon coins (4 + i))
  refine ⟨?_, ?_, ?_⟩
  · simp only [kU, congr1]
    rw [a1, n1, d1', KemEncoding.noise_refines]
    rfl
  · simp only [kU, congr1]; exact a2
  · simp only [kU, add_length, inverse_length, KemEncoding.noise_length, Nat.min_self]

/-- The kernels' polynomial `v` before compression. -/
def kV (key coins message : List (BitVec 8)) : List (BitVec 12) :=
  MlKemFast.add FO (MlKemFast.add FO (MlKemFast.inverse FO (MlKemFast.dot FO 4 (MlKemFast.polyAt FO key)
    (MlKemFast.polyAt FO (MlKemFast.nttStage FO BA KC coins)))) (MlKemFast.noise FO BA KC coins 8))
    (MlKemFast.messagePoly FO message)

/-- The specification's. -/
def sV (key coins message : List (BitVec 8)) : List (BitVec 32) :=
  MlKemPke.add AR SH (MlKemPke.add AR SH (MlKemNtt.inverse AR SH (MlKemPke.dot AR SH 4 (MlKemPke.decode SH BA 4 key)
    (sHat coins))) (MlKemPke.noise AR SH BA KC 2 coins (2 * 4)))
    ((MlKemEncoding.decode SH BA 1 256 message).map (MlKemEncoding.decompress AR SH 1))

theorem kV_refines (key coins message : List (BitVec 8)) (hvalid : KeyValid key) (hm : message.length = 32) :
    (kV key coins message).map MlKemFast.wide = sV key coins message ∧ MlKemFast.Canon (kV key coins message) ∧
      (kV key coins message).length = 256 := by
  have congr1 : MlKemFast.dot FO 4 (MlKemFast.polyAt FO key) (MlKemFast.polyAt FO (MlKemFast.nttStage FO BA KC coins)) =
      MlKemFast.dot FO 4 (fun j => MlKemFast.polyAt FO key (j % 4)) (kHat coins) :=
    dot_congr 4 _ _ _ _ (fun j hj => ⟨by rw [Nat.mod_eq_of_lt hj], polyAt_rhat coins j hj⟩)
  obtain ⟨d1, d2⟩ := MlKemFast.dot_refines 4 (fun j => MlKemFast.polyAt FO key (j % 4)) (kHat coins)
    (fun j => polyAt_canon key hvalid j) (fun j => (kHat_refines coins j).2)
  have d1' : (MlKemFast.dot FO 4 (fun j => MlKemFast.polyAt FO key (j % 4)) (kHat coins)).map MlKemFast.wide =
      MlKemPke.dot AR SH 4 (MlKemPke.decode SH BA 4 key) (sHat coins) := by
    rw [d1]
    exact specDot_congr 4 _ _ _ _ (fun j _ => ⟨(specDecode_eq key j).symm, (kHat_refines coins j).1⟩)
  obtain ⟨n1, n2⟩ := MlKemFast.inverse_refines _ d2
  obtain ⟨a1, a2⟩ := MlKemFast.add_refines _ _ n2 (KemEncoding.noise_canon coins 8)
  obtain ⟨b1, b2⟩ := MlKemFast.add_refines _ _ a2 (KemEncoding.messagePoly_canon message)
  refine ⟨?_, ?_, ?_⟩
  · simp only [kV, congr1]
    rw [b1, a1, n1, d1', KemEncoding.noise_refines, KemEncoding.messagePoly_refines message hm]
    rfl
  · simp only [kV, congr1]; exact b2
  · simp only [kV, add_length, inverse_length, KemEncoding.noise_length, KemEncoding.messagePoly_length, hm]
    rfl

/-! ### The ciphertext -/

theorem u_bytes (key coins : List (BitVec 8)) (i : Nat) (hi : i < 4) :
    MlKemFast.uStage FO BA KC i ((MlKemFast.matrixStage FO BA KC i key).getD 0 []) (MlKemFast.nttStage FO BA KC coins)
        coins = MlKemEncoding.encode SH BA 11 256 ((sU key coins i).map (MlKemEncoding.compress AR EN SH 11)) := by
  obtain ⟨r1, r2, r3⟩ := kU_refines key coins i hi
  show MlKemFast.encode FO 11 ((kU key coins i).map (MlKemFast.concrete.compress 11)) = _
  rw [KemEncoding.encode_refines 11 256 _ (by rw [List.length_map, r3]) (by decide) (by decide) (by decide),
    List.map_map, ← r1, List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro x hx
  exact MlKemFast.wide_compress11 x (r2 x hx)

theorem v_bytes (key coins message : List (BitVec 8)) (hvalid : KeyValid key) (hm : message.length = 32) :
    MlKemFast.vStage FO BA KC key (MlKemFast.nttStage FO BA KC coins) coins message =
      MlKemEncoding.encode SH BA 5 256 ((sV key coins message).map (MlKemEncoding.compress AR EN SH 5)) := by
  obtain ⟨r1, r2, r3⟩ := kV_refines key coins message hvalid hm
  show MlKemFast.encode FO 5 ((kV key coins message).map (MlKemFast.concrete.compress 5)) = _
  rw [KemEncoding.encode_refines 5 256 _ (by rw [List.length_map, r3]) (by decide) (by decide) (by decide),
    List.map_map, ← r1, List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro x hx
  exact MlKemFast.wide_compress5 x (r2 x hx)

theorem encrypt_bytes (key message coins : List (BitVec 8)) :
    (MlKemPke.encrypt AR EN SH BA WO KC 4 2 11 5 224 key message coins).bytes =
      (List.range 4).flatMap (fun i => MlKemEncoding.encode SH BA 11 256 ((sU key coins i).map (MlKemEncoding.compress AR EN SH 11))) ++
        MlKemEncoding.encode SH BA 5 256 ((sV key coins message).map (MlKemEncoding.compress AR EN SH 5)) := rfl

theorem encrypt_length (key message coins : List (BitVec 8)) :
    (MlKemPke.encrypt AR EN SH BA WO KC 4 2 11 5 224 key message coins).bytes.length = 1568 := by
  rw [encrypt_bytes, List.length_append,
    KemEncoding.flatMap_range_length _ 352 (fun _ => by rw [MlKemEncoding.encode_length]) 4,
    MlKemEncoding.encode_length]

theorem range4_flatMap {α : Type} (f : Nat → List α) : (List.range 4).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ (f 3 ++ []))) :=
  rfl

/-- The kernels' ciphertext (`u0 ‖ u1 ‖ u2 ‖ u3 ‖ v`) is the specification's encryption, on a valid key. -/
theorem ct_eq (key coins message : List (BitVec 8)) (hvalid : KeyValid key) (hm : message.length = 32) :
    MlKemFast.uStage FO BA KC 0 ((MlKemFast.matrixStage FO BA KC 0 key).getD 0 []) (MlKemFast.nttStage FO BA KC coins) coins ++
      MlKemFast.uStage FO BA KC 1 ((MlKemFast.matrixStage FO BA KC 1 key).getD 0 []) (MlKemFast.nttStage FO BA KC coins) coins ++
      MlKemFast.uStage FO BA KC 2 ((MlKemFast.matrixStage FO BA KC 2 key).getD 0 []) (MlKemFast.nttStage FO BA KC coins) coins ++
      MlKemFast.uStage FO BA KC 3 ((MlKemFast.matrixStage FO BA KC 3 key).getD 0 []) (MlKemFast.nttStage FO BA KC coins) coins ++
      MlKemFast.vStage FO BA KC key (MlKemFast.nttStage FO BA KC coins) coins message =
    (MlKemPke.encrypt AR EN SH BA WO KC 4 2 11 5 224 key message coins).bytes := by
  rw [encrypt_bytes, range4_flatMap, u_bytes key coins 0 (by decide), u_bytes key coins 1 (by decide),
    u_bytes key coins 2 (by decide), u_bytes key coins 3 (by decide), v_bytes key coins message hvalid hm]
  simp only [List.append_assoc, List.append_nil]

/-! ### The status -/

theorem and8_eq (x y : BitVec 8) (hx : x = 0 ∨ x = 255) (hy : y = 0 ∨ y = 255) :
    ByteAuth.concrete.and x y = if x = 255 ∧ y = 255 then 255 else 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem foldl_and8 : ∀ (l : List (BitVec 8)) (acc : BitVec 8), (∀ b ∈ l, b = 0 ∨ b = 255) → (acc = 0 ∨ acc = 255) →
    l.foldl ByteAuth.concrete.and acc = if acc = 255 ∧ ∀ b ∈ l, b = 255 then 255 else 0
  | [], acc, _, hacc => by rcases hacc with rfl | rfl <;> decide
  | b :: l, acc, hl, hacc => by
      have hb := hl b (List.mem_cons_self ..)
      have hab : ByteAuth.concrete.and acc b = 0 ∨ ByteAuth.concrete.and acc b = 255 := by
        rw [and8_eq acc b hacc hb]; split
        · exact Or.inr rfl
        · exact Or.inl rfl
      rw [List.foldl_cons, foldl_and8 l _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hab, and8_eq acc b hacc hb]
      rcases hacc with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem maskByte_cases (t : BitVec 1) : MlKemFast.maskByte FO t = 0 ∨ MlKemFast.maskByte FO t = 255 := by
  rcases KemSample.bv1 t with rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)

/-- Whether entry `(i, j)` found 256 coefficients in its four SHAKE128 blocks. -/
abbrev EntryOk (key : List (BitVec 8)) (i j : Nat) : Prop :=
  (MlKemFast.entry FO KC (((key.drop 1536).take 32) ++ [ByteAuth.concrete.const i, ByteAuth.concrete.const j])).1 = 1#1

open Classical in
theorem ok_byte (key : List (BitVec 8)) (i : Nat) :
    (MlKemFast.matrixStage FO BA KC i key).getD 1 [] = [if ∀ j, j < 4 → EntryOk key i j then 255 else 0] := by
  show [MlKemFast.maskByte FO ((((List.range 4).map (fun j => MlKemFast.entry FO KC
      (((key.drop 1536).take 32) ++ [ByteAuth.concrete.const i, ByteAuth.concrete.const j]))).map (·.1)).foldl
        MlKemFast.concrete.and MlKemFast.concrete.one)] = _
  rw [List.map_map, foldl_and1]
  have iff : (∀ b ∈ (List.range 4).map ((fun e => e.1) ∘ fun j => MlKemFast.entry FO KC
      (((key.drop 1536).take 32) ++ [ByteAuth.concrete.const i, ByteAuth.concrete.const j])), b = 1#1) ↔
      ∀ j, j < 4 → EntryOk key i j := by
    rw [List.forall_mem_map]
    simp only [List.mem_range, Function.comp_apply, EntryOk]
  by_cases h : ∀ j, j < 4 → EntryOk key i j
  · rw [if_pos (show MlKemFast.concrete.one = 1#1 ∧ _ from ⟨rfl, iff.mpr h⟩), if_pos h]
    decide
  · rw [if_neg (fun c => h (iff.mp c.2)), if_neg h]
    decide

theorem matrix_success (rho : List (BitVec 8)) :
    (MlKemPke.matrix SH BA WO KC 4 224 true rho).success =
      ((List.range 16).map (fun n => OpenResult.get BA (MlKemSample.matrix WO BA KC 256 224
        (rho ++ [ByteAuth.concrete.const (n / 4), ByteAuth.concrete.const (n % 4)])) 0)).foldl
          ByteAuth.concrete.and (ByteAuth.concrete.const 255) := by
  rw [List.foldl_map]
  rfl

open Classical in
theorem spec_success (key : List (BitVec 8)) :
    (sMat key).success = if ∀ n, n < 16 → EntryOk key (n / 4) (n % 4) then 255 else 0 := by
  have hcases : ∀ b ∈ (List.range 16).map (fun n => OpenResult.get BA (MlKemSample.matrix WO BA KC 256 224
      (((key.drop 1536).take 32) ++ [ByteAuth.concrete.const (n / 4), ByteAuth.concrete.const (n % 4)])) 0),
      b = 0 ∨ b = 255 := by
    intro b hb
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hb
    rw [KemSample.entry_status]
    exact maskByte_cases _
  rw [sMat, matrix_success, foldl_and8 _ (ByteAuth.concrete.const 255) hcases (Or.inr rfl)]
  by_cases hc : ∀ n, n < 16 → EntryOk key (n / 4) (n % 4)
  · rw [if_pos hc, if_pos]
    refine ⟨rfl, ?_⟩
    intro b hb
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hb
    rw [KemSample.entry_status, KemSample.maskByte_value, if_pos (hc n (List.mem_range.mp hn))]
  · rw [if_neg hc, if_neg]
    intro ⟨_, hall⟩
    apply hc
    intro n hn
    have := hall _ (List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩)
    rw [KemSample.entry_status, KemSample.maskByte_value] at this
    exact Classical.byContradiction fun hne => by
      rw [if_neg hne] at this
      exact absurd this (by decide)

theorem eqMask_ite (c : Prop) [Decidable c] :
    ByteAuth.eqMask BA (if c then (255 : BitVec 8) else 0) (ByteAuth.concrete.const 255) = if c then 255 else 0 := by
  rw [ByteAuth.eqMask_value]
  by_cases h : c
  · rw [if_pos h]; exact if_pos rfl
  · rw [if_neg h, if_neg (by decide)]

open Classical in
/-- The status `kem-finish` computes from `ok0..ok3` and `keyValid` is the specification's success byte,
on a valid key. -/
theorem kernel_status (key : List (BitVec 8)) (hvalid : KeyValid key) :
    ByteAuth.eqMask BA ((((MlKemFast.matrixStage FO BA KC 0 key).getD 1 [] ++ (MlKemFast.matrixStage FO BA KC 1 key).getD 1 [] ++
      (MlKemFast.matrixStage FO BA KC 2 key).getD 1 [] ++ (MlKemFast.matrixStage FO BA KC 3 key).getD 1 []) ++
      [MlKemFast.maskByte FO (MlKemFast.allBelow FO (MlKemFast.decode12 FO 1024 (key.take 1536)))]).foldl
        ByteAuth.concrete.and (ByteAuth.concrete.const 255)) (ByteAuth.concrete.const 255) =
    (sMat key).success := by
  rw [spec_success, ok_byte, ok_byte, ok_byte, ok_byte, keyValid_byte_valid key hvalid]
  have hcases : ∀ b ∈ ([if ∀ j, j < 4 → EntryOk key 0 j then (255 : BitVec 8) else 0] ++
      [if ∀ j, j < 4 → EntryOk key 1 j then (255 : BitVec 8) else 0] ++
      [if ∀ j, j < 4 → EntryOk key 2 j then (255 : BitVec 8) else 0] ++
      [if ∀ j, j < 4 → EntryOk key 3 j then (255 : BitVec 8) else 0]) ++ [255], b = 0 ∨ b = 255 := by
    intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (((rfl | rfl) | rfl) | rfl) | rfl
    all_goals first
      | exact Or.inr rfl
      | (split
         · exact Or.inr rfl
         · exact Or.inl rfl)
  rw [foldl_and8 _ (ByteAuth.concrete.const 255) hcases (Or.inr rfl), eqMask_ite]
  by_cases hc : ∀ n, n < 16 → EntryOk key (n / 4) (n % 4)
  · have row : ∀ i, i < 4 → ∀ j, j < 4 → EntryOk key i j := by
      intro i hi j hj
      have := hc (4 * i + j) (by omega)
      rwa [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at this
    rw [if_pos hc, if_pos]
    refine ⟨rfl, ?_⟩
    intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (((rfl | rfl) | rfl) | rfl) | rfl
    · exact if_pos (row 0 (by decide))
    · exact if_pos (row 1 (by decide))
    · exact if_pos (row 2 (by decide))
    · exact if_pos (row 3 (by decide))
    · rfl
  · obtain ⟨n, hn, hbad⟩ : ∃ n, n < 16 ∧ ¬ EntryOk key (n / 4) (n % 4) :=
      Classical.byContradiction fun hne => hc fun n hn =>
        Classical.byContradiction fun h' => hne ⟨n, hn, h'⟩
    have hrow : ¬ ∀ j, j < 4 → EntryOk key (n / 4) j := fun h => hbad (h (n % 4) (by omega))
    have zero_mem : (0 : BitVec 8) ∈ ([if ∀ j, j < 4 → EntryOk key 0 j then (255 : BitVec 8) else 0] ++
        [if ∀ j, j < 4 → EntryOk key 1 j then (255 : BitVec 8) else 0] ++
        [if ∀ j, j < 4 → EntryOk key 2 j then (255 : BitVec 8) else 0] ++
        [if ∀ j, j < 4 → EntryOk key 3 j then (255 : BitVec 8) else 0]) ++ [255] := by
      have hq : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 := by omega
      simp only [List.mem_append, List.mem_singleton]
      rcases hq with hq | hq | hq | hq <;> rw [hq] at hrow
      · exact Or.inl (Or.inl (Or.inl (Or.inl (if_neg hrow).symm)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (if_neg hrow).symm)))
      · exact Or.inl (Or.inl (Or.inr (if_neg hrow).symm))
      · exact Or.inl (Or.inr (if_neg hrow).symm)
    rw [if_neg hc, if_neg]
    intro c
    exact absurd (c.2 0 zero_mem) (by decide)

/-! ### The six stages together -/

/-- The six kernel stages on values, wired by name as the worker wires the kernels: `kem-hash`, `kem-ntt`,
`kem-matrix 0..3`, `kem-u 0..3`, `kem-v`, `kem-finish`. Output: `kemStatus`, `kemCiphertext`, `kemSecret`. -/
def pipeline (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) : List (List (BitVec 8)) :=
  let h := MlKemFast.hashStage FO BA KC kyber key entropyA entropyB
  let rhat := MlKemFast.nttStage FO BA KC (h.getD 2 [])
  let row := fun i => (MlKemFast.matrixStage FO BA KC i key).getD 0 []
  let ok := fun i => (MlKemFast.matrixStage FO BA KC i key).getD 1 []
  let u := fun i => MlKemFast.uStage FO BA KC i (row i) rhat (h.getD 2 [])
  let v := MlKemFast.vStage FO BA KC key rhat (h.getD 2 []) (h.getD 0 [])
  MlKemFast.finishStage BA KC kyber (u 0 ++ u 1 ++ u 2 ++ u 3 ++ v) (h.getD 1 []) (ok 0 ++ ok 1 ++ ok 2 ++ ok 3 ++ h.getD 3 [])

/-- The specification: `Signal.MlKem.encapsulate` with Kyber-1024's parameters, on the XOR of the two
parties' entropy. -/
def specEnc (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) : MlKemPke.Ciphertext (BitVec 8) :=
  MlKem.encapsulate AR EN SH BA WO KC 4 2 11 5 224 kyber key (List.zipWith ByteAuth.concrete.xor entropyA entropyB)

theorem hash_getD0 (kyber : Bool) (key eA eB : List (BitVec 8)) :
    (MlKemFast.hashStage FO BA KC kyber key eA eB).getD 0 [] =
      (if kyber then Keccak.sha3_256 KC (List.zipWith ByteAuth.concrete.xor eA eB) else List.zipWith ByteAuth.concrete.xor eA eB) := rfl
theorem hash_getD1 (kyber : Bool) (key eA eB : List (BitVec 8)) :
    (MlKemFast.hashStage FO BA KC kyber key eA eB).getD 1 [] =
      (Keccak.sha3_512 KC ((if kyber then Keccak.sha3_256 KC (List.zipWith ByteAuth.concrete.xor eA eB)
        else List.zipWith ByteAuth.concrete.xor eA eB) ++ Keccak.sha3_256 KC key)).take 32 := rfl
theorem hash_getD2 (kyber : Bool) (key eA eB : List (BitVec 8)) :
    (MlKemFast.hashStage FO BA KC kyber key eA eB).getD 2 [] =
      (Keccak.sha3_512 KC ((if kyber then Keccak.sha3_256 KC (List.zipWith ByteAuth.concrete.xor eA eB)
        else List.zipWith ByteAuth.concrete.xor eA eB) ++ Keccak.sha3_256 KC key)).drop 32 := rfl
theorem hash_getD3 (kyber : Bool) (key eA eB : List (BitVec 8)) :
    (MlKemFast.hashStage FO BA KC kyber key eA eB).getD 3 [] =
      [MlKemFast.maskByte FO (MlKemFast.allBelow FO (MlKemFast.decode12 FO 1024 (key.take 1536)))] := rfl

theorem specEnc_eq (kyber : Bool) (key eA eB : List (BitVec 8)) :
    specEnc kyber key eA eB =
      let message := if kyber then Keccak.sha3_256 KC (List.zipWith ByteAuth.concrete.xor eA eB)
        else List.zipWith ByteAuth.concrete.xor eA eB
      let expanded := Keccak.sha3_512 KC (message ++ Keccak.sha3_256 KC key)
      let enc := MlKemPke.encrypt AR EN SH BA WO KC 4 2 11 5 224 key message (expanded.drop 32)
      ⟨enc.success, enc.bytes ++ MlKem.kdf KC kyber (expanded.take 32) enc.bytes⟩ := rfl

theorem message_length (kyber : Bool) (eA eB : List (BitVec 8))
    (hlen : kyber = true ∨ (eA.length = 32 ∧ eB.length = 32)) :
    (if kyber then Keccak.sha3_256 KC (List.zipWith ByteAuth.concrete.xor eA eB)
      else List.zipWith ByteAuth.concrete.xor eA eB).length = 32 := by
  cases kyber
  · rcases hlen with h | ⟨ha, hb⟩
    · exact absurd h (by decide)
    · simp [ha, hb]
  · exact Keccak.hash_length _ 136 6 32 _ (by decide) (by decide)

/-- **The composition, valid key.** The kernels' status, ciphertext and secret are the specification's
success byte and its ciphertext and shared secret, each gated by the success byte. -/
theorem pipeline_valid (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (hvalid : KeyValid key)
    (hlen : kyber = true ∨ (entropyA.length = 32 ∧ entropyB.length = 32)) :
    pipeline kyber key entropyA entropyB =
      [[(specEnc kyber key entropyA entropyB).success],
       ((specEnc kyber key entropyA entropyB).bytes.take 1568).map
         (ByteAuth.concrete.and (specEnc kyber key entropyA entropyB).success),
       ((specEnc kyber key entropyA entropyB).bytes.drop 1568).map
         (ByteAuth.concrete.and (specEnc kyber key entropyA entropyB).success)] := by
  have hm := message_length kyber entropyA entropyB hlen
  rw [specEnc_eq]
  unfold pipeline
  dsimp only
  rw [hash_getD0, hash_getD1, hash_getD2, hash_getD3]
  generalize (if kyber then Keccak.sha3_256 KC (List.zipWith ByteAuth.concrete.xor entropyA entropyB)
    else List.zipWith ByteAuth.concrete.xor entropyA entropyB) = message at hm ⊢
  generalize Keccak.sha3_512 KC (message ++ Keccak.sha3_256 KC key) = expanded
  rw [ct_eq key (expanded.drop 32) message hvalid hm]
  unfold MlKemFast.finishStage
  dsimp only
  rw [kernel_status key hvalid]
  have hl := encrypt_length key message (expanded.drop 32)
  rw [List.take_left' hl, List.drop_left' hl]
  rfl

/-- **The composition, invalid key.** If any encoded coefficient of the key is ≥ q, every output byte
(status, ciphertext, secret) is zero. -/
theorem pipeline_invalid (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (h : ¬ KeyValid key) :
    ∀ field ∈ pipeline kyber key entropyA entropyB, ∀ byte ∈ field, byte = 0 := by
  unfold pipeline
  dsimp only
  apply MlKemFast.finish_rejects
  rw [hash_getD3, keyValid_byte_invalid key h, List.foldl_append, List.foldl_cons, List.foldl_nil, KemSample.and0r]
  decide

theorem spec_success_cases (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) :
    (specEnc kyber key entropyA entropyB).success = 0 ∨ (specEnc kyber key entropyA entropyB).success = 255 := by
  show (sMat key).success = 0 ∨ (sMat key).success = 255
  rw [spec_success]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Valid key, the specification succeeds: status 255, and the kernels' ciphertext and secret are
exactly the specification's. -/
theorem pipeline_valid_accept (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (hvalid : KeyValid key)
    (hlen : kyber = true ∨ (entropyA.length = 32 ∧ entropyB.length = 32))
    (hs : (specEnc kyber key entropyA entropyB).success = 255) :
    pipeline kyber key entropyA entropyB =
      [[255], (specEnc kyber key entropyA entropyB).bytes.take 1568, (specEnc kyber key entropyA entropyB).bytes.drop 1568] := by
  rw [pipeline_valid kyber key entropyA entropyB hvalid hlen, hs]
  have h1 := ByteAuth.release_accept ((specEnc kyber key entropyA entropyB).bytes.take 1568)
  have h2 := ByteAuth.release_accept ((specEnc kyber key entropyA entropyB).bytes.drop 1568)
  simp only [ByteAuth.release] at h1 h2
  rw [h1, h2]

/-- Valid key, the specification's matrix sampling exhausted its budget: everything is zero. -/
theorem pipeline_valid_reject (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (hvalid : KeyValid key)
    (hlen : kyber = true ∨ (entropyA.length = 32 ∧ entropyB.length = 32))
    (hs : (specEnc kyber key entropyA entropyB).success ≠ 255) :
    ∀ field ∈ pipeline kyber key entropyA entropyB, ∀ byte ∈ field, byte = 0 := by
  have h0 : (specEnc kyber key entropyA entropyB).success = 0 := by
    rcases spec_success_cases kyber key entropyA entropyB with h | h
    · exact h
    · exact absurd h hs
  rw [pipeline_valid kyber key entropyA entropyB hvalid hlen, h0]
  intro field hf byte hb
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with h | h | h <;> rw [h] at hb
  · exact List.mem_singleton.mp hb
  · obtain ⟨x, _, hx⟩ := List.mem_map.mp hb; rw [← hx]; exact KemSample.and0l x
  · obtain ⟨x, _, hx⟩ := List.mem_map.mp hb; rw [← hx]; exact KemSample.and0l x

/-! ### The kernels themselves (`Kernel.values`) -/

section
open TlsMpc.MlKemFastKernel
open Std.Tactic.BVDecide

/-- Output field `idx` of kernel `k` under assignment `a`. -/
def outVal (k : HybridKernel.Kernel) (a : BVExpr.Assignment) (idx : Nat) : List (BitVec 8) :=
  (EstablishKernel.Kernel.values k a).getD idx []

/-- If every kernel's named inputs carry the named outputs of the earlier kernels (as the worker binds
them by name), `kem-finish`'s three outputs are `pipeline` of the key and the two entropy inputs. -/
theorem kernels_compose (kyber : Bool) (key entropyA entropyB : List (BitVec 8))
    (aH aN aV aF : BVExpr.Assignment) (aM aU : Nat → BVExpr.Assignment)
    (hH1 : (HybridKernel.lookup hashInputs "kyberPrekey").map (BVExpr.eval aH) = key)
    (hH2 : (HybridKernel.lookup hashInputs "entropyA").map (BVExpr.eval aH) = entropyA)
    (hH3 : (HybridKernel.lookup hashInputs "entropyB").map (BVExpr.eval aH) = entropyB)
    (hN : (HybridKernel.lookup nttInputs "coins").map (BVExpr.eval aN) = outVal (kemHash kyber) aH 2)
    (hM : ∀ i, (HybridKernel.lookup matrixInputs "kyberPrekey").map (BVExpr.eval (aM i)) = key)
    (hU1 : ∀ i, (HybridKernel.lookup (uInputs i) s!"row{i}").map (BVExpr.eval (aU i)) = outVal (kemMatrix i) (aM i) 0)
    (hU2 : ∀ i, (HybridKernel.lookup (uInputs i) "rhat").map (BVExpr.eval (aU i)) = outVal (kemNtt ()) aN 0)
    (hU3 : ∀ i, (HybridKernel.lookup (uInputs i) "coins").map (BVExpr.eval (aU i)) = outVal (kemHash kyber) aH 2)
    (hV1 : (HybridKernel.lookup vInputs "kyberPrekey").map (BVExpr.eval aV) = key)
    (hV2 : (HybridKernel.lookup vInputs "rhat").map (BVExpr.eval aV) = outVal (kemNtt ()) aN 0)
    (hV3 : (HybridKernel.lookup vInputs "coins").map (BVExpr.eval aV) = outVal (kemHash kyber) aH 2)
    (hV4 : (HybridKernel.lookup vInputs "message").map (BVExpr.eval aV) = outVal (kemHash kyber) aH 0)
    (hFu0 : (HybridKernel.lookup finishInputs "u0").map (BVExpr.eval aF) = outVal (kemU 0) (aU 0) 0)
    (hFu1 : (HybridKernel.lookup finishInputs "u1").map (BVExpr.eval aF) = outVal (kemU 1) (aU 1) 0)
    (hFu2 : (HybridKernel.lookup finishInputs "u2").map (BVExpr.eval aF) = outVal (kemU 2) (aU 2) 0)
    (hFu3 : (HybridKernel.lookup finishInputs "u3").map (BVExpr.eval aF) = outVal (kemU 3) (aU 3) 0)
    (hFv : (HybridKernel.lookup finishInputs "v").map (BVExpr.eval aF) = outVal (kemV ()) aV 0)
    (hFk : (HybridKernel.lookup finishInputs "kbar").map (BVExpr.eval aF) = outVal (kemHash kyber) aH 1)
    (hFo0 : (HybridKernel.lookup finishInputs "ok0").map (BVExpr.eval aF) = outVal (kemMatrix 0) (aM 0) 1)
    (hFo1 : (HybridKernel.lookup finishInputs "ok1").map (BVExpr.eval aF) = outVal (kemMatrix 1) (aM 1) 1)
    (hFo2 : (HybridKernel.lookup finishInputs "ok2").map (BVExpr.eval aF) = outVal (kemMatrix 2) (aM 2) 1)
    (hFo3 : (HybridKernel.lookup finishInputs "ok3").map (BVExpr.eval aF) = outVal (kemMatrix 3) (aM 3) 1)
    (hFkv : (HybridKernel.lookup finishInputs "keyValid").map (BVExpr.eval aF) = outVal (kemHash kyber) aH 3) :
    EstablishKernel.Kernel.values (kemFinish kyber) aF = pipeline kyber key entropyA entropyB := by
  have eH := kemHash_spec kyber aH
  have eN := kemNtt_spec aN
  have eV := kemV_spec aV
  have eF := kemFinish_spec kyber aF
  simp only at eH eV eF
  have oH : ∀ idx, outVal (kemHash kyber) aH idx =
      (MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD idx [] := by
    intro idx; rw [outVal, eH, hH1, hH2, hH3]
  have oN : outVal (kemNtt ()) aN 0 = MlKemFast.nttStage FO BA KC
      ((MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD 2 []) := by
    rw [outVal, eN, List.getD_cons_zero, hN, oH]
  have oM : ∀ i idx, outVal (kemMatrix i) (aM i) idx = (MlKemFast.matrixStage FO BA KC i key).getD idx [] := by
    intro i idx; rw [outVal, kemMatrix_spec, hM]
  have oU : ∀ i, outVal (kemU i) (aU i) 0 = MlKemFast.uStage FO BA KC i
      ((MlKemFast.matrixStage FO BA KC i key).getD 0 [])
      (MlKemFast.nttStage FO BA KC ((MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD 2 []))
      ((MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD 2 []) := by
    intro i
    have eU := kemU_spec i (aU i)
    simp only at eU
    rw [outVal, eU, List.getD_cons_zero, hU1, hU2, hU3, oM, oN, oH]
  have oV : outVal (kemV ()) aV 0 = MlKemFast.vStage FO BA KC key
      (MlKemFast.nttStage FO BA KC ((MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD 2 []))
      ((MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD 2 [])
      ((MlKemFast.hashStage FO BA KC kyber key entropyA entropyB).getD 0 []) := by
    rw [outVal, eV, List.getD_cons_zero, hV1, hV2, hV3, hV4, oN, oH, oH]
  rw [eF]
  simp only [List.map_append]
  rw [hFu0, hFu1, hFu2, hFu3, hFv, hFk, hFo0, hFo1, hFo2, hFo3, hFkv, oU, oU, oU, oU, oV, oH, oM, oM, oM, oM, oH]
  rfl

end

#print axioms kernels_compose
#print axioms pipeline_valid
#print axioms pipeline_invalid
#print axioms pipeline_valid_accept
#print axioms pipeline_valid_reject

end TlsMpc.KernelSpecs.KemCompose
