import TlsMpc.ReceiveProofs

/-!
# Receive gating, accept direction (T13, proof track P6)

New file; it changes no definition and no emitter imports it.

The receive kernels (`TlsMpc/ReceiveKernels.lean`) are proved equal to the `ReceiveFirst`
definitions on concrete bytes (`ReceiveProofs.*_spec`), and a rejected stage is proved to release
only zeros (`ReceiveProofs.*_rejects`). This file proves the ACCEPT direction on those concrete
definitions: what a status byte of 255 says. Companions: `ReceiveAcceptText.lean` (what
`receive-text` opens), `ReceiveAcceptAccessKey.lean` (the 72 profile-key layouts).

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `session_status_iff`: `receive-session`'s status is 255 EXACTLY when the earlier check bytes are
  255, no agreement is zero, the layouts `p`, `q` hold, the identity key is the sender's, the base
  key is valid and torsion free, the counter is some `n ≤ jump` and the post-quantum index some
  `1 + i ≤ 1 + jump`, the MAC (`MessageMac.tag`, libsignal `compute_mac`) verifies under
  `messageStep … n i` (libsignal's keys: PQXDH + the two ratchet steps (`keys`, whose HKDF form is
  `ReceiveProofs.keys_specification`), chain key `n` = `ChainKey::next_key` applied `n` times,
  `Symmetric.derive`), and the CBC padding is valid. Both directions.
* `session_accept_outputs`: then the plaintext is `CbcOpen.openCore` under those keys, the
  receiver record stores chain key `n + 1`, and the conversation record is as built.
* `session_status_cases`: the status is always 0 or 255, so `ReceiveProofs.session_rejects`
  covers every non-accepting run.
* `text_zero_unless_accepted`, `receiveText_gated` (kernel level): `receive-text` on the session's
  plaintext outputs only zeros unless the session's status is 255.
* `certificateVerified_iff`, `certificate_valid`, `session_accept_certificate`: status 255 ⇒ the
  certificate's identity is the sender's, its signer is the trusted one, `now ≤ expires`, and the
  signature's `R` is the compression of the field engine's `[s]B − [h]A`.
* `unsealStatic_valid_iff` / `_outputs`, `unsealMessage_valid_iff` / `_outputs`: sealed sender
  v1's two halves are valid exactly when the HMAC-SHA256 tags (truncated to 10 bytes) verify under
  the keys of `EphemeralKeys::calculate` / `StaticKeys::calculate`, the agreements are nonzero and
  the decrypted bytes have the expected leading bytes; the opened `certificateLength` is bytes 3..5
  of the AES-256-CTR decryption.
* `prekeyOpen_valid_iff` / `_outputs`: the opened ids and Kyber ciphertext are the message's own
  fields.
* `contentShape_rejects`, `prekeyShape_rejects`, `signalShape_rejects`: the shape kernels open only
  zeros unless the stage before was valid.
* `opened_*`: the exact list of opened outputs of each of the 13 receive kernels.
* `atMost_value`: `atMost` is big-endian `≤`; `counterBytes_one`: a one-byte counter `b` selects
  chain key `b`.

NOT PROVED here: that the field engine computes the agreements, `[s]B − [h]A` and the torsion check
(field-program theorems elsewhere); that `CbcOpen.openCore`'s unpadding is PKCS#7 (no value lemma
for `Unpad.decode`); that `SealedSenderV1.material`, `Symmetric.derive`, `SpqrChain.material`,
`MessageMac.tag` match the Rust code (tested only); and the converse for genuine envelopes produced
by a sender (it needs CTR decryption to invert encryption and the DH agreements to agree, which
are assumptions about the field engine and X25519).
-/
namespace TlsMpc.KernelSpecs.ReceiveAccept
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open Signal.ReceiveFirst

/-! ### Masks over concrete bytes -/

@[simp] theorem concrete_and (x y : BitVec 8) : ByteAuth.concrete.and x y = x &&& y := rfl
@[simp] theorem concrete_xor (x y : BitVec 8) : ByteAuth.concrete.xor x y = x ^^^ y := rfl
@[simp] theorem concrete_not (x : BitVec 8) : ByteAuth.concrete.not x = ~~~x := rfl
theorem concrete_const (n : Nat) : ByteAuth.concrete.const n = BitVec.ofNat 8 n := rfl
theorem zero_and' (x : BitVec 8) : (0 : BitVec 8) &&& x = 0 := BitVec.zero_and
theorem ones_and' (x : BitVec 8) : (255 : BitVec 8) &&& x = x := BitVec.allOnes_and
theorem xor_zero' (x : BitVec 8) : x ^^^ (0 : BitVec 8) = x := BitVec.xor_zero
theorem zero_xor' (x : BitVec 8) : (0 : BitVec 8) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 8) : x ||| (0 : BitVec 8) = x := BitVec.or_zero

@[simp] theorem get_cons_zero (x : BitVec 8) (xs : List (BitVec 8)) :
    OpenResult.get ByteAuth.concrete (x :: xs) 0 = x := rfl
theorem get_cons_succ (x : BitVec 8) (xs : List (BitVec 8)) (i : Nat) :
    OpenResult.get ByteAuth.concrete (x :: xs) (i + 1) = OpenResult.get ByteAuth.concrete xs i := rfl

theorem and_eq_255 {x y : BitVec 8} : x &&& y = 255 ↔ x = 255 ∧ y = 255 := by
  constructor
  · intro h
    have t := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at t
    have c : (255 : BitVec 8).toNat = 255 := rfl
    rw [c] at t
    have hx := Nat.and_le_left (n := x.toNat) (m := y.toNat)
    have hy := Nat.and_le_right (n := x.toNat) (m := y.toNat)
    have lx := x.isLt
    have ly := y.isLt
    constructor
    · apply BitVec.eq_of_toNat_eq; rw [c]; omega
    · apply BitVec.eq_of_toNat_eq; rw [c]; omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem ite_eq_255 (P : Prop) [Decidable P] : (if P then (255 : BitVec 8) else 0) = 255 ↔ P := by
  by_cases h : P <;> simp [h]

theorem foldl_and_eq_255 (z : BitVec 8) (ms : List (BitVec 8)) :
    ms.foldl ByteAuth.concrete.and z = 255 ↔ z = 255 ∧ ∀ m ∈ ms, m = 255 := by
  induction ms generalizing z with
  | nil => simp
  | cons m ms ih =>
      rw [List.foldl_cons, ih, concrete_and, and_eq_255]
      simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `all` is 255 exactly when every mask is. -/
theorem all_eq_255 (ms : List (BitVec 8)) : all ByteAuth.concrete ms = 255 ↔ ∀ m ∈ ms, m = 255 := by
  rw [all, foldl_and_eq_255]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem foldl_and_map_eq_255 {α : Type} (g : α → BitVec 8) (z : BitVec 8) (xs : List α) :
    xs.foldl (fun mask x => ByteAuth.concrete.and mask (g x)) z = 255 ↔ z = 255 ∧ ∀ x ∈ xs, g x = 255 := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, concrete_and, and_eq_255]
      simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

theorem isSet_value (flag : List (BitVec 8)) :
    isSet ByteAuth.concrete flag = if OpenResult.get ByteAuth.concrete flag 0 = 255 then 255 else 0 :=
  ByteAuth.eqMask_value _ _

theorem isSet_eq_255 (flag : List (BitVec 8)) :
    isSet ByteAuth.concrete flag = 255 ↔ OpenResult.get ByteAuth.concrete flag 0 = 255 := by
  rw [isSet_value, ite_eq_255]

theorem equalMask_eq_255 (xs ys : List (BitVec 8)) : ByteAuth.equalMask ByteAuth.concrete xs ys = 255 ↔ xs = ys := by
  rw [ByteAuth.equalMask_value, ite_eq_255]

theorem eqMask_eq_255 (x y : BitVec 8) : ByteAuth.eqMask ByteAuth.concrete x y = 255 ↔ x = y := by
  rw [ByteAuth.eqMask_value, ite_eq_255]

theorem expect_eq_255 (bytes : List (BitVec 8)) (offset : Nat) (expected : List (BitVec 8)) :
    expect ByteAuth.concrete bytes offset expected = 255 ↔ Establish.part bytes offset expected.length = expected :=
  equalMask_eq_255 _ _

theorem agreementMask_eq_255 (agreement : List (BitVec 8)) :
    DhRatchet.agreementMask ByteAuth.concrete agreement = 255 ↔ agreement ≠ List.replicate 32 0 := by
  rw [DhRatchet.agreementMask_value, ite_eq_255]

/-- `Establish.accepted`: every check byte is 255 and no agreement is all zero. -/
theorem accepted_eq_255 (checks : List (BitVec 8)) (agreements : List (List (BitVec 8))) :
    Establish.accepted ByteAuth.concrete checks agreements = 255 ↔
      (∀ c ∈ checks, c = 255) ∧ ∀ g ∈ agreements, g ≠ List.replicate 32 0 := by
  rw [Establish.accepted, foldl_and_map_eq_255, foldl_and_map_eq_255]
  simp only [eqMask_eq_255, agreementMask_eq_255, concrete_const]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨rfl, h.1⟩, h.2⟩⟩

theorem release_255 (bytes : List (BitVec 8)) : ByteAuth.release ByteAuth.concrete 255 bytes = bytes :=
  ByteAuth.release_accept bytes

/-! ### Selecting one of several precomputed values by a private index -/

theorem numberBytes_inj {n m : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32)
    (h : numberBytes ByteAuth.concrete n = numberBytes ByteAuth.concrete m) : n = m := by
  simp only [numberBytes, List.range, List.range.loop, List.map_cons, List.map_nil, concrete_const,
    List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  have t0 := congrArg BitVec.toNat h0
  have t1 := congrArg BitVec.toNat h1
  have t2 := congrArg BitVec.toNat h2
  have t3 := congrArg BitVec.toNat h3
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub] at t0 t1 t2 t3
  omega

theorem either_concrete (x y : BitVec 8) : either ByteAuth.concrete x y = x ||| y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [either, hi]

theorem or_255 : ∀ m : BitVec 8, (255 : BitVec 8) ||| m = 255 := by decide

theorem foldl_either_255 (ms : List (BitVec 8)) (acc : BitVec 8) (h : acc = 255 ∨ (255 : BitVec 8) ∈ ms) :
    ms.foldl (either ByteAuth.concrete) acc = 255 := by
  induction ms generalizing acc with
  | nil => simpa using h
  | cons m ms ih =>
      rw [List.foldl_cons]
      apply ih
      rcases h with rfl | h
      · left; rw [either_concrete, or_255]
      · rcases List.mem_cons.mp h with rfl | h
        · left; rw [either_concrete, BitVec.or_comm, or_255]
        · right; exact h

theorem candidates_mask_miss (index : List (BitVec 8)) (n : Nat) (values : List (List (BitVec 8)))
    (miss : ∀ k < values.length, index ≠ numberBytes ByteAuth.concrete (n + k)) :
    ∀ c ∈ candidates ByteAuth.concrete index n values, c.1 = 0 := by
  induction values generalizing n with
  | nil => simp [candidates]
  | cons v vs ih =>
      intro c hc
      simp only [candidates, List.mem_cons] at hc
      rcases hc with rfl | hc
      · have h0 : index ≠ numberBytes ByteAuth.concrete n := by simpa using miss 0 (by simp)
        simp only [ByteAuth.equalMask_value, if_neg h0]
      · apply ih (n + 1) _ c hc
        intro k hk
        have := miss (k + 1) (by simp; omega)
        rwa [show n + (k + 1) = n + 1 + k by omega] at this

theorem candidates_mask_hit (index : List (BitVec 8)) (n i : Nat) (values : List (List (BitVec 8)))
    (hi : i < values.length) (hidx : index = numberBytes ByteAuth.concrete (n + i)) :
    (255 : BitVec 8) ∈ (candidates ByteAuth.concrete index n values).map (fun c => c.1) := by
  induction values generalizing n i with
  | nil => simp at hi
  | cons v vs ih =>
      simp only [candidates, List.map_cons, List.mem_cons]
      cases i with
      | zero => left; rw [ByteAuth.equalMask_value, if_pos (by simpa using hidx)]
      | succ i =>
          right
          exact ih (n + 1) i (by simp at hi; omega) (by rw [hidx]; congr 1; omega)

theorem candidates_pick_miss (index : List (BitVec 8)) (n j : Nat) (values : List (List (BitVec 8)))
    (miss : ∀ k < values.length, index ≠ numberBytes ByteAuth.concrete (n + k)) (acc : BitVec 8) :
    ((candidates ByteAuth.concrete index n values).map (fun c => (c.1, OpenResult.get ByteAuth.concrete c.2 j))).foldl
      (fun acc choice => ByteAuth.concrete.xor acc (ByteAuth.concrete.and choice.1 choice.2)) acc = acc := by
  induction values generalizing n acc with
  | nil => rfl
  | cons v vs ih =>
      simp only [candidates, List.map_cons, List.foldl_cons]
      have h0 : index ≠ numberBytes ByteAuth.concrete n := by simpa using miss 0 (by simp)
      rw [ByteAuth.equalMask_value, if_neg h0, concrete_and, concrete_xor, zero_and', xor_zero']
      apply ih (n + 1)
      intro k hk
      have := miss (k + 1) (by simp; omega)
      rwa [show n + (k + 1) = n + 1 + k by omega] at this

theorem candidates_pick_hit (index : List (BitVec 8)) (n i j : Nat) (values : List (List (BitVec 8)))
    (hi : i < values.length) (hidx : index = numberBytes ByteAuth.concrete (n + i))
    (uniq : ∀ k < values.length, k ≠ i → index ≠ numberBytes ByteAuth.concrete (n + k)) (acc : BitVec 8) :
    ((candidates ByteAuth.concrete index n values).map (fun c => (c.1, OpenResult.get ByteAuth.concrete c.2 j))).foldl
      (fun acc choice => ByteAuth.concrete.xor acc (ByteAuth.concrete.and choice.1 choice.2)) acc =
      acc ^^^ OpenResult.get ByteAuth.concrete (values.getD i []) j := by
  induction values generalizing n i acc with
  | nil => simp at hi
  | cons v vs ih =>
      simp only [candidates, List.map_cons, List.foldl_cons]
      cases i with
      | zero =>
          rw [ByteAuth.equalMask_value, if_pos (by simpa using hidx), concrete_and, concrete_xor, ones_and']
          rw [candidates_pick_miss index (n + 1) j vs _ _]
          · rfl
          · intro k hk
            have := uniq (k + 1) (by simp; omega) (by omega)
            rwa [show n + (k + 1) = n + 1 + k by omega] at this
      | succ i =>
          have h0 : index ≠ numberBytes ByteAuth.concrete n := by simpa using uniq 0 (by simp) (by omega)
          rw [ByteAuth.equalMask_value, if_neg h0, concrete_and, concrete_xor, zero_and', xor_zero']
          rw [ih (n + 1) i (by simp at hi; omega) (by rw [hidx]; congr 1; omega)]
          · rfl
          · intro k hk hki
            have := uniq (k + 1) (by simp; omega) (by omega)
            rwa [show n + (k + 1) = n + 1 + k by omega] at this

/-- Selection when the index is one of the candidates. -/
theorem selectAt_hit (index : List (BitVec 8)) (first : Nat) (values : List (List (BitVec 8))) (width i : Nat)
    (hi : i < values.length) (hidx : index = numberBytes ByteAuth.concrete (first + i))
    (hb : first + values.length ≤ 2 ^ 32) :
    selectAt ByteAuth.concrete index first values width =
      255 :: (List.range width).map (fun j => OpenResult.get ByteAuth.concrete (values.getD i []) j) := by
  have uniq : ∀ k < values.length, k ≠ i → index ≠ numberBytes ByteAuth.concrete (first + k) := by
    intro k hk hki heq
    rw [hidx] at heq
    have := numberBytes_inj (by omega) (by omega) heq
    omega
  simp only [selectAt, any, pick]
  rw [foldl_either_255 _ _ (Or.inr (candidates_mask_hit index first i values hi hidx))]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [candidates_pick_hit index first i j values hi hidx uniq]
  simp [concrete_const]

/-- Selection when the index is none of the candidates. -/
theorem selectAt_miss (index : List (BitVec 8)) (first : Nat) (values : List (List (BitVec 8))) (width : Nat)
    (miss : ∀ k < values.length, index ≠ numberBytes ByteAuth.concrete (first + k)) :
    selectAt ByteAuth.concrete index first values width = 0 :: List.replicate width 0 := by
  simp only [selectAt, any, pick]
  have masks := candidates_mask_miss index first values miss
  have hany : ∀ acc, ((candidates ByteAuth.concrete index first values).map (fun c => c.1)).foldl
      (either ByteAuth.concrete) acc = acc := by
    intro acc
    generalize candidates ByteAuth.concrete index first values = cs at masks
    induction cs generalizing acc with
    | nil => rfl
    | cons c cs ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [masks c (by simp), either_concrete, or_zero']
        exact ih acc (fun c' h => masks c' (by simp [h]))
  rw [hany]
  congr 1
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_map, List.getElem_replicate]
  rw [candidates_pick_miss index first _ values miss]
  rfl

theorem range_map_get (xs : List (BitVec 8)) :
    (List.range xs.length).map (fun j => OpenResult.get ByteAuth.concrete xs j) = xs := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [OpenResult.get, List.getElem?_eq_getElem h2]

/-- What a selection says, when every candidate value has the selected width: the validity
byte is 255 and the selected bytes satisfy `R` exactly when the index is a candidate whose value
satisfies `R`. -/
theorem selectAt_accept_iff (index : List (BitVec 8)) (first : Nat) (values : List (List (BitVec 8)))
    (width : Nat) (hb : first + values.length ≤ 2 ^ 32) (hw : ∀ v ∈ values, v.length = width)
    (R : List (BitVec 8) → Prop) :
    (OpenResult.get ByteAuth.concrete (selectAt ByteAuth.concrete index first values width) 0 = 255 ∧
        R ((selectAt ByteAuth.concrete index first values width).drop 1)) ↔
      ∃ i, i < values.length ∧ index = numberBytes ByteAuth.concrete (first + i) ∧ R (values.getD i []) := by
  by_cases hex : ∃ i, i < values.length ∧ index = numberBytes ByteAuth.concrete (first + i)
  · obtain ⟨i, hi, hidx⟩ := hex
    have hv : values.getD i [] = values[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hlen : (values.getD i []).length = width := by rw [hv]; exact hw _ (List.getElem_mem hi)
    rw [selectAt_hit index first values width i hi hidx hb, get_cons_zero, List.drop_one, List.tail_cons,
      ← hlen, range_map_get]
    constructor
    · rintro ⟨-, hr⟩; exact ⟨i, hi, hidx, hr⟩
    · rintro ⟨k, hk, hkidx, hr⟩
      have : first + k = first + i := numberBytes_inj (by omega) (by omega) (hkidx.symm.trans hidx)
      have hki : k = i := by omega
      subst hki
      exact ⟨rfl, hr⟩
  · have miss : ∀ k < values.length, index ≠ numberBytes ByteAuth.concrete (first + k) :=
      fun k hk heq => hex ⟨k, hk, heq⟩
    rw [selectAt_miss index first values width miss, get_cons_zero]
    constructor
    · rintro ⟨h, -⟩; exact absurd h (by decide)
    · rintro ⟨k, hk, heq, -⟩; exact absurd heq (miss k hk)

theorem range_map_get_of_length (xs : List (BitVec 8)) (L : Nat) (h : xs.length = L) :
    (List.range L).map (fun j => OpenResult.get ByteAuth.concrete xs j) = xs := by
  subst h; exact range_map_get xs

theorem getD_mem {α : Type} (xs : List (List α)) (i : Nat) (hi : i < xs.length) : xs.getD i [] ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem ofNat255_and (x : BitVec 8) : BitVec.ofNat 8 255 &&& x = x := BitVec.allOnes_and

theorem zero_ne_255 : ((0 : BitVec 8) = 255) ↔ False := by decide

theorem exists_witness_iff {P G : Nat → Prop} (n : Nat) (hP : ∀ m, P m ↔ m = n) :
    (∃ m, P m ∧ G m) ↔ G n := by
  constructor
  · rintro ⟨m, hm, hg⟩; rwa [(hP m).1 hm] at hg
  · intro hg; exact ⟨n, (hP n).2 rfl, hg⟩

/-! ### Keys of the first message -/

theorem keys_length (dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement : List (BitVec 8)) :
    (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement).length = 224 := by
  simp [keys, DhRatchet.materialFast_correct, DhRatchet.material_length, PrivateInitialSpqrV1.chainStart,
    TlsKdf.expandFast_correct, TlsKdf.expandCore_length]

theorem chainKeys_length (count : Nat) (key : List (BitVec 8)) :
    (chainKeys Sha256.concrete count key).length = count + 1 := by
  induction count generalizing key with
  | zero => rfl
  | succ count ih => simp [chainKeys, ih]

/-- `f` applied `n` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- Chain key `n` is the starting key advanced `n` times (`ratchet/keys.rs`, `ChainKey::next_key`:
HMAC-SHA256 of the byte 2). -/
theorem chainKeys_getD (count n : Nat) (key : List (BitVec 8)) (hn : n ≤ count) :
    (chainKeys Sha256.concrete count key).getD n [] = iter (Symmetric.nextChainKey Sha256.concrete) n key := by
  induction count generalizing n key with
  | zero =>
      obtain rfl : n = 0 := by omega
      rfl
  | succ count ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [chainKeys, List.getD_cons_succ, iter]
          exact ih n _ (by omega)

theorem nextChainKey_length (key : List (BitVec 8)) : (Symmetric.nextChainKey Sha256.concrete key).length = 32 := by
  simp [Symmetric.nextChainKey, Sha256.hmac_length]

theorem chainKeys_mem_length (count : Nat) (key : List (BitVec 8)) (h : key.length = 32) :
    ∀ v ∈ chainKeys Sha256.concrete count key, v.length = 32 := by
  induction count generalizing key with
  | zero =>
      intro v hv
      simp only [chainKeys, List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv; exact h
  | succ count ih =>
      intro v hv
      simp only [chainKeys, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact h
      · exact ih _ (nextChainKey_length _) v hv

theorem pqKeys_length (count counter : Nat) (key : List (BitVec 8)) :
    (pqKeys Sha256.concrete ByteAuth.concrete count counter key).length = count := by
  induction count generalizing counter key with
  | zero => rfl
  | succ count ih => simp [pqKeys, ih]

theorem pqKeys_mem_length (count counter : Nat) (key : List (BitVec 8)) :
    ∀ v ∈ pqKeys Sha256.concrete ByteAuth.concrete count counter key, v.length = 64 := by
  induction count generalizing counter key with
  | zero => simp [pqKeys]
  | succ count ih =>
      intro v hv
      simp only [pqKeys, List.mem_cons] at hv
      rcases hv with rfl | hv
      · simp [SpqrChain.materialFast_correct, SpqrChain.material_length]
      · exact ih _ _ v hv

theorem part_four (a b c e : List (BitVec 8)) (ha : a.length = 32) (hb : b.length = 32) (hc : c.length = 32)
    (he : e.length = 16) :
    Establish.part (a ++ (b ++ c ++ e)) 0 32 = a ∧ Establish.part (a ++ (b ++ c ++ e)) 32 32 = b ∧
      Establish.part (a ++ (b ++ c ++ e)) 64 32 = c ∧ Establish.part (a ++ (b ++ c ++ e)) 96 16 = e := by
  have d1 : List.drop 96 a = [] := List.drop_eq_nil_of_le (by omega)
  have d2 : List.drop 64 b = [] := List.drop_eq_nil_of_le (by omega)
  have d3 : List.take 16 e = e := List.take_of_length_le (by omega)
  simp [Establish.part, List.take_append, List.drop_append, ha, hb, hc, d1, d2, d3]

/-- The four parts of `messageKeys` are libsignal's next chain key, cipher key, MAC key and IV
(`Symmetric.derive`, the transcription of `ratchet/keys.rs`). -/
theorem messageKeys_parts (chainKey salt : List (BitVec 8)) :
    Establish.part (messageKeys Sha256.concrete chainKey salt) 0 32 =
        (Symmetric.derive Sha256.concrete chainKey salt).nextChainKey ∧
      Establish.part (messageKeys Sha256.concrete chainKey salt) 32 32 =
        (Symmetric.derive Sha256.concrete chainKey salt).material.cipherKey ∧
      Establish.part (messageKeys Sha256.concrete chainKey salt) 64 32 =
        (Symmetric.derive Sha256.concrete chainKey salt).material.macKey ∧
      Establish.part (messageKeys Sha256.concrete chainKey salt) 96 16 =
        (Symmetric.derive Sha256.concrete chainKey salt).material.iv := by
  rw [messageKeys, Symmetric.deriveFast_correct]
  obtain ⟨h1, h2, h3⟩ := Symmetric.messageMaterial_lengths Sha256.concrete
    (Symmetric.messageSeed Sha256.concrete chainKey) salt
  exact part_four _ _ _ _ (nextChainKey_length chainKey) h1 h2 h3

/-! ### `receive-session`: what status 255 says -/

/-- The SignalMessage inside the PreKeySignalMessage (public layout `p`, `size`). -/
def signalWire (p : PreKeyShape) (size : Nat) (message : List (BitVec 8)) : List (BitVec 8) :=
  Establish.part message (p.signalAt size) (p.signalSize size)

/-- The 4-byte value of the message counter (a varint of `q.counter` bytes at offset 37). -/
def counterBytes (q : SignalShape) (w : List (BitVec 8)) : List (BitVec 8) :=
  varintValue ByteAuth.concrete (Establish.part w 37 q.counter)

/-- The post-quantum index as 4 bytes (a one-byte varint; `signalMask` requires its top bit clear). -/
def pqIndexBytes (q : SignalShape) (signalSize : Nat) (w : List (BitVec 8)) : List (BitVec 8) :=
  lit ByteAuth.concrete [0, 0, 0] ++ [OpenResult.get ByteAuth.concrete w (q.pqAt signalSize + 2)]

/-- Sender then recipient address, as `signalMask` expects them. -/
def expectedAddresses (localAddress uuid device : List (BitVec 8)) : List (BitVec 8) :=
  Establish.addresses ByteAuth.concrete (uuid ++ device) (localAddress.take 16) (OpenResult.get ByteAuth.concrete localAddress 16)

/-- Receiving chain key `n` from the session keys `k` (bytes 32..64: the chain created by the
receiving ratchet step). -/
def chainKey (k : List (BitVec 8)) (n : Nat) : List (BitVec 8) :=
  iter (Symmetric.nextChainKey Sha256.concrete) n (Establish.part k 32 32)

/-- Post-quantum chain output `i` (next key 32 ‖ message key 32) of our receiving (A2B) chain,
started from bytes 160..192 of `k`. -/
def pqMaterial (k : List (BitVec 8)) (jump i : Nat) : List (BitVec 8) :=
  (pqKeys Sha256.concrete ByteAuth.concrete (jump + 1) 0 (Establish.part k 160 32)).getD i []

/-- libsignal's message keys for chain key `n` and post-quantum key `i`. -/
def messageStep (k : List (BitVec 8)) (jump n i : Nat) : Symmetric.Step (BitVec 8) :=
  Symmetric.derive Sha256.concrete (chainKey k n) (Establish.part (pqMaterial k jump i) 32 32)

section Session
variable (p : PreKeyShape) (q : SignalShape) (size jump : Nat)
  (message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
    sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId : List (BitVec 8))

/-- **`receive-session` status 255, exactly.** The status is 255 if and only if

* every earlier check byte (`prekeyValid`, `verified`) is 255 and no agreement is all zero;
* the PreKeySignalMessage has layout `p`, carries the sender identity `senderIdentity`;
* the base key is a valid, torsion-free point (`baseValid`, `torsionX`, `torsionY`);
* the SignalMessage has layout `q` and, if it carries addresses, they are (sender, us);
* its counter is some `n ≤ jump` and its post-quantum index some `1 + i ≤ 1 + jump`;
* the MAC verifies under libsignal's MAC key for chain key `n` and post-quantum key `i`
  (`MessageMac.tag`: HMAC-SHA256 over `05 ‖ sender ‖ 05 ‖ us ‖ message`, first 8 bytes); and
* the AES-256-CBC decryption under the cipher key and IV of those same keys has valid padding. -/
theorem session_status_iff (hjump : jump ≤ 16) :
    (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [255] ↔
    ((∀ c ∈ checks, c = 255) ∧
      (∀ g ∈ [dh1, dh2, dh3, oneTime, receiveAgreement, sendAgreement], g ≠ List.replicate 32 0) ∧
      prekeyMask ByteAuth.concrete p size message = 255 ∧
      Establish.part message (p.keysAt + 38) 32 = senderIdentity ∧
      baseValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
      torsionX = List.replicate 32 (ByteAuth.concrete.const 0) ∧
      torsionY = List.replicate 32 (ByteAuth.concrete.const 0) ∧
      signalMask ByteAuth.concrete q (p.signalSize size) (signalWire p size message)
        (expectedAddresses localAddress uuid device) = 255) ∧
    ∃ n, (n ≤ jump ∧ counterBytes q (signalWire p size message) = numberBytes ByteAuth.concrete n) ∧
    ∃ i, (i ≤ jump ∧ pqIndexBytes q (p.signalSize size) (signalWire p size message) =
        numberBytes ByteAuth.concrete (1 + i)) ∧
      MessageMac.tag Sha256.concrete
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.macKey
          senderIdentity ourIdentity (MessageMac.content (signalWire p size message)) =
        MessageMac.receivedTag (signalWire p size message) ∧
      OpenResult.get ByteAuth.concrete (CbcOpen.openCore AesInverse.concrete ByteAuth.concrete
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.cipherKey
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.iv
          (Establish.part (signalWire p size message) q.cipherAt q.ciphertext)) 0 = 255 := by
  have hklen := keys_length dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
  unfold messageStep chainKey pqMaterial counterBytes pqIndexBytes expectedAddresses
  simp only [session, List.getD_cons_zero, OpenResult.finish, get_cons_zero, List.cons.injEq, and_true,
    concrete_and, and_eq_255, all_eq_255, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    accepted_eq_255, equalMask_eq_255, MessageMac.verifyMask_value, ite_eq_255, CbcOpen.openCore, ofNat255_and,
    concrete_const]
  generalize keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement = k at hklen ⊢
  unfold signalWire
  generalize Establish.part message (p.signalAt size) (p.signalSize size) = w
  have hck : (Establish.part k 32 32).length = 32 := by simp [Establish.part, hklen]
  have hb1 : 0 + (chainKeys Sha256.concrete jump (Establish.part k 32 32)).length ≤ 2 ^ 32 := by
    rw [chainKeys_length]; omega
  have hb2 : 1 + (pqKeys Sha256.concrete ByteAuth.concrete (jump + 1) 0 (Establish.part k 160 32)).length ≤ 2 ^ 32 := by
    rw [pqKeys_length]; omega
  by_cases hc : ∃ n, n < jump + 1 ∧
      varintValue ByteAuth.concrete (Establish.part w 37 q.counter) = numberBytes ByteAuth.concrete (0 + n)
  · obtain ⟨n, hn, hcn⟩ := hc
    have hn' : n < (chainKeys Sha256.concrete jump (Establish.part k 32 32)).length := by
      rw [chainKeys_length]; exact hn
    rw [selectAt_hit _ 0 _ 32 n hn' hcn hb1]
    have hcl := chainKeys_mem_length jump _ hck _ (getD_mem _ n hn')
    rw [chainKeys_getD jump n _ (by omega)] at hcl ⊢
    by_cases hp : ∃ i, i < jump + 1 ∧
        lit ByteAuth.concrete [0, 0, 0] ++ [OpenResult.get ByteAuth.concrete w (q.pqAt (p.signalSize size) + 2)] =
          numberBytes ByteAuth.concrete (1 + i)
    · obtain ⟨i, hi, hpi⟩ := hp
      have hi' : i < (pqKeys Sha256.concrete ByteAuth.concrete (jump + 1) 0 (Establish.part k 160 32)).length := by
        rw [pqKeys_length]; exact hi
      rw [selectAt_hit _ 1 _ 64 i hi' hpi hb2]
      have hpl := pqKeys_mem_length (jump + 1) 0 _ _ (getD_mem _ i hi')
      have h33 : ∀ (x : BitVec 8) (xs : List (BitVec 8)), Establish.part (x :: xs) 33 32 = Establish.part xs 32 32 := by
        intro x xs; rfl
      simp only [get_cons_zero, List.drop_one, List.tail_cons, h33, range_map_get_of_length _ _ hcl,
        range_map_get_of_length _ _ hpl, (messageKeys_parts _ _).2.1, (messageKeys_parts _ _).2.2.1,
        (messageKeys_parts _ _).2.2.2, true_and]
      simp only [Nat.zero_add] at hcn
      have hCn : ∀ m, (m ≤ jump ∧ varintValue ByteAuth.concrete (Establish.part w 37 q.counter) =
          numberBytes ByteAuth.concrete m) ↔ m = n := by
        intro m
        constructor
        · rintro ⟨hm, hcm⟩; exact numberBytes_inj (by omega) (by omega) (hcm.symm.trans hcn)
        · rintro rfl; exact ⟨by omega, hcn⟩
      have hPi : ∀ m, (m ≤ jump ∧ lit ByteAuth.concrete [0, 0, 0] ++
          [OpenResult.get ByteAuth.concrete w (q.pqAt (p.signalSize size) + 2)] =
            numberBytes ByteAuth.concrete (1 + m)) ↔ m = i := by
        intro m
        constructor
        · rintro ⟨hm, hpm⟩
          have := numberBytes_inj (by omega) (by omega) (hpm.symm.trans hpi)
          omega
        · rintro rfl; exact ⟨by omega, hpi⟩
      rw [exists_witness_iff n hCn, exists_witness_iff i hPi]
      simp only [and_assoc]
    · have miss : ∀ k' < (pqKeys Sha256.concrete ByteAuth.concrete (jump + 1) 0 (Establish.part k 160 32)).length,
          lit ByteAuth.concrete [0, 0, 0] ++ [OpenResult.get ByteAuth.concrete w (q.pqAt (p.signalSize size) + 2)] ≠
            numberBytes ByteAuth.concrete (1 + k') := by
        intro k' hk' heq; rw [pqKeys_length] at hk'; exact hp ⟨k', hk', heq⟩
      rw [selectAt_miss _ 1 _ 64 miss]
      simp only [get_cons_zero, zero_ne_255, false_and, and_false, false_iff]
      rintro ⟨_, _, _, i, ⟨hi, hpi⟩, _⟩
      exact hp ⟨i, by omega, hpi⟩
  · have miss : ∀ k' < (chainKeys Sha256.concrete jump (Establish.part k 32 32)).length,
        varintValue ByteAuth.concrete (Establish.part w 37 q.counter) ≠ numberBytes ByteAuth.concrete (0 + k') := by
      intro k' hk' heq; rw [chainKeys_length] at hk'; exact hc ⟨k', hk', heq⟩
    rw [selectAt_miss _ 0 _ 32 miss]
    simp only [get_cons_zero, zero_ne_255, false_and, and_false, false_iff]
    rintro ⟨_, n, ⟨hn, hcn⟩, _⟩
    exact hc ⟨n, by omega, by simpa using hcn⟩

/-- **What `receive-session` releases when its status is 255.** For the counter `n` and
post-quantum index `1 + i` of `session_status_iff`:

* `plaintext` (output 3, the input of `receive-text` and `receive-access-key`) is exactly the
  AES-256-CBC decryption with PKCS#7 unpadding (`CbcOpen.openCore`, without its status byte) of the
  message's ciphertext under libsignal's cipher key and IV for that counter;
* the receiver record (output 2) stores the root key, the NEXT chain key (`n + 1`), the sender's
  ratchet key, the next counter, the post-quantum root, the next post-quantum chain key, the index
  and the sender's base key;
* the conversation record (output 1) is the send kernels' record built from the session keys. -/
theorem session_accept_outputs (hjump : jump ≤ 16)
    (h : (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [255]) :
    ∃ n i, (n ≤ jump ∧ counterBytes q (signalWire p size message) = numberBytes ByteAuth.concrete n) ∧
      (i ≤ jump ∧ pqIndexBytes q (p.signalSize size) (signalWire p size message) =
        numberBytes ByteAuth.concrete (1 + i)) ∧
      (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
        ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
        baseValid torsionX torsionY certificate accessKey requestId).getD 1 [] =
        certificate ++ Establish.session ByteAuth.concrete 80 ratchetPublic
          (Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 96 32)
          (Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 192 32)
          ourIdentity senderIdentity ++
        Establish.metadata ByteAuth.concrete uuid accessKey requestId device
          (varintValue ByteAuth.concrete (Establish.part message (p.idsAt size + 1) p.registration)) ∧
      (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
        ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
        baseValid torsionX torsionY certificate accessKey requestId).getD 2 [] =
        Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 64 32 ++
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).nextChainKey ++
          Establish.part (signalWire p size message) 4 32 ++
          ChainSend.nextCounter Sha256.concrete ByteAuth.concrete (counterBytes q (signalWire p size message)) ++
          Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 128 32 ++
          Establish.part (pqMaterial (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump i) 0 32 ++
          pqIndexBytes q (p.signalSize size) (signalWire p size message) ++
          Establish.part message (p.keysAt + 3) 32 ∧
      (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
        ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
        baseValid torsionX torsionY certificate accessKey requestId).getD 3 [] =
        (CbcOpen.openCore AesInverse.concrete ByteAuth.concrete
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.cipherKey
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.iv
          (Establish.part (signalWire p size message) q.cipherAt q.ciphertext)).drop 1 := by
  obtain ⟨_, n, ⟨hn, hcn⟩, i, ⟨hi, hpi⟩, _, _⟩ := (session_status_iff p q size jump message checks senderIdentity
    ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
    baseValid torsionX torsionY certificate accessKey requestId hjump).mp h
  refine ⟨n, i, ⟨hn, hcn⟩, ⟨hi, hpi⟩, ?_⟩
  have hklen := keys_length dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
  unfold messageStep chainKey pqMaterial counterBytes pqIndexBytes signalWire at *
  simp only [session, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true] at h ⊢
  generalize keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement = k at hklen h ⊢
  generalize Establish.part message (p.signalAt size) (p.signalSize size) = w at hcn hpi h ⊢
  have hck : (Establish.part k 32 32).length = 32 := by simp [Establish.part, hklen]
  have hn' : n < (chainKeys Sha256.concrete jump (Establish.part k 32 32)).length := by
    rw [chainKeys_length]; omega
  have hi' : i < (pqKeys Sha256.concrete ByteAuth.concrete (jump + 1) 0 (Establish.part k 160 32)).length := by
    rw [pqKeys_length]; omega
  have hb1 : 0 + (chainKeys Sha256.concrete jump (Establish.part k 32 32)).length ≤ 2 ^ 32 := by
    rw [chainKeys_length]; omega
  have hb2 : 1 + (pqKeys Sha256.concrete ByteAuth.concrete (jump + 1) 0 (Establish.part k 160 32)).length ≤ 2 ^ 32 := by
    rw [pqKeys_length]; omega
  rw [selectAt_hit _ 0 _ 32 n hn' (by simpa using hcn) hb1, selectAt_hit _ 1 _ 64 i hi' hpi hb2] at h ⊢
  have hcl := chainKeys_mem_length jump _ hck _ (getD_mem _ n hn')
  have hpl := pqKeys_mem_length (jump + 1) 0 _ _ (getD_mem _ i hi')
  rw [chainKeys_getD jump n _ (by omega)] at hcl h ⊢
  have h33 : ∀ (x : BitVec 8) (xs : List (BitVec 8)), Establish.part (x :: xs) 33 32 = Establish.part xs 32 32 := by
    intro x xs; rfl
  have h1 : ∀ (x : BitVec 8) (xs : List (BitVec 8)), Establish.part (x :: xs) 1 32 = Establish.part xs 0 32 := by
    intro x xs; rfl
  simp only [get_cons_zero, List.drop_one, List.tail_cons, h33, h1, range_map_get_of_length _ _ hcl,
    range_map_get_of_length _ _ hpl, (messageKeys_parts _ _).1, (messageKeys_parts _ _).2.1,
    (messageKeys_parts _ _).2.2.1, (messageKeys_parts _ _).2.2.2, OpenResult.finish, concrete_and] at h ⊢
  obtain ⟨hchk, hpad⟩ := and_eq_255.mp h
  rw [hchk, hpad]
  simp only [ones_and', release_255, CbcOpen.openCore, OpenResult.finish, concrete_const, ofNat255_and,
    concrete_and, List.tail_cons, hpad]
  exact ⟨trivial, trivial, trivial⟩

end Session

/-! ### Every status byte is 0 or 255 -/

/-- A mask byte: 0 or 255. -/
def IsMask (x : BitVec 8) : Prop := x = 0 ∨ x = 255

instance (x : BitVec 8) : Decidable (IsMask x) := inferInstanceAs (Decidable (_ ∨ _))

theorem isMask_and {x y : BitVec 8} (hx : IsMask x) (hy : IsMask y) : IsMask (ByteAuth.concrete.and x y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem isMask_not {x : BitVec 8} (hx : IsMask x) : IsMask (ByteAuth.concrete.not x) := by
  rcases hx with rfl | rfl <;> decide

theorem isMask_ite (P : Prop) [Decidable P] : IsMask (if P then 255 else 0) := by
  by_cases h : P
  · right; simp [h]
  · left; simp [h]

theorem isMask_const255 : IsMask (ByteAuth.concrete.const 255) := Or.inr rfl
theorem isMask_const0 : IsMask (ByteAuth.concrete.const 0) := Or.inl rfl

theorem isMask_maskBit (x : BitVec 8) (i : Nat) : IsMask (ByteAuth.concrete.maskBit x i) := by
  have all : ∀ b : BitVec 1, IsMask (BitVec.replicate 8 b) := by decide
  exact all _

theorem isMask_eqMask (x y : BitVec 8) : IsMask (ByteAuth.eqMask ByteAuth.concrete x y) := by
  rw [ByteAuth.eqMask_value]; exact isMask_ite _

theorem isMask_equalMask (xs ys : List (BitVec 8)) : IsMask (ByteAuth.equalMask ByteAuth.concrete xs ys) := by
  rw [ByteAuth.equalMask_value]; exact isMask_ite _

theorem isMask_expect (bytes : List (BitVec 8)) (offset : Nat) (expected : List (BitVec 8)) :
    IsMask (expect ByteAuth.concrete bytes offset expected) := isMask_equalMask _ _

theorem isMask_isSet (flag : List (BitVec 8)) : IsMask (isSet ByteAuth.concrete flag) := isMask_eqMask _ _

theorem isMask_top (x : BitVec 8) : IsMask (top ByteAuth.concrete x) := isMask_maskBit x 7

theorem isMask_whenever (c : Bool) {m : BitVec 8} (hm : IsMask m) : IsMask (whenever ByteAuth.concrete c m) := by
  cases c
  · exact isMask_const255
  · exact hm

theorem isMask_foldl_and_map {α : Type} (g : α → BitVec 8) (z : BitVec 8) (xs : List α) (hz : IsMask z)
    (hg : ∀ x ∈ xs, IsMask (g x)) : IsMask (xs.foldl (fun mask x => ByteAuth.concrete.and mask (g x)) z) := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih _ (isMask_and hz (hg x (by simp))) (fun y hy => hg y (by simp [hy]))

theorem isMask_all (ms : List (BitVec 8)) (h : ∀ m ∈ ms, IsMask m) : IsMask (all ByteAuth.concrete ms) := by
  have := isMask_foldl_and_map id (ByteAuth.concrete.const 255) ms isMask_const255 h
  exact this

theorem isMask_either {x y : BitVec 8} (hx : IsMask x) (hy : IsMask y) : IsMask (either ByteAuth.concrete x y) :=
  isMask_not (isMask_and (isMask_not hx) (isMask_not hy))

theorem isMask_foldl_either (ms : List (BitVec 8)) (z : BitVec 8) (hz : IsMask z) (h : ∀ m ∈ ms, IsMask m) :
    IsMask (ms.foldl (either ByteAuth.concrete) z) := by
  induction ms generalizing z with
  | nil => exact hz
  | cons m ms ih =>
      rw [List.foldl_cons]
      exact ih _ (isMask_either hz (h m (by simp))) (fun y hy => h y (by simp [hy]))

theorem isMask_any (ms : List (BitVec 8)) (h : ∀ m ∈ ms, IsMask m) : IsMask (any ByteAuth.concrete ms) :=
  isMask_foldl_either ms _ isMask_const0 h

theorem isMask_varintShape (bytes : List (BitVec 8)) (offset width : Nat) :
    IsMask (varintShape ByteAuth.concrete bytes offset width) :=
  isMask_foldl_and_map _ _ _ (isMask_not (isMask_top _)) (fun _ _ => isMask_top _)

theorem isMask_accepted (checks : List (BitVec 8)) (agreements : List (List (BitVec 8))) :
    IsMask (Establish.accepted ByteAuth.concrete checks agreements) :=
  isMask_foldl_and_map _ _ _ (isMask_foldl_and_map _ _ _ isMask_const255 (fun _ _ => isMask_eqMask _ _))
    (fun _ _ => isMask_not (isMask_equalMask _ _))

theorem isMask_prekeyMask (p : PreKeyShape) (size : Nat) (m : List (BitVec 8)) :
    IsMask (prekeyMask ByteAuth.concrete p size m) := by
  unfold prekeyMask
  apply isMask_all
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨isMask_eqMask _ _, isMask_whenever _ (isMask_and (isMask_expect _ _ _) (isMask_varintShape _ _ _)),
    isMask_expect _ _ _, isMask_expect _ _ _, isMask_expect _ _ _, isMask_expect _ _ _, isMask_varintShape _ _ _,
    isMask_expect _ _ _, isMask_varintShape _ _ _, isMask_expect _ _ _, isMask_varintShape _ _ _,
    isMask_expect _ _ _⟩

theorem isMask_signalMask (q : SignalShape) (size : Nat) (w addresses : List (BitVec 8)) :
    IsMask (signalMask ByteAuth.concrete q size w addresses) := by
  unfold signalMask
  apply isMask_all
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨isMask_eqMask _ _, isMask_expect _ _ _, isMask_expect _ _ _, isMask_varintShape _ _ _,
    isMask_expect _ _ _, isMask_varintShape _ _ _, isMask_expect _ _ _, isMask_expect _ _ _, isMask_expect _ _ _,
    isMask_not (isMask_top _), isMask_whenever _ (isMask_and (isMask_expect _ _ _) (isMask_equalMask _ _))⟩

theorem candidates_isMask (index : List (BitVec 8)) (n : Nat) (values : List (List (BitVec 8))) :
    ∀ c ∈ candidates ByteAuth.concrete index n values, IsMask c.1 := by
  induction values generalizing n with
  | nil => simp [candidates]
  | cons v vs ih =>
      intro c hc
      simp only [candidates, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact isMask_equalMask _ _
      · exact ih (n + 1) c hc

theorem isMask_selectAt (index : List (BitVec 8)) (first : Nat) (values : List (List (BitVec 8))) (width : Nat) :
    IsMask (OpenResult.get ByteAuth.concrete (selectAt ByteAuth.concrete index first values width) 0) := by
  simp only [selectAt, get_cons_zero]
  apply isMask_any
  intro m hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  exact candidates_isMask index first values c hc

theorem decodeCases_head (block : List (BitVec 8)) (counts : List Nat) :
    ∃ x xs, Unpad.decodeCases ByteAuth.concrete block counts = x :: xs ∧ IsMask x := by
  induction counts with
  | nil => exact ⟨0, List.replicate 17 0, rfl, Or.inl rfl⟩
  | cons c cs ih =>
      obtain ⟨x, xs, hx, hm⟩ := ih
      refine ⟨Unpad.chooseByte ByteAuth.concrete (Unpad.caseMask ByteAuth.concrete block c) (ByteAuth.concrete.const 255) x,
        _, by rw [Unpad.decodeCases, hx]; rfl, ?_⟩
      rcases isMask_equalMask (block.drop (16 - c)) (List.replicate c (ByteAuth.concrete.const c)) with h | h
      · rw [Unpad.caseMask, h, Unpad.chooseByte_reject]; exact hm
      · rw [Unpad.caseMask, h, Unpad.chooseByte_accept]; exact isMask_const255

theorem isMask_decode (block : List (BitVec 8)) :
    IsMask (OpenResult.get ByteAuth.concrete (Unpad.decode ByteAuth.concrete block) 0) := by
  obtain ⟨x, xs, hx, hm⟩ := decodeCases_head block ((List.range 16).map (· + 1))
  rw [Unpad.decode, hx, get_cons_zero]; exact hm

section Gating
variable (p : PreKeyShape) (q : SignalShape) (size jump : Nat)
  (message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
    sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId : List (BitVec 8))

/-- **`receive-session`'s status is 255 or 0** (so `session_rejects` covers every non-accepted
status: nothing is ever released under a partial mask). -/
theorem session_status_cases :
    (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [255] ∨
    (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [0] := by
  simp only [session, List.getD_cons_zero, OpenResult.finish, get_cons_zero, List.cons.injEq, and_true]
  refine Or.symm (isMask_and (isMask_all _ ?_) (isMask_decode _))
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨isMask_accepted _ _, isMask_prekeyMask _ _ _, isMask_equalMask _ _, isMask_equalMask _ _,
    isMask_equalMask _ _, isMask_equalMask _ _, isMask_signalMask _ _ _ _, isMask_selectAt _ _ _ _,
    isMask_selectAt _ _ _ _, isMask_equalMask _ _⟩

/-! ### `receive-text` releases nothing unless the session accepted -/

theorem foldl_and_zero (ms : List (BitVec 8)) (z : BitVec 8) (h : z = 0 ∨ (0 : BitVec 8) ∈ ms) :
    ms.foldl ByteAuth.concrete.and z = 0 := by
  induction ms generalizing z with
  | nil => simpa using h
  | cons m ms ih =>
      rw [List.foldl_cons]
      apply ih
      rcases h with rfl | h
      · left; exact zero_and' m
      · rcases List.mem_cons.mp h with rfl | h
        · left; exact BitVec.and_zero
        · right; exact h

theorem all_cons_zero (rest : List (BitVec 8)) : all ByteAuth.concrete (0 :: rest) = 0 :=
  foldl_and_zero _ _ (Or.inr (by simp))

theorem get_of_zeros (xs : List (BitVec 8)) (hz : ∀ b ∈ xs, b = 0) (i : Nat) : OpenResult.get ByteAuth.concrete xs i = 0 := by
  unfold OpenResult.get
  cases h : xs[i]? with
  | none => rfl
  | some x => exact hz x (List.mem_of_getElem? h)

/-- `receive-text` on an all-zero plaintext outputs only zeros. -/
theorem text_zero (capacity : Nat) (plain : List (BitVec 8)) (hz : ∀ b ∈ plain, b = 0) :
    ∀ field ∈ text ByteAuth.concrete capacity plain, ∀ b ∈ field, b = 0 := by
  have hget : OpenResult.get ByteAuth.concrete (plain.drop 8) 0 = 0 :=
    get_of_zeros _ (fun b hb => hz b (List.mem_of_mem_drop hb)) 0
  have h10 : ByteAuth.eqMask ByteAuth.concrete 0 (ByteAuth.concrete.const 10) = 0 := by
    rw [ByteAuth.eqMask_value]; decide
  simp only [text, hget, h10, all_cons_zero, ByteAuth.release_reject]
  intro field hf b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · simpa using hb
  · exact List.eq_of_mem_replicate hb
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb; rfl
  · exact List.eq_of_mem_replicate hb

/-- **`receive-text` is gated by `receive-session`** (definition level): if the session's status
is not 255, every output of `receive-text` on the session's plaintext is zero (status, length,
text and layout). -/
theorem text_zero_unless_accepted (capacity : Nat)
    (hne : (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] ≠ [255]) :
    ∀ field ∈ text ByteAuth.concrete capacity
        ((session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
          ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
          baseValid torsionX torsionY certificate accessKey requestId).getD 3 []),
      ∀ b ∈ field, b = 0 := by
  rcases session_status_cases p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1
    dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate
    accessKey requestId with h | h
  · exact absurd h hne
  · apply text_zero
    intro b hb
    exact ReceiveKernel.session_rejects p q size jump message checks senderIdentity ourIdentity localAddress uuid
      device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY
      certificate accessKey requestId h _ (getD_mem _ 3 (by simp [session])) b hb

end Gating

/-! ### The same at kernel level -/

section Kernels
local notation "values" => TlsMpc.ReceiveKernel.values

/-- **`receive-text` is gated by `receive-session`** (kernel level): when the `plaintext` input of
`receive-text` is the `plaintext` output of `receive-session` (the controller's wiring) and the
session's opened `status` is not 255, every output of `receive-text` (all four opened) is zero. -/
theorem receiveText_gated (cert size : Nat) (p : PreKeyShape) (q : SignalShape) (jump ciphertext capacity : Nat)
    (assign assign' : BVExpr.Assignment)
    (wired : (HybridKernel.lookup (ReceiveKernel.textInputs ciphertext) "plaintext").map (BVExpr.eval assign') =
      (values (ReceiveKernel.session cert size p q jump) assign).getD 3 [])
    (rejected : (values (ReceiveKernel.session cert size p q jump) assign).getD 0 [] ≠ [255]) :
    ∀ field ∈ values (ReceiveKernel.text ciphertext capacity) assign', ∀ b ∈ field, b = 0 := by
  have hs := ReceiveKernel.session_spec cert size p q jump assign
  have ht := ReceiveKernel.text_spec ciphertext capacity assign'
  simp only at hs ht
  rw [hs] at wired rejected
  rw [ht, wired]
  simp only [List.getD_cons_zero, List.getD_cons_succ] at wired rejected ⊢
  have hz := text_zero_unless_accepted p q size jump _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ capacity rejected
  intro field hf b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;>
    exact hz _ (getD_mem _ _ (by simp [text])) b hb

/-- What each receive kernel opens (its outputs marked `opened` or addressed to one party):
nothing beyond the fields listed in `SECURITY_MAP.md` (ops 50, 51). -/
def openedNames (k : HybridKernel.Kernel) : List String :=
  (k.outputs.filter (fun o => o.opened || o.audience != 0)).map (·.name)

theorem opened_unsealStatic (size : Nat) : openedNames (ReceiveKernel.unsealStatic size) = [] := rfl
theorem opened_unsealMessage (size : Nat) :
    openedNames (ReceiveKernel.unsealMessage size) = ["certificateLength"] := rfl
theorem opened_contentShape (size cert : Nat) : openedNames (ReceiveKernel.contentShape size cert) = ["shape"] := rfl
theorem opened_content (size cert : Nat) (hint : Bool) : openedNames (ReceiveKernel.content size cert hint) = [] := rfl
theorem opened_certificate (cert : Nat) (c : CertShape) : openedNames (ReceiveKernel.certificate cert c) = [] := rfl
theorem opened_certificateVerified : openedNames (ReceiveKernel.certificateVerified ()) = [] := rfl
theorem opened_prekeyShape (size : Nat) : openedNames (ReceiveKernel.prekeyShape size) = ["shape"] := rfl
theorem opened_prekeyOpen (size : Nat) (p : PreKeyShape) :
    openedNames (ReceiveKernel.prekeyOpen size p) =
      ["oneTimePrekeyId", "signedPrekeyId", "kyberPrekeyId", "kyberCiphertext"] := rfl
theorem opened_signalShape (size : Nat) (p : PreKeyShape) : openedNames (ReceiveKernel.signalShape size p) = ["shape"] :=
  rfl
theorem opened_session (cert size : Nat) (p : PreKeyShape) (q : SignalShape) (jump : Nat) :
    openedNames (ReceiveKernel.session cert size p q jump) = ["status"] := rfl
theorem opened_text (ciphertext capacity : Nat) :
    openedNames (ReceiveKernel.text ciphertext capacity) = ["status", "length", "text", "layout"] := rfl
theorem opened_accessKey (cert ciphertext offset : Nat) :
    openedNames (ReceiveKernel.accessKey cert ciphertext offset) = ["status"] := rfl
theorem opened_envelopePoint (size : Nat) : openedNames (ReceiveKernel.envelopePoint size) = [] := rfl

end Kernels

/-! ### `receive-certificate-verified` -/

/-- **`receive-certificate-verified` is 255 exactly when** the certificate's other checks passed
(`certificateValid` 255), the server key decoded to a curve point (`serverValid` is the field
value 1), and the point `rx, ry` (the field engine's `[s]B − [h]A` for the signature's `s` and the
challenge `h` of `receive-certificate`) compresses to the signature's `R`, with `s`'s bits 253, 254
clear (libsignal's `xeddsa` verify, `R == [s]B − [h]A`). -/
theorem certificateVerified_iff (certificateValid signature serverValid rx ry : List (BitVec 8)) :
    (certificateVerified ByteAuth.concrete certificateValid signature serverValid rx ry).getD 0 [] = [255] ↔
      OpenResult.get ByteAuth.concrete certificateValid 0 = 255 ∧
      serverValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
      signature.length = 64 ∧ rx.length = 32 ∧ ry.length = 32 ∧
      (OpenResult.get ByteAuth.concrete signature 63 &&& 127).toNat < 32 ∧
      signature.take 32 = XEdDsa.compress ByteAuth.concrete rx ry := by
  simp only [certificateVerified, List.getD_cons_zero, List.cons.injEq, and_true, concrete_and, and_eq_255,
    isSet_eq_255, Establish.signatureMask, equalMask_eq_255, XEdDsa.matchR]
  by_cases hl : signature.length = 64 ∧ rx.length = 32 ∧ ry.length = 32
  · rw [if_pos hl, and_eq_255, XEdDsa.scalarMask_spec, ite_eq_255, equalMask_eq_255]
    simp only [hl, true_and]
  · rw [if_neg hl]
    constructor
    · rintro ⟨_, _, h⟩; exact absurd h (by decide)
    · rintro ⟨_, _, h1, h2, h3, _⟩; exact absurd ⟨h1, h2, h3⟩ hl

/-! ### Sealed sender v1 (`sealed_sender.rs`, `sealed_sender_decrypt_to_usmc`, v1 arm) -/

/-- `EphemeralKeys::calculate` with `Direction::Receiving`: HKDF-SHA256 with salt
`"UnidentifiedDelivery" ‖ 05 ‖ ourIdentity ‖ ephemeral` (the envelope's bytes 3..36 are
`05 ‖ ephemeral`), input the agreement, 96 bytes: chain key, cipher key, MAC key. -/
def ephemeralKeys (ourIdentity envelope agreement : List (BitVec 8)) : List (BitVec 8) :=
  SealedSenderV1.material Sha256.concrete
    (label Sha256.concrete ++ (ByteAuth.concrete.const 5 :: ourIdentity) ++ Establish.part envelope 3 33) agreement

/-- `StaticKeys::calculate`: HKDF-SHA256 with salt `chain ‖ encryptedStatic` (all 43 bytes, MAC
included), input the agreement, 96 bytes of which the first 32 are discarded. -/
def staticKeys (envelope chain agreement : List (BitVec 8)) : List (BitVec 8) :=
  SealedSenderV1.material Sha256.concrete (chain ++ Establish.part envelope 38 43) agreement

/-- `crypto.rs`, `aes256_ctr_hmacsha256_decrypt`, the check: the last 10 bytes are the first 10
bytes of HMAC-SHA256 of the rest. -/
def macMatches (macKey sealed : List (BitVec 8)) : Prop :=
  (Sha256.hmac Sha256.concrete macKey (sealed.take (sealed.length - 10))).take 10 = sealed.drop (sealed.length - 10)

/-- `aes256_ctr_hmacsha256_decrypt`, the decryption: AES-256-CTR (zero counter block) of all but
the last 10 bytes. -/
def ctrOpen (cipherKey sealed : List (BitVec 8)) : List (BitVec 8) :=
  SealedSenderV1.ctr Aes.concrete cipherKey (sealed.take (sealed.length - 10))

theorem envelopeMask_eq_255 (size : Nat) (envelope : List (BitVec 8)) :
    envelopeMask ByteAuth.concrete size envelope = 255 ↔
      Establish.part envelope 0 4 = lit ByteAuth.concrete [17, 10, 33, 5] ∧
      Establish.part envelope 36 2 = lit ByteAuth.concrete [18, 43] ∧
      Establish.part envelope 81 (fieldHeader ByteAuth.concrete 26 (size - 81)).length =
        fieldHeader ByteAuth.concrete 26 (size - 81) := by
  simp only [envelopeMask, all_eq_255, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true, expect_eq_255, lit, List.length_map, List.length_cons, List.length_nil]

/-- **`receive-unseal-static` is valid exactly when** the envelope has the v1 layout, the
encrypted static key's 10-byte MAC verifies under the MAC key of `ephemeralKeys`, the agreement is
not all zero, and the decrypted static key starts with the key type `05`. -/
theorem unsealStatic_valid_iff (size : Nat) (ourIdentity envelope agreement : List (BitVec 8)) :
    (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 0 [] =
        [255] ↔
      envelopeMask ByteAuth.concrete size envelope = 255 ∧
      macMatches (Establish.part (ephemeralKeys ourIdentity envelope agreement) 64 32) (Establish.part envelope 38 43) ∧
      agreement ≠ List.replicate 32 0 ∧
      OpenResult.get ByteAuth.concrete
        (ctrOpen (Establish.part (ephemeralKeys ourIdentity envelope agreement) 32 32) (Establish.part envelope 38 43)) 0 =
        ByteAuth.concrete.const 5 := by
  simp only [unsealStatic, List.getD_cons_zero, List.cons.injEq, and_true, all_eq_255, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, openPart, get_cons_zero, get_cons_succ, equalMask_eq_255,
    agreementMask_eq_255, eqMask_eq_255, ephemeralKeys, macMatches, ctrOpen]

/-- **What `receive-unseal-static` outputs when valid**: the sender's identity key is the
decrypted static key without its type byte, and the chain key is the first 32 bytes of
`ephemeralKeys`. -/
theorem unsealStatic_outputs (size : Nat) (ourIdentity envelope agreement : List (BitVec 8))
    (h : (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 0 [] =
      [255]) :
    (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 1 [] =
        (ctrOpen (Establish.part (ephemeralKeys ourIdentity envelope agreement) 32 32)
          (Establish.part envelope 38 43)).drop 1 ∧
      (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 2 [] =
        (ephemeralKeys ourIdentity envelope agreement).take 32 := by
  simp only [unsealStatic, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true] at h ⊢
  rw [h, release_255, release_255]
  exact ⟨rfl, rfl⟩

/-- **`receive-unseal-message` is valid exactly when** the first half was valid, the encrypted
message's 10-byte MAC verifies under the MAC key of `staticKeys`, the agreement is not all zero,
and the decrypted UnidentifiedSenderMessageContent starts `08 type 12` followed by a two-byte
varint (the certificate's length prefix). -/
theorem unsealMessage_valid_iff (size : Nat) (envelope staticValid chain agreement : List (BitVec 8)) :
    (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 0 [] =
        [255] ↔
      OpenResult.get ByteAuth.concrete staticValid 0 = 255 ∧
      macMatches (Establish.part (staticKeys envelope chain agreement) 64 32) (envelope.drop (messageAt size)) ∧
      agreement ≠ List.replicate 32 0 ∧
      Establish.part (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size)))
        0 1 = lit ByteAuth.concrete [8] ∧
      Establish.part (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size)))
        2 1 = lit ByteAuth.concrete [18] ∧
      varintShape ByteAuth.concrete
        (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size))) 3 2 = 255 := by
  simp only [unsealMessage, List.getD_cons_zero, List.cons.injEq, and_true, all_eq_255, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, openPart, get_cons_zero, isSet_eq_255, equalMask_eq_255,
    agreementMask_eq_255, expect_eq_255, staticKeys, macMatches, ctrOpen, List.drop_one, List.tail_cons, lit,
    List.length_map, List.length_cons, List.length_nil]

/-- **What `receive-unseal-message` outputs when valid**: the content is the AES-256-CTR decryption
under `staticKeys`, and the opened `certificateLength` is its bytes 3..5 (the length prefix of
field 2, the sender certificate). -/
theorem unsealMessage_outputs (size : Nat) (envelope staticValid chain agreement : List (BitVec 8))
    (h : (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 0 [] =
      [255]) :
    (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 1 [] =
        ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size)) ∧
      (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 2 [] =
        Establish.part (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32)
          (envelope.drop (messageAt size))) 3 2 := by
  simp only [unsealMessage, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true] at h ⊢
  rw [h, release_255, release_255]
  exact ⟨rfl, rfl⟩

/-! ### `receive-prekey-open` -/

/-- **`receive-prekey-open` is valid exactly when** the content stage was valid, the message type
is PREKEY_MESSAGE (1), the PreKeySignalMessage has layout `p` (`prekeyMask`), its identity key is
the certificate's (`senderIdentity`), its base key is below `2^255 − 19` (`canonicalRange`), and
the inner SignalMessage starts with the ratchet key's header `0A 21 05`. -/
theorem prekeyOpen_valid_iff (p : PreKeyShape) (size : Nat) (message valid messageType senderIdentity : List (BitVec 8)) :
    (prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity).getD 0 [] = [255] ↔
      OpenResult.get ByteAuth.concrete valid 0 = 255 ∧
      OpenResult.get ByteAuth.concrete messageType 0 = ByteAuth.concrete.const 1 ∧
      prekeyMask ByteAuth.concrete p size message = 255 ∧
      Establish.part message (p.keysAt + 38) 32 = senderIdentity ∧
      canonicalRange ByteAuth.concrete (Establish.part message (p.keysAt + 3) 32) = 255 ∧
      Establish.part message (p.signalAt size + 1) 3 = lit ByteAuth.concrete [10, 33, 5] := by
  simp only [prekeyOpen, List.getD_cons_zero, List.cons.injEq, and_true, all_eq_255, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, isSet_eq_255, eqMask_eq_255, equalMask_eq_255, expect_eq_255, lit,
    List.length_map, List.length_cons, List.length_nil]

/-- **What `receive-prekey-open` releases when valid**: the base key and ratchet key (private), and
the opened ids and Kyber ciphertext are the message's own fields: the varint values of the
one-time, signed and Kyber prekey ids (4 bytes big endian) and the 1,568 bytes after `42 A1 0C 08`. -/
theorem prekeyOpen_outputs (p : PreKeyShape) (size : Nat) (message valid messageType senderIdentity : List (BitVec 8))
    (h : (prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity).getD 0 [] = [255]) :
    prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity =
      [[255], Establish.part message (p.keysAt + 3) 32, Establish.part message (p.signalAt size + 4) 32,
        varintValue ByteAuth.concrete (Establish.part message 2 p.oneTime),
        varintValue ByteAuth.concrete (Establish.part message (p.idsAt size + 2 + p.registration) p.signed),
        varintValue ByteAuth.concrete (Establish.part message (p.idsAt size + 3 + p.registration + p.signed) p.kyber),
        Establish.part message (p.idsAt size + 3 + p.registration + p.signed + p.kyber + 4) 1568] := by
  simp only [prekeyOpen, List.getD_cons_zero, List.cons.injEq, and_true] at h ⊢
  rw [h]
  simp only [release_255, and_self]

/-! ### One-byte varints (the counters 0..127) -/

theorem varintValue_one : ∀ b : BitVec 8,
    varintValue ByteAuth.concrete [b] = [0, 0, 0, b &&& 127] := by decide

/-- With a one-byte counter (`q.counter = 1`; `signalMask` then requires its top bit clear), the
counter's value bytes are `[0, 0, 0, b]` for the counter byte `b`, so `session_status_iff`'s `n`
is `b.toNat`. -/
theorem counterBytes_one (w : List (BitVec 8)) (hw : 37 < w.length) (q : SignalShape) (hq : q.counter = 1)
    (htop : (OpenResult.get ByteAuth.concrete w 37).toNat < 128) :
    counterBytes q w = numberBytes ByteAuth.concrete (OpenResult.get ByteAuth.concrete w 37).toNat := by
  have hpart : Establish.part w 37 1 = [OpenResult.get ByteAuth.concrete w 37] := by
    simp [Establish.part, OpenResult.get, List.getElem?_eq_getElem hw, List.take_one, List.head?_drop]
  rw [counterBytes, hq, hpart, varintValue_one]
  generalize OpenResult.get ByteAuth.concrete w 37 = b at htop
  have hb : b &&& 127 = b := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have : (127 : BitVec 8).toNat = 127 := rfl
    rw [this]
    have := Nat.and_two_pow_sub_one_eq_mod b.toNat 7
    simp only [Nat.reducePow, Nat.reduceSub] at this
    rw [this]; omega
  rw [hb]
  simp only [numberBytes, List.range, List.range.loop, List.map_cons, List.map_nil, concrete_const]
  have h0 : b.toNat / 256 ^ (3 - 0) % 256 = 0 := by simp; omega
  have h1 : b.toNat / 256 ^ (3 - 1) % 256 = 0 := by simp; omega
  have h2 : b.toNat / 256 ^ (3 - 2) % 256 = 0 := by simp; omega
  have h3 : b.toNat / 256 ^ (3 - 3) % 256 = b.toNat := by simp; omega
  rw [h0, h1, h2, h3, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-! ### Comparing big-endian numbers (`atMost`) -/

/-- The mask of a proposition. -/
def mk (P : Prop) [Decidable P] : BitVec 8 := if P then 255 else 0

theorem mk_and (P Q : Prop) [Decidable P] [Decidable Q] : ByteAuth.concrete.and (mk P) (mk Q) = mk (P ∧ Q) := by
  unfold mk; by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem mk_not (P : Prop) [Decidable P] : ByteAuth.concrete.not (mk P) = mk (¬P) := by
  unfold mk; by_cases hp : P <;> simp [hp] <;> decide

theorem mk_xor (P Q : Prop) [Decidable P] [Decidable Q] : ByteAuth.concrete.xor (mk P) (mk Q) = mk (¬(P ↔ Q)) := by
  unfold mk; by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq] <;> decide

theorem mk_either (P Q : Prop) [Decidable P] [Decidable Q] : either ByteAuth.concrete (mk P) (mk Q) = mk (P ∨ Q) := by
  simp only [either, mk_not, mk_and]
  unfold mk; by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem mk_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : mk P = mk Q := by
  unfold mk; by_cases hp : P <;> simp [hp, h.mp, (not_congr h).mp]

theorem mk_eq_255 (P : Prop) [Decidable P] : mk P = 255 ↔ P := ite_eq_255 P

theorem maskBit_mk_fin : ∀ (x : BitVec 8) (i : Fin 8), ByteAuth.concrete.maskBit x i = mk (x.getLsbD i = true) := by
  decide

theorem maskBit_mk (x : BitVec 8) (i : Nat) (hi : i < 8) : ByteAuth.concrete.maskBit x i = mk (x.getLsbD i = true) :=
  maskBit_mk_fin x ⟨i, hi⟩

/-- The bits of a byte, most significant first. -/
def byteBits (x : BitVec 8) : List Bool := [7, 6, 5, 4, 3, 2, 1, 0].map x.getLsbD

def bitsOf : List (BitVec 8) → List Bool
  | [] => []
  | x :: xs => byteBits x ++ bitsOf xs

/-- A bit string's value, most significant first. -/
def val : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + val bs

theorem val_lt (bs : List Bool) : val bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [val]
  | cons b bs ih =>
      simp only [val, List.length_cons, Nat.pow_succ]
      split <;> omega

theorem val_append (as bs : List Bool) : val (as ++ bs) = val as * 2 ^ bs.length + val bs := by
  induction as with
  | nil => simp [val]
  | cons a as ih =>
      simp only [List.cons_append, val, List.length_append, ih]
      cases a
      · simp
      · simp only [if_true]
        rw [Nat.pow_add, Nat.add_mul]
        omega

theorem val_inj (bs cs : List Bool) (hl : bs.length = cs.length) (hv : val bs = val cs) : bs = cs := by
  induction bs generalizing cs with
  | nil => cases cs <;> simp_all
  | cons b bs ih =>
      cases cs with
      | nil => simp at hl
      | cons c cs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          simp only [val] at hv
          have h1 := val_lt bs
          have h2 := val_lt cs
          rw [hl] at hv h1
          have hbc : b = c := by
            cases b <;> cases c <;> simp only [if_true, if_false, Bool.false_eq_true] at hv <;>
              first | rfl | omega
          subst hbc
          have : val bs = val cs := by omega
          rw [ih cs hl this]

theorem byteBits_length (x : BitVec 8) : (byteBits x).length = 8 := rfl

theorem val_byteBits : ∀ x : BitVec 8, val (byteBits x) = x.toNat := by decide

theorem bitsOf_length (xs : List (BitVec 8)) : (bitsOf xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [bitsOf, List.length_append, byteBits_length, ih, List.length_cons]; omega

theorem maskBits_eq (xs : List (BitVec 8)) : maskBits ByteAuth.concrete xs = (bitsOf xs).map (fun b => mk (b = true)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [maskBits, bitsOf, List.map_append, ih, byteBits, List.map_cons, List.map_nil]
      congr 1
      simp only [maskBit_mk x 7 (by decide), maskBit_mk x 6 (by decide), maskBit_mk x 5 (by decide),
        maskBit_mk x 4 (by decide), maskBit_mk x 3 (by decide), maskBit_mk x 2 (by decide),
        maskBit_mk x 1 (by decide), maskBit_mk x 0 (by decide)]

theorem compareBits_value (bs cs : List Bool) (hl : bs.length = cs.length) (L E : Prop) [Decidable L] [Decidable E] :
    compareBits ByteAuth.concrete (bs.map (fun b => mk (b = true))) (cs.map (fun b => mk (b = true))) (mk L) (mk E) =
      (mk (L ∨ (E ∧ val bs < val cs)), mk (E ∧ bs = cs)) := by
  induction bs generalizing cs L E with
  | nil =>
      cases cs with
      | nil =>
          simp only [List.map_nil, compareBits]
          congr 1
          · exact mk_congr (by simp [val])
          · exact mk_congr (by simp)
      | cons => simp at hl
  | cons b bs ih =>
      cases cs with
      | nil => simp at hl
      | cons c cs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          simp only [List.map_cons, compareBits, mk_not, mk_and, mk_xor, mk_either]
          rw [ih cs hl]
          have h1 := val_lt bs
          have h2 := val_lt cs
          rw [hl] at h1
          have f1 : val bs < 2 ^ cs.length + val cs := by omega
          have f2 : ¬ (2 ^ cs.length + val bs < val cs) := by omega
          congr 1
          · apply mk_congr
            simp only [val, hl]
            cases b <;> cases c <;> simp [f1, f2]
          · apply mk_congr
            cases b <;> cases c <;> simp

/-- **`atMost` is the big-endian comparison**: for byte strings of equal length, 255 exactly when
the value of `x` is at most the value of `y`. -/
theorem atMost_value (x y : List (BitVec 8)) (hl : x.length = y.length) :
    atMost ByteAuth.concrete x y = mk (val (bitsOf x) ≤ val (bitsOf y)) := by
  have hb : (bitsOf x).length = (bitsOf y).length := by rw [bitsOf_length, bitsOf_length, hl]
  have h0 : ByteAuth.concrete.const 0 = mk False := rfl
  have h255 : ByteAuth.concrete.const 255 = mk True := rfl
  simp only [atMost, maskBits_eq, h0, h255, compareBits_value _ _ hb, mk_either]
  apply mk_congr
  simp only [false_or, true_and]
  constructor
  · rintro (h | h)
    · omega
    · rw [h]; exact Nat.le_refl _
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr (val_inj _ _ hb h)

theorem val_bitsOf_two (a b : BitVec 8) : val (bitsOf [a, b]) = a.toNat * 256 + b.toNat := by
  simp only [bitsOf, List.append_nil, val_append, byteBits_length, val_byteBits]

/-! ### The three `-shape` kernels release nothing unless the stage before was valid -/

theorem release_isSet_zero (flag : List (BitVec 8)) (h : OpenResult.get ByteAuth.concrete flag 0 ≠ 255)
    (bytes : List (BitVec 8)) : ∀ b ∈ ByteAuth.release ByteAuth.concrete (isSet ByteAuth.concrete flag) bytes, b = 0 := by
  rw [isSet_value, if_neg h, ByteAuth.release_reject]
  intro b hb
  exact List.eq_of_mem_replicate hb

theorem contentShape_rejects (size cert : Nat) (content valid : List (BitVec 8))
    (h : OpenResult.get ByteAuth.concrete valid 0 ≠ 255) :
    ∀ field ∈ contentShape ByteAuth.concrete size cert content valid, ∀ b ∈ field, b = 0 := by
  intro field hf
  simp only [contentShape, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact release_isSet_zero valid h _

theorem prekeyShape_rejects (size : Nat) (m valid : List (BitVec 8)) (h : OpenResult.get ByteAuth.concrete valid 0 ≠ 255) :
    ∀ field ∈ prekeyShape ByteAuth.concrete size m valid, ∀ b ∈ field, b = 0 := by
  intro field hf
  simp only [prekeyShape, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact release_isSet_zero valid h _

theorem signalShape_rejects (p : PreKeyShape) (size : Nat) (m valid : List (BitVec 8))
    (h : OpenResult.get ByteAuth.concrete valid 0 ≠ 255) :
    ∀ field ∈ signalShape ByteAuth.concrete p size m valid, ∀ b ∈ field, b = 0 := by
  intro field hf
  simp only [signalShape, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact release_isSet_zero valid h _

/-! ### `receive-certificate` -/

theorem top_value : ∀ x : BitVec 8, top ByteAuth.concrete x = mk (128 ≤ x.toNat) := by decide

theorem not_zeroMask_eq_255 (x : BitVec 8) : ByteAuth.concrete.not (ByteAuth.zeroMask ByteAuth.concrete x) = 255 ↔ x ≠ 0 := by
  rw [ByteAuth.zeroMask_value]
  by_cases hx : x = 0
  · simp only [hx, if_true, ne_eq, not_true_eq_false, iff_false]; decide
  · simp only [hx, if_false, ne_eq, not_false_eq_true, iff_true]; decide

/-- **What `receive-certificate`'s validity says** (for the public shape `cert`, `c`): the content
stage was valid; the certificate's identity key is `senderIdentity` (the key decrypted from the
envelope's static part); its signer (embedded server certificate, or server id) is the trusted
`signer`; its device id is in 1..127; `now ≤ expires` (`atMost` is the big-endian comparison,
`atMost_value`); and the layout masks (field tags, lengths, the UUID's form) hold. -/
theorem certificate_valid {H R : Type} (h : XEdDsaSha512.Ops (BitVec 8) H) (r : XEdDsaScalar.Ops (BitVec 8) R)
    (cert : Nat) (c : CertShape) (bytes valid senderIdentity signer now serverX serverY : List (BitVec 8))
    (hv : (certificate ByteAuth.concrete h r cert c bytes valid senderIdentity signer now serverX serverY).getD 0 [] =
      [255]) :
    OpenResult.get ByteAuth.concrete valid 0 = 255 ∧
    Establish.part bytes (bodyAt cert + c.e164 + 14) 32 = senderIdentity ∧
    Establish.part bytes (if c.embedded then bodyAt cert + c.e164 + 48 else bodyAt cert + c.e164 + 46 + 2 + c.uuidSize + 1)
      c.signerSize = signer ∧
    (OpenResult.get ByteAuth.concrete bytes (bodyAt cert + c.e164 + 1)).toNat < 128 ∧
    OpenResult.get ByteAuth.concrete bytes (bodyAt cert + c.e164 + 1) ≠ 0 ∧
    atMost ByteAuth.concrete now (Establish.part bytes (bodyAt cert + c.e164 + 3) 8).reverse = 255 ∧
    Establish.part bytes (bodyAt cert + c.e164) 1 = lit ByteAuth.concrete [16] ∧
    Establish.part bytes (bodyAt cert + c.e164 + 2) 1 = lit ByteAuth.concrete [25] ∧
    Establish.part bytes (bodyAt cert + c.e164 + 11) 3 = lit ByteAuth.concrete [34, 33, 5] ∧
    Establish.part bytes (bodyAt cert + c.body) 2 = lit ByteAuth.concrete [18, 64] := by
  simp only [certificate, List.getD_cons_zero, List.cons.injEq, and_true, all_eq_255, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true] at hv
  obtain ⟨h0, _, _, h3, h4, h5, h6, h7, h8, h9, _, h11, _, _, h14⟩ := hv
  rw [isSet_eq_255] at h0
  rw [equalMask_eq_255] at h9 h11
  rw [expect_eq_255] at h3 h6 h8 h14
  rw [concrete_not, ← concrete_not, top_value, mk_not, mk_eq_255, Nat.not_le] at h4
  rw [not_zeroMask_eq_255] at h5
  simp only [lit, List.length_map, List.length_cons, List.length_nil] at h3 h6 h8 h14
  exact ⟨h0, h9, h11, h4, h5, h7, h3, h6, h8, h14⟩

/-! ### T13 composed: what `receive-session` status 255 says about the certificate -/

/-- **T13, accept direction, composed.** With the controller's wiring (the session's `verified`
check byte is `receive-certificate-verified`'s output on `receive-certificate`'s validity and
signature), `receive-session` status 255 implies:

* the message MAC verified under libsignal's keys for some counter `n ≤ jump` and post-quantum
  index `1 + i` (`session_status_iff`);
* the certificate's validity checks passed (`certificate_valid`: identity key, trusted signer,
  device id, expiry, layout);
* the server key decoded to a curve point and the signature's `R` is the compression of the field
  engine's `[s]B − [h]A` (`rx`, `ry`) with `s < 2^253` (`certificateVerified_iff`), where `h` is
  `receive-certificate`'s challenge over the certificate body. -/
theorem session_accept_certificate {H R : Type} (hh : XEdDsaSha512.Ops (BitVec 8) H) (rr : XEdDsaScalar.Ops (BitVec 8) R)
    (p : PreKeyShape) (q : SignalShape) (size jump : Nat) (hjump : jump ≤ 16)
    (message prekeyValid senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
      sendAgreement ratchetPublic baseValid torsionX torsionY certificate' accessKey requestId : List (BitVec 8))
    (cert : Nat) (c : CertShape) (bytes contentValid signer now serverX serverY serverValid rx ry : List (BitVec 8))
    (h : (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message
      (prekeyValid ++ (certificateVerified ByteAuth.concrete
        ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 [])
        ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 3 [])
        serverValid rx ry).getD 0 [])
      senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
      ratchetPublic baseValid torsionX torsionY certificate' accessKey requestId).getD 0 [] = [255]) :
    (∃ n, (n ≤ jump ∧ counterBytes q (signalWire p size message) = numberBytes ByteAuth.concrete n) ∧
      ∃ i, (i ≤ jump ∧ pqIndexBytes q (p.signalSize size) (signalWire p size message) =
          numberBytes ByteAuth.concrete (1 + i)) ∧
        MessageMac.tag Sha256.concrete
            (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.macKey
            senderIdentity ourIdentity (MessageMac.content (signalWire p size message)) =
          MessageMac.receivedTag (signalWire p size message)) ∧
    (certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 [] =
      [255] ∧
    Establish.part bytes (bodyAt cert + c.e164 + 14) 32 = senderIdentity ∧
    Establish.part bytes (if c.embedded then bodyAt cert + c.e164 + 48 else bodyAt cert + c.e164 + 46 + 2 + c.uuidSize + 1)
      c.signerSize = signer ∧
    atMost ByteAuth.concrete now (Establish.part bytes (bodyAt cert + c.e164 + 3) 8).reverse = 255 ∧
    serverValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
    (OpenResult.get ByteAuth.concrete (Establish.part bytes (bodyAt cert + c.body + 2) 64) 63 &&& 127).toNat < 32 ∧
    (Establish.part bytes (bodyAt cert + c.body + 2) 64).take 32 = XEdDsa.compress ByteAuth.concrete rx ry := by
  obtain ⟨⟨hchecks, -⟩, n, hn, i, hi, hmac, -⟩ := (session_status_iff p q size jump message _ senderIdentity ourIdentity
    localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX
    torsionY certificate' accessKey requestId hjump).mp h
  -- the `verified` byte is 255
  have hver : (certificateVerified ByteAuth.concrete
      ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 [])
      ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 3 [])
      serverValid rx ry).getD 0 [] = [255] := by
    simp only [certificateVerified, List.getD_cons_zero] at hchecks ⊢
    rw [hchecks _ (List.mem_append_right _ (List.mem_singleton_self _))]
  obtain ⟨hcv, hsv, _, _, _, hs, hR⟩ := (certificateVerified_iff _ _ _ _ _).mp hver
  have hcert : (certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 []
      = [255] := by
    have e : (certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 []
        = [OpenResult.get ByteAuth.concrete ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity
          signer now serverX serverY).getD 0 []) 0] := by
      simp only [certificate, List.getD_cons_zero, get_cons_zero]
    rw [e, hcv]
  obtain ⟨_, hid, hsigner, _, _, hexp, _⟩ := certificate_valid hh rr cert c bytes contentValid senderIdentity signer now
    serverX serverY hcert
  have hsig : (certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 3 []
      = Establish.part bytes (bodyAt cert + c.body + 2) 64 := by
    simp only [certificate, List.getD_cons_succ, List.getD_cons_zero]
  rw [hsig] at hs hR
  exact ⟨⟨n, hn, i, hi, hmac⟩, hcert, hid, hsigner, hexp, hsv, hs, hR⟩

end TlsMpc.KernelSpecs.ReceiveAccept
