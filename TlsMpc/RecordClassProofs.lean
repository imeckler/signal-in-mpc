import TlsMpc.RecordClassKernels

/-!
Theorems about the size-class record kernels (`TlsMpc/RecordClassKernels.lean`).

* `openParsed_refines`, `sealCiphertext_refines`: the compiled expressions
  evaluate to the same functions on values.
* `openParsed_padded`: on a record followed by `k` zero bytes, with `size` the
  record's own length field, the parse the class kernel hands to the
  post-handshake parser is the parse `tls-open-application-ctr` hands to it for
  the record alone, followed by `k` zero bytes. Every check of the exact-size
  kernel (header encoding, tag mask, inner type) is in it unchanged.
* `core_padded`: the post-handshake parser gives the same event, state and
  length for a parse followed by zero bytes, and the same content followed by
  zero bytes, whenever the parse's length field is within its content (which
  `TlsInner.spec` guarantees: `spec_length_fits`).
* `sealCiphertext_padded`: for a content of `n` bytes followed by ANY `k` bytes,
  with `size` = `n + 17`, the ciphertext is the CTR encryption of the content
  and its type byte — what `tls-seal-ctr 23 n 0` opens — followed by `k` zero
  bytes, and the length is accepted.
-/
namespace TlsMpc.RecordClass
open Std.Tactic.BVDecide
open TlsWebSocketActivity (maskSpec)

/-! ### From expressions to values -/

section Refinement
variable {g : Gcm.Ops B W} {g' : Gcm.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {fb : B → B'} {fw : W → W'} (hg : Gcm.Hom g g' fb fw) (ha : ByteAuth.Hom a a' fb)
include ha

theorem maskBytes_map (masks bytes : List B) :
    (maskBytes a masks bytes).map fb = maskBytes a' (masks.map fb) (bytes.map fb) := by
  induction masks generalizing bytes with
  | nil => simp [maskBytes]
  | cons m ms ih =>
      cases bytes with
      | nil => simp [maskBytes]
      | cons b bs => simp [maskBytes, ha.and, ih]

theorem within_fst_map (high low : B) (offset count : Nat) :
    fb (within a high low offset count).1 = (within a' (fb high) (fb low) offset count).1 :=
  congrArg Prod.fst (TlsWebSocketUpgrade.activity_map ha high low offset count)

theorem within_snd_map (high low : B) (offset count : Nat) :
    (within a high low offset count).2.map fb = (within a' (fb high) (fb low) offset count).2 :=
  congrArg Prod.snd (TlsWebSocketUpgrade.activity_map ha high low offset count)

theorem place_map (content below upTo : List B) :
    (place a content below upTo).map fb = place a' (content.map fb) (below.map fb) (upTo.map fb) := by
  induction content generalizing below upTo with
  | nil => cases upTo <;> simp [place, ha.and, ha.const]
  | cons c cs ih =>
      cases below with
      | nil => simp [place]
      | cons l ls =>
          cases upTo with
          | nil => simp [place]
          | cons h hs => simp [place, ha.and, ha.xor, ha.const, ih]

include hg

theorem openParsed_map (expanded nonce wire : List B) (high low accepted : B) :
    (openParsed g a expanded nonce wire high low accepted).map fb =
      openParsed g' a' (expanded.map fb) (nonce.map fb) (wire.map fb) (fb high) (fb low) (fb accepted) := by
  have hc : TlsReceive.ciphertext (wire.map fb) = (TlsReceive.ciphertext wire).map fb := by
    simp [TlsReceive.ciphertext, List.map_take, List.map_drop]
  simp only [openParsed, openPlaintext, TlsReceive.releaseOpened_map ha, GcmOpen.Opened.map, ha.and,
    ByteAuth.equalMask_map ha, maskBytes_map ha, Gcm.ctr_map hg, List.map_take, List.map_cons, List.map_nil,
    hg.aes.const, hc, List.length_map, within_fst_map ha, within_snd_map ha]

theorem sealCiphertext_map (expanded nonce content : List B) (high low : B) :
    (fb (sealCiphertext g a expanded nonce content high low).1,
      (sealCiphertext g a expanded nonce content high low).2.map fb) =
      sealCiphertext g' a' (expanded.map fb) (nonce.map fb) (content.map fb) (fb high) (fb low) := by
  simp only [sealCiphertext, maskBytes_map ha, Gcm.ctr_map hg, place_map ha, List.length_map,
    within_fst_map ha, within_snd_map ha]

end Refinement

theorem openParsed_refines (expanded nonce wire : List (BVExpr 8)) (high low accepted : BVExpr 8)
    (assign : BVExpr.Assignment) :
    (openParsed Gcm.symbolic ByteAuth.symbolic expanded nonce wire high low accepted).map (BVExpr.eval assign) =
      openParsed Gcm.concrete ByteAuth.concrete (expanded.map (BVExpr.eval assign)) (nonce.map (BVExpr.eval assign))
        (wire.map (BVExpr.eval assign)) (BVExpr.eval assign high) (BVExpr.eval assign low)
        (BVExpr.eval assign accepted) :=
  openParsed_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign) expanded nonce wire high low accepted

theorem sealCiphertext_refines (expanded nonce content : List (BVExpr 8)) (high low : BVExpr 8)
    (assign : BVExpr.Assignment) :
    (BVExpr.eval assign (sealCiphertext Gcm.symbolic ByteAuth.symbolic expanded nonce content high low).1,
      (sealCiphertext Gcm.symbolic ByteAuth.symbolic expanded nonce content high low).2.map (BVExpr.eval assign)) =
      sealCiphertext Gcm.concrete ByteAuth.concrete (expanded.map (BVExpr.eval assign))
        (nonce.map (BVExpr.eval assign)) (content.map (BVExpr.eval assign)) (BVExpr.eval assign high)
        (BVExpr.eval assign low) :=
  sealCiphertext_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign) expanded nonce content high low

/-! ### Masks -/

private theorem and_on (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem and_off (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and

theorem maskBytes_zero (bytes : List (BitVec 8)) :
    maskBytes ByteAuth.concrete (List.replicate bytes.length 0) bytes = List.replicate bytes.length 0 := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => simp only [List.length_cons, List.replicate_succ, maskBytes, and_off, ih]

/-- Bytes under an all-ones mask are kept; what follows is masked by the rest. -/
theorem maskBytes_ones (kept rest masks : List (BitVec 8)) :
    maskBytes ByteAuth.concrete (List.replicate kept.length 255 ++ masks) (kept ++ rest) =
      kept ++ maskBytes ByteAuth.concrete masks rest := by
  induction kept with
  | nil => rfl
  | cons b bs ih => simp only [List.length_cons, List.replicate_succ, List.cons_append, maskBytes, and_on, ih]

theorem maskBytes_split (kept rest : List (BitVec 8)) :
    maskBytes ByteAuth.concrete (List.replicate kept.length 255 ++ List.replicate rest.length 0) (kept ++ rest) =
      kept ++ List.replicate rest.length 0 := by
  rw [maskBytes_ones, maskBytes_zero]

theorem maskSpec_past (offset count length : Nat) (h : length ≤ offset) :
    maskSpec offset count length = List.replicate count 0 := by
  induction count generalizing offset with
  | zero => rfl
  | succ n ih =>
      have hf : ¬(offset < length ∧ length ≤ offset + (n + 1)) := by omega
      simp only [maskSpec, if_neg hf, ih (offset + 1) (by omega), List.replicate_succ]

theorem maskSpec_split (offset m k : Nat) :
    maskSpec offset (m + k) (offset + m) = List.replicate m 255 ++ List.replicate k 0 := by
  induction m generalizing offset with
  | zero => simpa using maskSpec_past offset k offset (Nat.le_refl _)
  | succ m ih =>
      have hc : m + 1 + k = (m + k) + 1 := by omega
      have ht : offset < offset + (m + 1) ∧ offset + (m + 1) ≤ offset + (m + k + 1) := by omega
      have hl : offset + (m + 1) = (offset + 1) + m := by omega
      rw [hc]
      simp only [maskSpec, if_pos ht]
      rw [hl, ih (offset + 1), List.replicate_succ, List.cons_append]

/-- A length that is `m` past the offset, in a field of `m + k` bytes: it fits,
and the masks are `m` ones then `k` zeros. -/
theorem within_value (high low : BitVec 8) (offset m k : Nat) (hb : offset + (m + k) < 65536)
    (hl : TlsPrivateSeal.lengthValue high low = offset + m) :
    within ByteAuth.concrete high low offset (m + k) = (255, List.replicate m 255 ++ List.replicate k 0) := by
  have h1 := TlsWebSocketActivity.activity_valid high low offset (m + k) hb
  have h2 := TlsWebSocketActivity.activity_masks high low offset (m + k) hb
  rw [hl] at h1 h2
  rw [maskSpec_split] at h2
  have hv : offset ≤ offset + m ∧ offset + m ≤ offset + (m + k) := by omega
  rw [if_pos hv] at h1
  exact Prod.ext h1 h2

/-! ### CTR on a prefix -/

theorem ctrLoop_nil (o : Gcm.Ops B W) (expanded nonce : List B) (n counter : Nat) :
    Gcm.ctrLoop o expanded nonce n counter [] = [] := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih => simp [Gcm.ctrLoop, Aes.addRoundKey, ih]

/-- Blocks beyond the content add nothing. -/
theorem ctrLoop_more (o : Gcm.Ops B W) (expanded nonce : List B) (n extra counter : Nat) (content : List B)
    (hc : content.length ≤ 16 * n) :
    Gcm.ctrLoop o expanded nonce (n + extra) counter content = Gcm.ctrLoop o expanded nonce n counter content := by
  induction n generalizing counter content with
  | zero =>
      have : content = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [ctrLoop_nil, ctrLoop_nil]
  | succ n ih =>
      have hd : (content.drop 16).length ≤ 16 * n := by simp only [List.length_drop]; omega
      have hn : n + 1 + extra = (n + extra) + 1 := by omega
      rw [hn]
      simp only [Gcm.ctrLoop, ih (counter + 1) (content.drop 16) hd]

theorem zipWith_prefix (f : α → β → γ) (xs ys : List α) (zs : List β) :
    (List.zipWith f (xs ++ ys) zs).take xs.length = List.zipWith f xs zs := by
  induction xs generalizing zs with
  | nil => simp
  | cons x xs ih =>
      cases zs with
      | nil => simp
      | cons z zs => simp [ih]

/-- The keystream is applied position by position: the first bytes of the
result depend only on the first bytes of the content. -/
theorem ctrLoop_prefix (o : Gcm.Ops B W) (expanded nonce : List B) (he : expanded.length = 176)
    (n counter : Nat) (xs ys : List B) :
    (Gcm.ctrLoop o expanded nonce n counter (xs ++ ys)).take xs.length =
      Gcm.ctrLoop o expanded nonce n counter xs := by
  induction n generalizing counter xs with
  | zero => simp [Gcm.ctrLoop]
  | succ n ih =>
      have hs : (Aes.encryptExpanded o.aes 10 expanded (nonce ++ Gcm.encodeNat o 4 counter)).length = 16 :=
        Aes.encryptExpanded_length o.aes 10 _ _ (by simpa using he)
      simp only [Gcm.ctrLoop]
      by_cases hx : 16 ≤ xs.length
      · have hl : (Aes.addRoundKey o.aes (xs.take 16)
            (Aes.encryptExpanded o.aes 10 expanded (nonce ++ Gcm.encodeNat o 4 counter))).length = 16 := by
          simp only [Aes.addRoundKey, List.length_zipWith, List.length_take, hs]; omega
        have hd : (xs.drop 16).length = xs.length - 16 := by simp
        rw [List.take_append_of_le_length hx, List.drop_append_of_le_length hx, List.take_append,
          List.take_of_length_le (by omega), hl, ← hd, ih]
      · have hx' : xs.length ≤ 16 := by omega
        have ht : (xs ++ ys).take 16 = xs ++ ys.take (16 - xs.length) := by
          rw [List.take_append, List.take_of_length_le hx']
        have hl : xs.length ≤ (Aes.addRoundKey o.aes (xs ++ ys.take (16 - xs.length))
            (Aes.encryptExpanded o.aes 10 expanded (nonce ++ Gcm.encodeNat o 4 counter))).length := by
          simp only [Aes.addRoundKey, List.length_zipWith, List.length_append, List.length_take, hs]; omega
        rw [ht, List.take_append_of_le_length hl, List.take_of_length_le hx', List.drop_of_length_le hx',
          ctrLoop_nil, List.append_nil]
        exact zipWith_prefix _ _ _ _

/-- CTR of a content followed by more bytes starts with CTR of the content. -/
theorem ctr_prefix (o : Gcm.Ops B W) (expanded nonce : List B) (he : expanded.length = 176) (xs ys : List B) :
    Gcm.ctr o expanded nonce (xs ++ ys) =
      Gcm.ctr o expanded nonce xs ++ (Gcm.ctr o expanded nonce (xs ++ ys)).drop xs.length := by
  have hn : (xs ++ ys).length + 15 = (xs.length + 15) + ys.length := by simp only [List.length_append]; omega
  have hm : ((xs ++ ys).length + 15) / 16 = (xs.length + 15) / 16 + (((xs ++ ys).length + 15) / 16 - (xs.length + 15) / 16) := by
    have : (xs.length + 15) / 16 ≤ ((xs ++ ys).length + 15) / 16 := by
      rw [hn]; exact Nat.div_le_div_right (by omega)
    omega
  have hp : (Gcm.ctr o expanded nonce (xs ++ ys)).take xs.length = Gcm.ctr o expanded nonce xs := by
    unfold Gcm.ctr
    rw [ctrLoop_prefix o expanded nonce he, hm, ctrLoop_more o expanded nonce _ _ _ xs (by omega)]
  rw [← hp, List.take_append_drop]

/-! ### Opening a record that is followed by zero bytes -/

theorem replicate_add (m k : Nat) (x : α) : List.replicate (m + k) x = List.replicate m x ++ List.replicate k x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : m + 1 + k = (m + k) + 1 := by omega
      rw [h, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

theorem splitSpec_padded (bytes : List (BitVec 8)) (k : Nat) :
    TlsInner.splitSpec (bytes ++ List.replicate k 0) = TlsInner.splitSpec bytes := by
  induction bytes with
  | nil =>
      induction k with
      | zero => rfl
      | succ k ih =>
          simp only [List.nil_append] at ih
          simp only [List.nil_append, List.replicate_succ, TlsInner.splitSpec, ih, ↓reduceIte]
  | cons b bs ih => simp only [List.cons_append, TlsInner.splitSpec, ih]

/-- TLS record padding: zero bytes after the inner plaintext change nothing but the buffer size. -/
theorem spec_padded (bytes : List (BitVec 8)) (k : Nat) :
    TlsInner.spec (bytes ++ List.replicate k 0) = TlsInner.spec bytes ++ List.replicate k 0 := by
  unfold TlsInner.spec
  rw [splitSpec_padded]
  have hz : List.replicate ((bytes ++ List.replicate k (0 : BitVec 8)).length + 4) (0 : BitVec 8) =
      List.replicate (bytes.length + 4) 0 ++ List.replicate k 0 := by
    rw [← replicate_add]; congr 1; simp only [List.length_append, List.length_replicate]; omega
  cases hs : TlsInner.splitSpec bytes with
  | none => exact hz
  | some pair =>
      obtain ⟨content, kind⟩ := pair
      have hl := TlsInner.splitSpec_length bytes content kind hs
      have hc : (bytes ++ List.replicate k (0 : BitVec 8)).length - content.length = (bytes.length - content.length) + k := by
        simp only [List.length_append, List.length_replicate]; omega
      simp only
      split
      · rw [hc, replicate_add]; simp only [List.append_assoc]
      · exact hz

/-- What the parse's length field says, as the post-handshake parser reads it. -/
def lengthField (parsed : List (BitVec 8)) : Nat := TlsPrivateSeal.lengthValue (parsed.getD 2 0) (parsed.getD 3 0)

/-- The inner parser's length is within its content buffer. -/
theorem spec_length_fits (bytes : List (BitVec 8)) : lengthField (TlsInner.spec bytes) ≤ bytes.length := by
  unfold TlsInner.spec lengthField TlsPrivateSeal.lengthValue
  cases hs : TlsInner.splitSpec bytes with
  | none => simp [List.getD]
  | some pair =>
      obtain ⟨content, kind⟩ := pair
      have hl := TlsInner.splitSpec_length bytes content kind hs
      simp only
      split
      · simp only [List.cons_append, List.getD_cons_succ, List.getD_cons_zero, BitVec.toNat_ofNat]
        omega
      · simp [List.getD]

theorem ciphertext_padded (wire : List (BitVec 8)) (k : Nat) (hn : 21 ≤ wire.length) :
    ∃ tail, tail.length = k ∧
      TlsReceive.ciphertext (wire ++ List.replicate k 0) = TlsReceive.ciphertext wire ++ tail := by
  refine ⟨(((wire ++ List.replicate k (0 : BitVec 8)).drop 5).drop (wire.length - 21)).take k, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop, List.length_append, List.length_replicate]; omega
  · have h1 : (wire ++ List.replicate k (0 : BitVec 8)).length - 21 = (wire.length - 21) + k := by
      simp only [List.length_append, List.length_replicate]; omega
    unfold TlsReceive.ciphertext
    rw [h1, List.take_add]
    congr 1
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem encodeNat_value (high low : BitVec 8) :
    Gcm.encodeNat Gcm.concrete 2 (TlsPrivateSeal.lengthValue high low) = [high, low] := by
  have hh : BitVec.ofNat 8 ((256 * high.toNat + low.toNat) / 256) = high := by
    apply BitVec.eq_of_toNat_eq
    have := high.isLt; have := low.isLt
    simp only [BitVec.toNat_ofNat]; omega
  have hlow : BitVec.ofNat 8 (256 * high.toNat + low.toNat) = low := by
    apply BitVec.eq_of_toNat_eq
    have := low.isLt
    simp only [BitVec.toNat_ofNat]; omega
  simp only [Gcm.encodeNat, Gcm.concrete, Aes.concrete, TlsPrivateSeal.lengthValue, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil]
  simp [hh, hlow]

theorem releaseOpened_padded (mask accepted : BitVec 8) (plaintext : List (BitVec 8)) (k : Nat) :
    TlsReceive.releaseOpened ByteAuth.concrete mask ⟨accepted, plaintext ++ List.replicate k 0⟩ =
      TlsReceive.releaseOpened ByteAuth.concrete mask ⟨accepted, plaintext⟩ ++ List.replicate k 0 := by
  have hz : ∀ x : BitVec 8, ByteAuth.concrete.and x 0 = 0 := fun _ => BitVec.and_zero
  simp only [TlsReceive.releaseOpened, TlsInnerParallel.decode_spec, spec_padded, ByteAuth.release, List.map_append,
    List.map_replicate, hz]

/-- The parse `tls-open-application-ctr` hands to the post-handshake parser, on values. -/
def exactParsed (expanded nonce wire : List (BitVec 8)) (accepted : BitVec 8) : List (BitVec 8) :=
  TlsReceive.releaseOpened ByteAuth.concrete
    (ByteAuth.equalMask ByteAuth.concrete (wire.take 5)
      (TlsRecord.header Gcm.concrete ((TlsReceive.ciphertext wire).length + 16)))
    ⟨accepted, Gcm.ctr Gcm.concrete expanded nonce (TlsReceive.ciphertext wire)⟩

/-- A record followed by `k` zero bytes, with its own length field as `size`:
the class kernel's parse is the exact-size kernel's parse followed by `k` zero
bytes. -/
theorem openParsed_padded (expanded nonce wire : List (BitVec 8)) (high low accepted : BitVec 8) (k : Nat)
    (he : expanded.length = 176) (hn : 22 ≤ wire.length) (hb : wire.length + k < 65536)
    (hs : TlsPrivateSeal.lengthValue high low = wire.length - 5) :
    openParsed Gcm.concrete ByteAuth.concrete expanded nonce (wire ++ List.replicate k 0) high low accepted =
      exactParsed expanded nonce wire accepted ++ List.replicate k 0 := by
  obtain ⟨tail, htl, hct⟩ := ciphertext_padded wire k (by omega)
  have hlen : (TlsReceive.ciphertext wire).length = wire.length - 21 := TlsReceive.ciphertext_length wire
  have hw := within_value high low 16 (TlsReceive.ciphertext wire).length k (by omega) (by omega)
  have hctr := ctr_prefix Gcm.concrete expanded nonce he (TlsReceive.ciphertext wire) tail
  have hkept : (Gcm.ctr Gcm.concrete expanded nonce (TlsReceive.ciphertext wire)).length =
      (TlsReceive.ciphertext wire).length := Gcm.ctr_length Gcm.concrete _ _ _ he
  have hrest : ((Gcm.ctr Gcm.concrete expanded nonce (TlsReceive.ciphertext wire ++ tail)).drop
      (TlsReceive.ciphertext wire).length).length = k := by
    rw [List.length_drop, Gcm.ctr_length Gcm.concrete _ _ _ he, List.length_append]; omega
  have hsplit := maskBytes_split (Gcm.ctr Gcm.concrete expanded nonce (TlsReceive.ciphertext wire))
    ((Gcm.ctr Gcm.concrete expanded nonce (TlsReceive.ciphertext wire ++ tail)).drop (TlsReceive.ciphertext wire).length)
  rw [hkept, hrest, ← hctr] at hsplit
  have hplain : openPlaintext Gcm.concrete ByteAuth.concrete expanded nonce (wire ++ List.replicate k 0) high low =
      (255, Gcm.ctr Gcm.concrete expanded nonce (TlsReceive.ciphertext wire) ++ List.replicate k 0) := by
    simp only [openPlaintext, hct, List.length_append, htl, hw, hsplit]
  have hheader : TlsRecord.header Gcm.concrete ((TlsReceive.ciphertext wire).length + 16) =
      [Gcm.concrete.aes.const 23, Gcm.concrete.aes.const 3, Gcm.concrete.aes.const 3, high, low] := by
    have hv : (TlsReceive.ciphertext wire).length + 16 = TlsPrivateSeal.lengthValue high low := by omega
    rw [hv, TlsRecord.header, encodeNat_value]; rfl
  unfold openParsed exactParsed
  rw [hplain, hheader, List.take_append_of_le_length (by omega), releaseOpened_padded]
  simp only [and_on]

/-! ### The post-handshake parser on a parse followed by zero bytes -/

section Parser
open TlsPostHandshake Signal.Word64

theorem choose_off (yes no : Scan (BitVec 8) (BitVec 64)) : choose concrete ByteAuth.concrete 0 yes no = no := by
  simp only [choose, TlsInner.select_reject, select_reject]

theorem scan_append (enabled : BitVec 8) (length : BitVec 64) (index : Nat) (xs ys : List (BitVec 8))
    (state : Scan (BitVec 8) (BitVec 64)) :
    scan concrete ByteAuth.concrete enabled length index (xs ++ ys) state =
      scan concrete ByteAuth.concrete enabled length (index + xs.length) ys
        (scan concrete ByteAuth.concrete enabled length index xs state) := by
  induction xs generalizing index state with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, scan, ih, List.length_cons]
      congr 1; omega

/-- Bytes at or beyond the stated length are not scanned. -/
theorem scan_past (enabled : BitVec 8) (length : BitVec 64) (index : Nat) (ys : List (BitVec 8))
    (state : Scan (BitVec 8) (BitVec 64)) (hl : length.toNat ≤ index) (hb : index + ys.length < 2 ^ 64) :
    scan concrete ByteAuth.concrete enabled length index ys state = state := by
  induction ys generalizing index with
  | nil => rfl
  | cons y ys ih =>
      have hu : concrete.ule (concrete.const (index + 1)) length = 0 := by
        rw [ule_value]
        have hc : (concrete.const (index + 1)).toNat = index + 1 := by
          show (BitVec.ofNat 64 (index + 1)).toNat = index + 1
          simp only [BitVec.toNat_ofNat, List.length_cons] at hb ⊢; omega
        rw [hc, if_neg (by omega)]
      have ha : ByteAuth.concrete.and enabled 0 = 0 := BitVec.and_zero
      simp only [scan, hu, ha, choose_off]
      exact ih (index + 1) (by omega) (by simp only [List.length_cons] at hb; omega)

theorem get_padded (xs : List (BitVec 8)) (k index : Nat) :
    TlsPostHandshake.get ByteAuth.concrete (xs ++ List.replicate k 0) index =
      TlsPostHandshake.get ByteAuth.concrete xs index := by
  simp only [TlsPostHandshake.get, List.getElem?_append, List.getElem?_replicate]
  split
  · rfl
  · rename_i h
    rw [List.getElem?_eq_none (by omega)]
    split <;> rfl

theorem ule_fits (length : BitVec 64) (n : Nat) (h : length.toNat ≤ n) (hb : n < 2 ^ 64) :
    concrete.ule length (concrete.const n) = 255 := by
  rw [ule_value]
  have hc : (concrete.const n).toNat = n := by
    show (BitVec.ofNat 64 n).toNat = n
    simp only [BitVec.toNat_ofNat]; omega
  rw [hc, if_pos h]

theorem pack_length (p2 p3 : BitVec 8) :
    (concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [p2, p3])).toNat =
      TlsPrivateSeal.lengthValue p2 p3 := by
  have h : concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [p2, p3]) =
      (((0#8 ++ 0#8) ++ (0#8 ++ 0#8)) ++ ((0#8 ++ 0#8) ++ (p2 ++ p3)) : BitVec 64) := rfl
  have h2 := p2.isLt
  have h3 := p3.isLt
  rw [h]
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, TlsPrivateSeal.lengthValue]
  simp
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

theorem finish_padded (s : State (BitVec 8) (BitVec 64)) (p0 p1 p2 p3 : BitVec 8) (content : List (BitVec 8)) (k : Nat)
    (after : Scan (BitVec 8) (BitVec 64))
    (hfit : (concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [p2, p3])).toNat ≤ content.length)
    (hb : content.length + k < 2 ^ 64) :
    finish concrete ByteAuth.concrete s (p0 :: p1 :: p2 :: p3 :: (content ++ List.replicate k 0)) after =
      finish concrete ByteAuth.concrete s (p0 :: p1 :: p2 :: p3 :: content) after ++ List.replicate k 0 := by
  have hu1 := ule_fits _ content.length hfit (by omega)
  have hu2 := ule_fits (concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [p2, p3])) (content.length + k)
    (by omega) hb
  have hg : (content ++ List.replicate k 0)[1]?.getD (ByteAuth.concrete.const 0) =
      content[1]?.getD (ByteAuth.concrete.const 0) := get_padded content k 1
  have hz : ∀ x : BitVec 8, ByteAuth.concrete.and x 0 = 0 := fun _ => BitVec.and_zero
  simp only [finish, TlsPostHandshake.get, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, List.length_append,
    List.length_replicate, hu1, hu2, hg, ByteAuth.release, List.map_append, List.map_replicate, hz,
    List.append_assoc, List.cons_append, List.map_cons, List.nil_append]

/-- The post-handshake parser on a parse followed by `k` zero bytes: the same
event, request flag, parser state and length, and the same content followed by
`k` zero bytes — provided the parse's length field is within its content. -/
theorem process_padded (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8)) (k : Nat)
    (h4 : 4 ≤ parsed.length) (hfit : lengthField parsed ≤ parsed.length - 4) (hb : parsed.length + k < 2 ^ 64) :
    process concrete ByteAuth.concrete s (parsed ++ List.replicate k 0) =
      process concrete ByteAuth.concrete s parsed ++ List.replicate k 0 := by
  match parsed, h4, hfit, hb with
  | p0 :: p1 :: p2 :: p3 :: content, _, hfit, hb =>
      have hfit' : (concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [p2, p3])).toNat ≤
          content.length := by
        rw [pack_length]; simpa [lengthField] using hfit
      simp only [List.length_cons] at hb
      simp only [process, TlsPostHandshake.get, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, List.drop_succ_cons, List.drop_zero]
      rw [scan_append, scan_past _ _ _ _ _ (by simpa using hfit') (by simp only [List.length_replicate]; omega)]
      exact finish_padded s p0 p1 p2 p3 content k _ hfit' (by omega)

theorem core_padded (state parsed : List (BitVec 8)) (k : Nat)
    (h4 : 4 ≤ parsed.length) (hfit : lengthField parsed ≤ parsed.length - 4) (hb : parsed.length + k < 2 ^ 64) :
    core concrete ByteAuth.concrete state (parsed ++ List.replicate k 0) =
      core concrete ByteAuth.concrete state parsed ++ List.replicate k 0 :=
  process_padded _ parsed k h4 hfit hb

end Parser

theorem lengthField_release (mask : BitVec 8) (bytes : List (BitVec 8)) :
    lengthField (ByteAuth.release ByteAuth.concrete mask bytes) ≤ lengthField bytes := by
  have hand : ∀ x : BitVec 8, (ByteAuth.concrete.and mask x).toNat ≤ x.toNat := fun x => by
    show (mask &&& x).toNat ≤ x.toNat
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have hget : ∀ i, ((ByteAuth.release ByteAuth.concrete mask bytes).getD i 0).toNat ≤ (bytes.getD i 0).toNat := fun i => by
    simp only [ByteAuth.release, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bytes[i]? with
    | none => simp
    | some x => exact hand x
  have h2 := hget 2
  have h3 := hget 3
  unfold lengthField TlsPrivateSeal.lengthValue
  omega

/-- The whole of `tls-open-application-class` after its inputs, on values: for
a record followed by `k` zero bytes and its own length field as `size`, the
parser's output is what it is for the exact-size kernel's parse of the record
alone (`exactParsed`), followed by `k` zero bytes. So the opened event, the
next parser state and the private length are the same, and the private content
is the same bytes followed by `k` zero bytes. -/
theorem open_padded (state expanded nonce wire : List (BitVec 8)) (high low accepted : BitVec 8) (k : Nat)
    (he : expanded.length = 176) (hn : 22 ≤ wire.length) (hb : wire.length + k < 65536)
    (hs : TlsPrivateSeal.lengthValue high low = wire.length - 5) :
    TlsPostHandshake.core Signal.Word64.concrete ByteAuth.concrete state
        (openParsed Gcm.concrete ByteAuth.concrete expanded nonce (wire ++ List.replicate k 0) high low accepted) =
      TlsPostHandshake.core Signal.Word64.concrete ByteAuth.concrete state (exactParsed expanded nonce wire accepted) ++
        List.replicate k 0 := by
  rw [openParsed_padded expanded nonce wire high low accepted k he hn hb hs]
  have hlen : (exactParsed expanded nonce wire accepted).length = (TlsReceive.ciphertext wire).length + 4 := by
    simp only [exactParsed, TlsReceive.releaseOpened, ByteAuth.release, List.length_map, TlsInnerParallel.decode_length,
      Gcm.ctr_length Gcm.concrete _ _ _ he]
  have hfit : lengthField (exactParsed expanded nonce wire accepted) ≤ (TlsReceive.ciphertext wire).length := by
    unfold exactParsed TlsReceive.releaseOpened
    rw [TlsInnerParallel.decode_spec]
    refine Nat.le_trans (lengthField_release _ _) ?_
    refine Nat.le_trans (spec_length_fits _) ?_
    rw [Gcm.ctr_length Gcm.concrete _ _ _ he]
    exact Nat.le_refl _
  have hc := TlsReceive.ciphertext_length wire
  exact core_padded state _ k (by omega) (by omega) (by omega)

/-- The parse inside `tls-open-application-ctr` (`HybridKernel.tlsOpenApplicationCtr`) evaluates to `exactParsed`. -/
theorem exactParsed_refines (expanded nonce wire : List (BVExpr 8)) (accepted : BVExpr 8) (assign : BVExpr.Assignment) :
    (TlsReceive.releaseOpened ByteAuth.symbolic
        (ByteAuth.equalMask ByteAuth.symbolic (wire.take 5)
          (TlsRecord.header Gcm.symbolic ((TlsReceive.ciphertext wire).length + 16)))
        ⟨accepted, Gcm.ctr Gcm.symbolic expanded nonce (TlsReceive.ciphertext wire)⟩).map (BVExpr.eval assign) =
      exactParsed (expanded.map (BVExpr.eval assign)) (nonce.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))
        (BVExpr.eval assign accepted) := by
  have hc : TlsReceive.ciphertext (wire.map (BVExpr.eval assign)) = (TlsReceive.ciphertext wire).map (BVExpr.eval assign) := by
    simp [TlsReceive.ciphertext, List.map_take, List.map_drop]
  simp only [exactParsed, TlsReceive.releaseOpened_map (ByteAuth.evaluationHom assign), GcmOpen.Opened.map,
    ByteAuth.equalMask_map (ByteAuth.evaluationHom assign), TlsRecord.header_map (Gcm.evaluationHom assign),
    Gcm.ctr_map (Gcm.evaluationHom assign), List.map_take, hc, List.length_map]

/-! ### Sealing a content held in a capacity -/

private theorem step_on (c : BitVec 8) :
    ByteAuth.concrete.xor (ByteAuth.concrete.and 255 c)
      (ByteAuth.concrete.and (ByteAuth.concrete.xor 255 255) (ByteAuth.concrete.const 23)) = c := by
  show ((255 : BitVec 8) &&& c) ^^^ (((255 : BitVec 8) ^^^ 255) &&& 23) = c
  rw [show (255 : BitVec 8) &&& c = c from BitVec.allOnes_and]
  simp
private theorem step_at (r : BitVec 8) :
    ByteAuth.concrete.xor (ByteAuth.concrete.and 0 r)
      (ByteAuth.concrete.and (ByteAuth.concrete.xor 255 0) (ByteAuth.concrete.const 23)) = 23 := by
  show ((0 : BitVec 8) &&& r) ^^^ (((255 : BitVec 8) ^^^ 0) &&& 23) = 23
  rw [show (0 : BitVec 8) &&& r = 0 from BitVec.zero_and]; decide
private theorem step_off (r : BitVec 8) :
    ByteAuth.concrete.xor (ByteAuth.concrete.and 0 r)
      (ByteAuth.concrete.and (ByteAuth.concrete.xor 0 0) (ByteAuth.concrete.const 23)) = 0 := by
  show ((0 : BitVec 8) &&& r) ^^^ (((0 : BitVec 8) ^^^ 0) &&& 23) = 0
  rw [show (0 : BitVec 8) &&& r = 0 from BitVec.zero_and]; decide
private theorem last_on : ByteAuth.concrete.and 255 (ByteAuth.concrete.const 23) = 23 := by decide
private theorem last_off : ByteAuth.concrete.and 0 (ByteAuth.concrete.const 23) = 0 := by decide

theorem place_zero (rest : List (BitVec 8)) :
    place ByteAuth.concrete rest (List.replicate rest.length 0) (List.replicate (rest.length + 1) 0) =
      List.replicate (rest.length + 1) 0 := by
  induction rest with
  | nil => simp only [List.length_nil, List.replicate_zero, List.replicate_succ, place, last_off]
  | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ, place, step_off]
      simp only [List.replicate_succ] at ih
      rw [ih]

/-- Content, then the type byte, then zeros — whatever followed the content. -/
theorem place_value (content rest : List (BitVec 8)) :
    place ByteAuth.concrete (content ++ rest) (List.replicate content.length 255 ++ List.replicate rest.length 0)
        (List.replicate (content.length + 1) 255 ++ List.replicate rest.length 0) =
      content ++ [23] ++ List.replicate rest.length 0 := by
  induction content with
  | nil =>
      cases rest with
      | nil => simp only [List.length_nil, List.replicate_zero, List.replicate_succ, List.nil_append, List.append_nil,
          place, last_on]
      | cons r rs =>
          have h := place_zero rs
          simp only [List.replicate_succ] at h
          simp only [List.length_nil, List.length_cons, List.replicate_zero, List.replicate_succ, List.nil_append,
            List.cons_append, place, step_at, h]
  | cons c cs ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append, place, step_on]
      simp only [List.replicate_succ, List.cons_append] at ih
      rw [ih]

/-- A content of `n` bytes followed by any `k` bytes, with `size` = `n + 17`:
the length is accepted and the ciphertext is the CTR encryption of the
TLSInnerPlaintext of the content alone (type 23, no padding) — the ciphertext
`tls-seal-ctr 23 n 0` opens — followed by `k` zero bytes. -/
theorem sealCiphertext_padded (expanded nonce content rest : List (BitVec 8)) (high low : BitVec 8)
    (he : expanded.length = 176) (hb : content.length + rest.length + 17 < 65536)
    (hs : TlsPrivateSeal.lengthValue high low = content.length + 17) :
    sealCiphertext Gcm.concrete ByteAuth.concrete expanded nonce (content ++ rest) high low =
      (255, Gcm.ctr Gcm.concrete expanded nonce (TlsRecord.inner Gcm.concrete content 23 0) ++
        List.replicate rest.length 0) := by
  have hinner : TlsRecord.inner Gcm.concrete content 23 0 = content ++ [23] := by
    simp only [TlsRecord.inner, Gcm.zeros, List.replicate_zero, List.append_nil]; rfl
  have hbelow := within_value high low 17 content.length rest.length (by omega) (by omega)
  have hupTo := within_value high low 16 (content.length + 1) rest.length (by omega) (by omega)
  have hcount : (content ++ rest).length + 1 = content.length + 1 + rest.length := by
    simp only [List.length_append]; omega
  have hctr := ctr_prefix Gcm.concrete expanded nonce he (content ++ [23]) (List.replicate rest.length 0)
  have hkept : (Gcm.ctr Gcm.concrete expanded nonce (content ++ [23])).length = content.length + 1 := by
    rw [Gcm.ctr_length Gcm.concrete _ _ _ he]; simp
  have hrest : ((Gcm.ctr Gcm.concrete expanded nonce (content ++ [23] ++ List.replicate rest.length 0)).drop
      (content ++ [(23 : BitVec 8)]).length).length = (List.replicate rest.length (0 : BitVec 8)).length := by
    rw [List.length_drop, Gcm.ctr_length Gcm.concrete _ _ _ he]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega
  have hsplit := maskBytes_split (Gcm.ctr Gcm.concrete expanded nonce (content ++ [23]))
    ((Gcm.ctr Gcm.concrete expanded nonce (content ++ [23] ++ List.replicate rest.length 0)).drop
      (content ++ [(23 : BitVec 8)]).length)
  rw [hkept, hrest, ← hctr, List.length_replicate] at hsplit
  have hgoal : sealCiphertext Gcm.concrete ByteAuth.concrete expanded nonce (content ++ rest) high low =
      ((within ByteAuth.concrete high low 17 (content ++ rest).length).1,
        maskBytes ByteAuth.concrete (within ByteAuth.concrete high low 16 ((content ++ rest).length + 1)).2
          (Gcm.ctr Gcm.concrete expanded nonce (place ByteAuth.concrete (content ++ rest)
            (within ByteAuth.concrete high low 17 (content ++ rest).length).2
            (within ByteAuth.concrete high low 16 ((content ++ rest).length + 1)).2))) := rfl
  rw [hgoal, hcount, List.length_append, hbelow, hupTo]
  dsimp only
  rw [place_value, hsplit, hinner]

#print axioms ctr_prefix
#print axioms within_value
#print axioms openParsed_refines
#print axioms openParsed_padded
#print axioms spec_length_fits
#print axioms open_padded
#print axioms exactParsed_refines
#print axioms sealCiphertext_padded

end TlsMpc.RecordClass
