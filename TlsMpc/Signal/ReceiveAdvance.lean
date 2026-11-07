import TlsMpc.Signal.SkippedKeys
import TlsMpc.Signal.Symmetric

/-! Public bounded receive-chain advancement. The circuit explores maxJump+1
candidate counters without secret branches, deriving HMAC(chain,01) seeds and
HMAC(chain,02) next keys. Intermediate seeds enter the bounded newest-first
store. The target seed is returned separately and is not inserted. No counter
wrap is accepted, including target=uint32.max. Authentication-gated commit
preserves the original chain/counter/store on failure. This is a bounded seed
path, not the full forward-jump policy, CBC authentication, or session persistence. -/
namespace TlsMpc.Signal.ReceiveAdvance
open Std.Tactic.BVDecide SkippedKeys

structure Candidate (B : Type) where
  found : B
  seed : Bytes B 32
  nextChain : Bytes B 32
  nextCounter : Bytes B 4
  slots : List (Slot B)

def Candidate.map (f : B → B') (r : Candidate B) : Candidate B' :=
  ⟨f r.found, f ∘ r.seed, f ∘ r.nextChain, f ∘ r.nextCounter, r.slots.map (Slot.map f)⟩

def wordBytes (s : Sha256.Ops B W) (counter : W) : Bytes B 4 := fun i => s.unpack counter i.val

def listBytes (a : ByteAuth.Ops B) (bytes : List B) : Bytes B n := fun i => bytes[i.val]?.getD (a.const 0)

def choose (a : ByteAuth.Ops B) (mask : B) (yes no : Candidate B) : Candidate B :=
  ⟨Unpad.chooseByte a mask yes.found no.found, chooseBytes a mask yes.seed no.seed,
    chooseBytes a mask yes.nextChain no.nextChain, chooseBytes a mask yes.nextCounter no.nextCounter,
    chooseSlots a mask yes.slots no.slots⟩

def rejected (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (chain : Bytes B 32)
    (counter : W) (slots : List (Slot B)) : Candidate B :=
  ⟨a.const 0, fun _ => a.const 0, chain, wordBytes s counter, slots⟩

/-- Shared seed and next-chain derivation using a single prepared HMAC state. -/
def chainStep (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (chain : Bytes B 32) : Bytes B 32 × Bytes B 32 :=
  let prepared := HmacPrepared.prepare s (List.ofFn chain)
  (listBytes a (HmacPrepared.run s prepared [s.byteConst 1]),
   listBytes a (HmacPrepared.run s prepared [s.byteConst 2]))

def scan (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (ratchet : Bytes B 32)
    (target : W) (fallback : Candidate B) : Nat → B → W → Bytes B 32 → List (Slot B) → Candidate B
  | 0, _, _, _, _ => fallback
  | fuel+1, active, counter, chain, slots =>
      let canStep := a.and active (a.not (ByteAuth.equalMask a
        (List.ofFn (wordBytes s counter)) (List.replicate 4 (a.const 255))))
      let hit := a.and canStep (ByteAuth.equalMask a (List.ofFn (wordBytes s counter)) (List.ofFn (wordBytes s target)))
      let (seed,next) := chainStep s a chain
      let nextCounter := s.add counter (s.wordConst 1)
      let current : Candidate B := ⟨a.const 255,seed,next,wordBytes s nextCounter,slots⟩
      let tail := scan s a ratchet target fallback fuel canStep nextCounter next
        (insertFront a ratchet (wordBytes s counter) seed slots)
      choose a hit current tail

def advance (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat)
    (ratchet chain : Bytes B 32) (current target : W) (slots : List (Slot B)) : Candidate B :=
  scan s a ratchet target (rejected s a chain current slots) (maxJump+1) (a.const 255) current chain slots

/-- Candidate must come from advance over the supplied old state. -/
def commit (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (auth : B) (candidate : Candidate B)
    (oldChain : Bytes B 32) (oldCounter : W) (oldSlots : List (Slot B)) : Candidate B :=
  let accepted := a.and (ByteAuth.eqMask a auth (a.const 255)) (ByteAuth.eqMask a candidate.found (a.const 255))
  ⟨accepted, fun i => a.and accepted (candidate.seed i),
    chooseBytes a accepted candidate.nextChain oldChain,
    chooseBytes a accepted candidate.nextCounter (wordBytes s oldCounter),
    chooseSlots a accepted candidate.slots oldSlots⟩

def committed (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat) (auth : B)
    (ratchet chain : Bytes B 32) (current target : W) (slots : List (Slot B)) : Candidate B :=
  commit s a auth (advance s a maxJump ratchet chain current target slots) chain current slots

def bytes (r : Candidate B) : List B :=
  r.found :: (List.ofFn r.seed ++ List.ofFn r.nextChain ++ List.ofFn r.nextCounter ++ storeBytes r.slots)

theorem chainStep_correct (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (chain : Bytes B 32) :
    chainStep s a chain =
      (listBytes a (Symmetric.messageSeed s (List.ofFn chain)),
       listBytes a (Symmetric.nextChainKey s (List.ofFn chain))) := by
  simp only [chainStep, HmacPrepared.run_prepare, Symmetric.messageSeed, Symmetric.nextChainKey]

theorem choose_accept (yes no : Candidate (BitVec 8)) (h : yes.slots.length = no.slots.length) :
    choose ByteAuth.concrete 255 yes no = yes := by
  unfold choose chooseBytes
  simp only [Unpad.chooseByte_accept, chooseSlots_accept _ _ h]

theorem choose_reject (yes no : Candidate (BitVec 8)) (h : yes.slots.length = no.slots.length) :
    choose ByteAuth.concrete 0 yes no = no := by
  unfold choose chooseBytes
  simp only [Unpad.chooseByte_reject, chooseSlots_reject _ _ h]

theorem scan_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (ratchet : Bytes B 32)
    (target : W) (fallback : Candidate B) (fuel : Nat) (active : B) (counter : W)
    (chain : Bytes B 32) (slots : List (Slot B)) (h : fallback.slots.length = slots.length) :
    (scan s a ratchet target fallback fuel active counter chain slots).slots.length = slots.length := by
  induction fuel generalizing active counter chain slots with
  | zero => exact h
  | succ fuel ih =>
      simp only [scan, choose, chooseSlots, List.length_zipWith]
      rw [ih _ _ _ _ (by simpa [insert_length] using h), insert_length, Nat.min_self]

theorem advance_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat)
    (ratchet chain : Bytes B 32) (current target : W) (slots : List (Slot B)) :
    (advance s a maxJump ratchet chain current target slots).slots.length = slots.length := by
  exact scan_length _ _ _ _ _ _ _ _ _ _ rfl

theorem failed_auth_preserves (maxJump : Nat) (auth : BitVec 8)
    (ratchet chain : Bytes (BitVec 8) 32) (current target : BitVec 32)
    (slots : List (Slot (BitVec 8))) (h : auth ≠ 255) :
    committed Sha256.concrete ByteAuth.concrete maxJump auth ratchet chain current target slots =
      rejected Sha256.concrete ByteAuth.concrete chain current slots := by
  have ha : ByteAuth.eqMask ByteAuth.concrete auth (ByteAuth.concrete.const 255) = 0 := by
    change ByteAuth.eqMask ByteAuth.concrete auth 255 = 0
    rw [ByteAuth.eqMask_value, if_neg h]
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [committed, commit, ha, hz]
  rw [chooseSlots_reject _ _ (advance_length _ _ _ _ _ _ _ _)]
  unfold chooseBytes
  simp only [Unpad.chooseByte_reject]
  rfl

theorem committed_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat) (auth : B)
    (ratchet chain : Bytes B 32) (current target : W) (slots : List (Slot B)) :
    (committed s a maxJump auth ratchet chain current target slots).slots.length = slots.length := by
  simp [committed, commit, chooseSlots, advance_length]

theorem bytes_length (r : Candidate B) : (bytes r).length = 69 + 69*r.slots.length := by
  simp [bytes, storeBytes_length]; omega

theorem failed_candidate_preserves (maxJump : Nat) (auth : BitVec 8)
    (ratchet chain : Bytes (BitVec 8) 32) (current target : BitVec 32)
    (slots : List (Slot (BitVec 8)))
    (h : (advance Sha256.concrete ByteAuth.concrete maxJump ratchet chain current target slots).found ≠ 255) :
    committed Sha256.concrete ByteAuth.concrete maxJump auth ratchet chain current target slots =
      rejected Sha256.concrete ByteAuth.concrete chain current slots := by
  have ha : ByteAuth.eqMask ByteAuth.concrete
      (advance Sha256.concrete ByteAuth.concrete maxJump ratchet chain current target slots).found
      (ByteAuth.concrete.const 255) = 0 := by
    change ByteAuth.eqMask ByteAuth.concrete _ 255 = 0
    rw [ByteAuth.eqMask_value, if_neg h]
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have hzero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [committed, commit, ha, hz, hzero]
  rw [chooseSlots_reject _ _ (advance_length _ _ _ _ _ _ _ _)]
  unfold chooseBytes
  simp only [Unpad.chooseByte_reject]
  rfl

theorem authenticated_hit_commits (maxJump : Nat)
    (ratchet chain : Bytes (BitVec 8) 32) (current target : BitVec 32)
    (slots : List (Slot (BitVec 8)))
    (h : (advance Sha256.concrete ByteAuth.concrete maxJump ratchet chain current target slots).found = 255) :
    committed Sha256.concrete ByteAuth.concrete maxJump 255 ratchet chain current target slots =
      advance Sha256.concrete ByteAuth.concrete maxJump ratchet chain current target slots := by
  have ha : ByteAuth.eqMask ByteAuth.concrete 255 (ByteAuth.concrete.const 255) = 255 := by decide
  have ht : ByteAuth.concrete.and 255 255 = 255 := by decide
  have hand (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  simp only [committed, commit, h, ha, ht, hand]
  rw [chooseSlots_accept _ _ (advance_length _ _ _ _ _ _ _ _)]
  unfold chooseBytes
  simp only [Unpad.chooseByte_accept]
  rw [← h]

theorem wordBytes_eq (x y : BitVec 32) :
    List.ofFn (wordBytes Sha256.concrete x) = List.ofFn (wordBytes Sha256.concrete y) ↔ x = y := by
  have reconstruct (z : BitVec 32) :
      (z.extractLsb' 24 8 ++ (z.extractLsb' 16 8 ++ (z.extractLsb' 8 8 ++ z.extractLsb' 0 8))) = z := by
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    exact BitVec.extractLsb'_eq_self
  simp only [wordBytes, Sha256.concrete, List.ofFn_succ, List.ofFn_zero, List.cons.injEq]
  constructor
  · rintro ⟨h0,h1,h2,h3,_⟩
    change x.extractLsb' 24 8 = y.extractLsb' 24 8 at h0
    change x.extractLsb' 16 8 = y.extractLsb' 16 8 at h1
    change x.extractLsb' 8 8 = y.extractLsb' 8 8 at h2
    change x.extractLsb' 0 8 = y.extractLsb' 0 8 at h3
    have he : (x.extractLsb' 24 8 ++ (x.extractLsb' 16 8 ++ (x.extractLsb' 8 8 ++ x.extractLsb' 0 8))) =
        (y.extractLsb' 24 8 ++ (y.extractLsb' 16 8 ++ (y.extractLsb' 8 8 ++ y.extractLsb' 0 8))) := by
      rw [h0,h1,h2,h3]
    exact (reconstruct x).symm.trans (he.trans (reconstruct y))
  · intro he; subst y; exact ⟨rfl,rfl,rfl,rfl,True.intro⟩

theorem wordEqual_value (x y : BitVec 32) :
    ByteAuth.equalMask ByteAuth.concrete (List.ofFn (wordBytes Sha256.concrete x))
      (List.ofFn (wordBytes Sha256.concrete y)) = if x = y then 255 else 0 := by
  simp only [ByteAuth.equalMask_value, wordBytes_eq]

theorem counterMask_value (x : BitVec 32) :
    ByteAuth.concrete.not (ByteAuth.equalMask ByteAuth.concrete
      (List.ofFn (wordBytes Sha256.concrete x)) (List.replicate 4 (ByteAuth.concrete.const 255))) =
      if x = 4294967295 then 0 else 255 := by
  have he : List.replicate 4 (ByteAuth.concrete.const 255) =
      List.ofFn (wordBytes Sha256.concrete (4294967295 : BitVec 32)) := by decide
  rw [he, wordEqual_value]
  split <;> rfl

theorem scan_inactive (ratchet : Bytes (BitVec 8) 32) (target : BitVec 32) (fallback : Candidate (BitVec 8))
    (fuel : Nat) (counter : BitVec 32) (chain : Bytes (BitVec 8) 32) (slots : List (Slot (BitVec 8)))
    (h : fallback.slots.length = slots.length) :
    scan Sha256.concrete ByteAuth.concrete ratchet target fallback fuel 0 counter chain slots = fallback := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  induction fuel generalizing counter chain slots with
  | zero => rfl
  | succ fuel ih =>
      simp only [scan, hz]
      rw [choose_reject]
      · exact ih _ _ _ (by simpa [insert_length] using h)
      · rw [scan_length _ _ _ _ _ _ _ _ _ _ (by simpa [insert_length] using h), insert_length]

/-- Reference recurrence with ordinary branching: derive exactly until the
first target, reject at max-u32, and insert only strictly intermediate seeds. -/
def scanSpec (ratchet : Bytes (BitVec 8) 32) (target : BitVec 32) (fallback : Candidate (BitVec 8)) :
    Nat → BitVec 32 → Bytes (BitVec 8) 32 → List (Slot (BitVec 8)) → Candidate (BitVec 8)
  | 0, _, _, _ => fallback
  | fuel+1, counter, chain, slots =>
      if counter = 4294967295 then fallback else
      let seed := listBytes ByteAuth.concrete (Symmetric.messageSeed Sha256.concrete (List.ofFn chain))
      let next := listBytes ByteAuth.concrete (Symmetric.nextChainKey Sha256.concrete (List.ofFn chain))
      if counter = target then ⟨255,seed,next,wordBytes Sha256.concrete (counter+1),slots⟩
      else scanSpec ratchet target fallback fuel (counter+1) next
        (insertFront ByteAuth.concrete ratchet (wordBytes Sha256.concrete counter) seed slots)

theorem scan_spec (ratchet : Bytes (BitVec 8) 32) (target : BitVec 32) (fallback : Candidate (BitVec 8))
    (fuel : Nat) (counter : BitVec 32) (chain : Bytes (BitVec 8) 32) (slots : List (Slot (BitVec 8)))
    (h : fallback.slots.length = slots.length) :
    scan Sha256.concrete ByteAuth.concrete ratchet target fallback fuel 255 counter chain slots =
      scanSpec ratchet target fallback fuel counter chain slots := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have ho (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have inc (x : BitVec 32) : Sha256.concrete.add x (Sha256.concrete.wordConst 1) = x+1 := rfl
  induction fuel generalizing counter chain slots with
  | zero => rfl
  | succ fuel ih =>
      simp only [scan, counterMask_value, wordEqual_value, ho, inc, scanSpec]
      have hlen : slots.length = (scan Sha256.concrete ByteAuth.concrete ratchet target fallback fuel
          (if counter = 4294967295 then 0 else 255) (counter+1) (chainStep Sha256.concrete ByteAuth.concrete chain).2
          (insertFront ByteAuth.concrete ratchet (wordBytes Sha256.concrete counter)
            (chainStep Sha256.concrete ByteAuth.concrete chain).1 slots)).slots.length := by
        rw [scan_length _ _ _ _ _ _ _ _ _ _ (by simpa [insert_length] using h), insert_length]
      by_cases hm : counter = 4294967295
      · simp only [if_pos hm, hz]
        rw [choose_reject _ _ (by simpa only [if_pos hm] using hlen)]
        exact scan_inactive _ _ _ _ _ _ _ (by simpa [insert_length] using h)
      · simp only [if_neg hm, ho]
        by_cases ht : counter = target
        · simp only [if_pos ht]
          rw [choose_accept _ _ (by simpa only [if_neg hm] using hlen)]
          rw [chainStep_correct]
          rfl
        · simp only [if_neg ht]
          rw [choose_reject _ _ (by simpa only [if_neg hm] using hlen)]
          rw [ih _ _ _ (by simpa [insert_length] using h), chainStep_correct]

theorem advance_spec (maxJump : Nat) (ratchet chain : Bytes (BitVec 8) 32)
    (current target : BitVec 32) (slots : List (Slot (BitVec 8))) :
    advance Sha256.concrete ByteAuth.concrete maxJump ratchet chain current target slots =
      scanSpec ratchet target (rejected Sha256.concrete ByteAuth.concrete chain current slots)
        (maxJump+1) current chain slots := by
  exact scan_spec _ _ _ _ _ _ _ rfl

theorem counter_lt_max (x : BitVec 32) (h : x ≠ 4294967295) : x.toNat < 4294967295 := by
  have hb := x.isLt
  have hn : x.toNat ≠ 4294967295 := by
    intro he
    apply h
    apply BitVec.eq_of_toNat_eq
    exact he
  change x.toNat < 4294967296 at hb
  omega

theorem increment_toNat (x : BitVec 32) (h : x ≠ 4294967295) : (x+1).toNat = x.toNat+1 := by
  have hb := counter_lt_max x h
  change (x.toNat+1)%4294967296 = x.toNat+1
  exact Nat.mod_eq_of_lt (by omega)

theorem scanSpec_found_iff (ratchet : Bytes (BitVec 8) 32) (target : BitVec 32)
    (fallback : Candidate (BitVec 8)) (hf : fallback.found = 0) (fuel : Nat)
    (counter : BitVec 32) (chain : Bytes (BitVec 8) 32) (slots : List (Slot (BitVec 8))) :
    (scanSpec ratchet target fallback fuel counter chain slots).found = 255 ↔
      ∃ distance, distance < fuel ∧ counter.toNat + distance = target.toNat ∧ target.toNat < 4294967295 := by
  induction fuel generalizing counter chain slots with
  | zero => simp [scanSpec, hf]
  | succ fuel ih =>
      by_cases hm : counter = 4294967295
      · subst counter
        simp only [scanSpec, ↓reduceIte, hf]
        have hn : (0 : BitVec 8) ≠ 255 := by decide
        change (0 : BitVec 8) = 255 ↔ ∃ distance, distance < fuel+1 ∧ 4294967295+distance = target.toNat ∧ target.toNat < 4294967295
        constructor
        · intro he; exact (hn he).elim
        · rintro ⟨distance,_,he,hb⟩; omega
      · by_cases ht : counter = target
        · subst target
          simp only [scanSpec, if_neg hm, ↓reduceIte]
          constructor
          · intro _; exact ⟨0, by omega, by omega, counter_lt_max counter hm⟩
          · intro _; trivial
        · simp only [scanSpec, if_neg hm, if_neg ht]
          rw [ih, increment_toNat counter hm]
          have hn : counter.toNat ≠ target.toNat := by
            intro he; exact ht (BitVec.eq_of_toNat_eq he)
          constructor
          · rintro ⟨distance,hd,he,hb⟩
            exact ⟨distance+1,by omega,by omega,hb⟩
          · rintro ⟨distance,hd,he,hb⟩
            exact ⟨distance-1,by omega,by omega,hb⟩

/-- Exact eligibility: no backward lookup, public distance bound, and room for
incrementing the returned chain counter. In particular max-u32 is rejected. -/
theorem advance_found_iff (maxJump : Nat) (ratchet chain : Bytes (BitVec 8) 32)
    (current target : BitVec 32) (slots : List (Slot (BitVec 8))) :
    (advance Sha256.concrete ByteAuth.concrete maxJump ratchet chain current target slots).found = 255 ↔
      current.toNat ≤ target.toNat ∧ target.toNat ≤ current.toNat+maxJump ∧ target.toNat < 4294967295 := by
  rw [advance_spec, scanSpec_found_iff _ _ _ rfl]
  constructor
  · rintro ⟨distance,hd,he,hb⟩; omega
  · rintro ⟨hlo,hhi,hb⟩
    exact ⟨target.toNat-current.toNat,by omega,by omega,hb⟩

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

include hs in
theorem wordBytes_map (counter : W) : f ∘ wordBytes s counter = wordBytes s' (fw counter) := by
  funext i; exact hs.unpack counter i.val

include ha in
theorem listBytes_map (data : List B) : f ∘ (listBytes a data : Bytes B n) = listBytes a' (data.map f) := by
  funext i
  simp only [Function.comp_def, listBytes, List.getElem?_map]
  cases he : data[i.val]? <;> simp [ha.const]

include ha in
theorem choose_map (mask : B) (yes no : Candidate B) :
    (choose a mask yes no).map f = choose a' (f mask) (yes.map f) (no.map f) := by
  simp only [choose, Candidate.map, Unpad.chooseByte_map ha, chooseBytes_map ha, chooseSlots_map ha]

include hs ha in
theorem rejected_map (chain : Bytes B 32) (counter : W) (slots : List (Slot B)) :
    (rejected s a chain counter slots).map f =
      rejected s' a' (f ∘ chain) (fw counter) (slots.map (Slot.map f)) := by
  simp only [rejected, Candidate.map, ha.const, wordBytes_map hs, Function.comp_def]

include hs ha in
theorem chainStep_map (chain : Bytes B 32) :
    (f ∘ (chainStep s a chain).1, f ∘ (chainStep s a chain).2) = chainStep s' a' (f ∘ chain) := by
  simp only [chainStep_correct, listBytes_map ha, Symmetric.messageSeed_map hs, Symmetric.nextChainKey_map hs,
    List.map_ofFn, Function.comp_def]

include hs ha in
theorem scan_map (ratchet : Bytes B 32) (target : W) (fallback : Candidate B)
    (fuel : Nat) (active : B) (counter : W) (chain : Bytes B 32) (slots : List (Slot B)) :
    (scan s a ratchet target fallback fuel active counter chain slots).map f =
      scan s' a' (f ∘ ratchet) (fw target) (fallback.map f) fuel (f active) (fw counter)
        (f ∘ chain) (slots.map (Slot.map f)) := by
  induction fuel generalizing active counter chain slots with
  | zero => rfl
  | succ fuel ih =>
      have hseed := congrArg Prod.fst (chainStep_map hs ha chain)
      have hnext := congrArg Prod.snd (chainStep_map hs ha chain)
      dsimp only at hseed hnext
      simp only [scan]
      rw [choose_map ha, ih]
      simp only [Candidate.map, ha.and, ha.not, ha.const,
        ByteAuth.equalMask_map ha, List.map_replicate, List.map_ofFn, wordBytes_map hs,
        hs.add, hs.wordConst, insert_map ha, hseed, hnext]

include hs ha in
theorem advance_map (maxJump : Nat) (ratchet chain : Bytes B 32) (current target : W) (slots : List (Slot B)) :
    (advance s a maxJump ratchet chain current target slots).map f =
      advance s' a' maxJump (f ∘ ratchet) (f ∘ chain) (fw current) (fw target) (slots.map (Slot.map f)) := by
  simp only [advance, scan_map hs ha, rejected_map hs ha, ha.const]

include hs ha in
theorem commit_map (auth : B) (candidate : Candidate B) (chain : Bytes B 32) (counter : W) (slots : List (Slot B)) :
    (commit s a auth candidate chain counter slots).map f =
      commit s' a' (f auth) (candidate.map f) (f ∘ chain) (fw counter) (slots.map (Slot.map f)) := by
  simp only [commit, Candidate.map, chooseBytes_map ha, chooseSlots_map ha,
    wordBytes_map hs, ha.and, ha.const, ByteAuth.eqMask_map ha]
  simp only [Function.comp_def, ha.and, ByteAuth.eqMask_map ha, ha.const]

include hs ha in
theorem committed_map (maxJump : Nat) (auth : B) (ratchet chain : Bytes B 32)
    (current target : W) (slots : List (Slot B)) :
    (committed s a maxJump auth ratchet chain current target slots).map f =
      committed s' a' maxJump (f auth) (f ∘ ratchet) (f ∘ chain) (fw current) (fw target) (slots.map (Slot.map f)) := by
  simp only [committed, commit_map hs ha, advance_map hs ha]
end Refinement

theorem bytes_map (f : B → B') (r : Candidate B) : (bytes r).map f = bytes (r.map f) := by
  simp [bytes, Candidate.map, storeBytes_map, Function.comp_def]

theorem compiled_advance_correct (maxJump : Nat) (ratchet chain : Bytes (BVExpr 8) 32)
    (current target : BVExpr 32) (slots : List (Slot (BVExpr 8))) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (bytes (advance Sha256.symbolic ByteAuth.symbolic maxJump ratchet chain current target slots)).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (bytes (advance Sha256.symbolic ByteAuth.symbolic maxJump ratchet chain current target slots)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (bytes (advance Sha256.symbolic ByteAuth.symbolic maxJump ratchet chain current target slots)))).vec.get index hi)) =
      (ByteCircuit.joinValue (bytes (advance Sha256.concrete ByteAuth.concrete maxJump
        (BVExpr.eval assign ∘ ratchet) (BVExpr.eval assign ∘ chain)
        (BVExpr.eval assign current) (BVExpr.eval assign target) (slots.map (Slot.map (BVExpr.eval assign)))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, bytes_map,
    advance_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_committed_correct (maxJump : Nat) (auth : BVExpr 8) (ratchet chain : Bytes (BVExpr 8) 32)
    (current target : BVExpr 32) (slots : List (Slot (BVExpr 8))) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (bytes (committed Sha256.symbolic ByteAuth.symbolic maxJump auth ratchet chain current target slots)).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (bytes (committed Sha256.symbolic ByteAuth.symbolic maxJump auth ratchet chain current target slots)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (bytes (committed Sha256.symbolic ByteAuth.symbolic maxJump auth ratchet chain current target slots)))).vec.get index hi)) =
      (ByteCircuit.joinValue (bytes (committed Sha256.concrete ByteAuth.concrete maxJump
        (BVExpr.eval assign auth) (BVExpr.eval assign ∘ ratchet) (BVExpr.eval assign ∘ chain)
        (BVExpr.eval assign current) (BVExpr.eval assign target) (slots.map (Slot.map (BVExpr.eval assign)))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, bytes_map,
    committed_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.ReceiveAdvance
