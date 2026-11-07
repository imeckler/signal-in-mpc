import LibSignalReference.Proofs.ShaCompact

namespace LibSignalReference.Proofs.ShaCompact.Equivalence

open TlsMpc.Sha256

set_option maxHeartbeats 2000000

def read (o : Ops B W) (words : List W) (i : Nat) : W :=
  words[i]?.getD (o.wordConst 0)

def word (o : Ops B W) (words : List W) (i : Nat) : W :=
  o.add (o.add (o.add (small1 o (read o words (i - 2))) (read o words (i - 7)))
    (small0 o (read o words (i - 15)))) (read o words (i - 16))

def valid (o : Ops B W) (words : List W) : Prop :=
  ∀ i, 16 ≤ i → i < words.length → read o words i = word o words i

theorem read_append (o : Ops B W) (xs ys : List W) (i : Nat) (hi : i < xs.length) :
    read o (xs ++ ys) i = read o xs i := by
  simp [read, List.getElem?_append_left hi]

theorem read_append_last (o : Ops B W) (xs : List W) (x : W) :
    read o (xs ++ [x]) xs.length = x := by
  simp [read, List.getElem?_append_right]

theorem word_append (o : Ops B W) (xs ys : List W) (i : Nat)
    (hlo : 16 ≤ i) (hhi : i ≤ xs.length) :
    word o (xs ++ ys) i = word o xs i := by
  unfold word
  rw [read_append o xs ys (i - 2) (by omega),
    read_append o xs ys (i - 7) (by omega),
    read_append o xs ys (i - 15) (by omega),
    read_append o xs ys (i - 16) (by omega)]

theorem step_eq (o : Ops B W) (xs : List W) :
    scheduleStep o xs = xs ++ [word o xs xs.length] := rfl

theorem valid_step (o : Ops B W) (xs : List W) (hsize : 16 ≤ xs.length)
    (hx : valid o xs) : valid o (scheduleStep o xs) := by
  rw [step_eq]
  intro i hlo hhi
  have hb : i ≤ xs.length := by simpa using hhi
  rw [word_append o xs _ i hlo hb]
  by_cases hi : i < xs.length
  · rw [read_append o xs _ i hi]
    exact hx i hlo hi
  · have hi : i = xs.length := by omega
    subst i
    exact read_append_last o xs _

theorem valid_extend (o : Ops B W) (n : Nat) (xs : List W) (hx : valid o xs)
    (hsize : 16 ≤ xs.length) : valid o (extendSchedule o n xs) := by
  induction n generalizing xs with
  | zero => exact hx
  | succ n ih =>
    simp only [extendSchedule]
    apply ih _ (valid_step o xs hsize hx)
    simp [step_eq]
    omega

theorem read_extend (o : Ops B W) (n : Nat) (xs : List W) (i : Nat) (hi : i < xs.length) :
    read o (extendSchedule o n xs) i = read o xs i := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [extendSchedule]
    rw [ih _ (by simp [step_eq]; omega), step_eq, read_append o xs _ i hi]

def window (o : Ops B W) (i : Nat) (ring wide : List W) : Prop :=
  ∀ j, i - 16 ≤ j → j < max 16 i → read o ring (j % 16) = read o wide j

theorem read_set (o : Ops B W) (xs : List W) (position i : Nat) (x : W)
    (hi : position < xs.length) :
    read o (xs.set position x) i = if position = i then x else read o xs i := by
  simp only [read, List.getElem?_set, if_pos hi]
  split <;> simp_all

theorem scheduled_word (i : Nat) (ring wide : List (BitVec 32))
    (hw : window concrete i ring wide) (hv : valid concrete wide) (hi : i < wide.length) :
    (TlsMpc.Signal.ShaCompact.schedule concrete i ring).2 = read concrete wide i := by
  by_cases early : i < 16
  · have h := hw i (by omega) (by omega)
    simpa [TlsMpc.Signal.ShaCompact.schedule, early, read, Nat.mod_eq_of_lt early] using h
  · have h16 : 16 ≤ i := by omega
    have h2 := hw (i - 2) (by omega) (by omega)
    have h7 := hw (i - 7) (by omega) (by omega)
    have h15 := hw (i - 15) (by omega) (by omega)
    have hback := hw (i - 16) (by omega) (by omega)
    rw [hv i h16 hi]
    simp only [TlsMpc.Signal.ShaCompact.schedule, if_neg early, Prod.snd]
    change concrete.add (concrete.add (concrete.add
      (read concrete ring ((i - 16) % 16))
      (small0 concrete (read concrete ring ((i - 15) % 16))))
      (read concrete ring ((i - 7) % 16)))
      (small1 concrete (read concrete ring ((i - 2) % 16))) = _
    rw [h2, h7, h15, hback]
    simp only [word, concrete]
    ac_rfl

theorem window_step (i : Nat) (ring wide : List (BitVec 32)) (hlen : ring.length = 16)
    (hw : window concrete i ring wide) (hv : valid concrete wide) (hi : i < wide.length) :
    window concrete (i + 1) (TlsMpc.Signal.ShaCompact.schedule concrete i ring).1 wide := by
  intro j hlo hhi
  by_cases early : i < 16
  · simp only [TlsMpc.Signal.ShaCompact.schedule, if_pos early, Prod.fst]
    exact hw j (by omega) (by omega)
  · have hs := scheduled_word i ring wide hw hv hi
    simp only [TlsMpc.Signal.ShaCompact.schedule, if_neg early, Prod.fst] at *
    rw [read_set concrete ring (i % 16) (j % 16) _ (by omega)]
    by_cases heq : j = i
    · subst j
      simpa using hs
    · have hmod : i % 16 ≠ j % 16 := by omega
      rw [if_neg hmod]
      exact hw j (by omega) (by omega)

theorem schedule_length (o : Ops B W) (i : Nat) (ring : List W) :
    (TlsMpc.Signal.ShaCompact.schedule o i ring).1.length = ring.length := by
  simp only [TlsMpc.Signal.ShaCompact.schedule]
  split <;> simp

theorem run_eq_rounds (count i : Nat) (ring wide : List (BitVec 32))
    (s : State (BitVec 32)) (hwide : wide.length = 64) (hlen : ring.length = 16)
    (hv : valid concrete wide) (hw : window concrete i ring wide) (hcount : i + count = 64) :
    TlsMpc.Signal.ShaCompact.run concrete count i ring s =
      rounds concrete (constants.drop i) (wide.drop i) s := by
  have hc : constants.length = 64 := rfl
  induction count generalizing i ring s with
  | zero =>
    have hi : i = 64 := by omega
    subst i
    simp [TlsMpc.Signal.ShaCompact.run, List.drop_eq_nil_of_le (by omega : constants.length ≤ 64),
      rounds]
  | succ count ih =>
    have hi : i < wide.length := by omega
    have hk : i < constants.length := by omega
    have hs := scheduled_word i ring wide hw hv hi
    have hlen' : (TlsMpc.Signal.ShaCompact.schedule concrete i ring).1.length = 16 := by
      rw [schedule_length, hlen]
    have hw' := window_step i ring wide hlen hw hv hi
    rw [TlsMpc.Signal.ShaCompact.run]
    cases hp : TlsMpc.Signal.ShaCompact.schedule concrete i ring with
    | mk next emitted =>
      simp only [hp, Prod.fst, Prod.snd] at hs hlen' hw' ⊢
      rw [ih (i + 1) next _ hlen' hw' (by omega)]
      rw [List.drop_eq_getElem_cons hk, List.drop_eq_getElem_cons hi]
      simp only [rounds, hs, read, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hk, Option.getD_some]

theorem compact_eq_root (s : State (BitVec 32)) (block : List (BitVec 32))
    (hlen : block.length = 16) :
    TlsMpc.Signal.ShaCompact.compress concrete s block = TlsMpc.Sha256.compress concrete s block := by
  let wide := extendSchedule concrete 48 block
  have hwide : wide.length = 64 := by simp [wide, extended_length, hlen]
  have hv0 : valid concrete block := by intro i hlo hhi; omega
  have hv : valid concrete wide := valid_extend concrete 48 block hv0 (by omega)
  have hw : window concrete 0 block wide := by
    intro j hlo hhi
    have hj : j < 16 := by simpa using hhi
    have hb : j < block.length := by omega
    simpa [wide, Nat.mod_eq_of_lt hj] using (read_extend concrete 48 block j hb).symm
  have heq := run_eq_rounds 64 0 block wide s hwide hlen hv hw rfl
  simp only [List.drop_zero] at heq
  unfold TlsMpc.Signal.ShaCompact.compress TlsMpc.Sha256.compress
  rw [heq]

end LibSignalReference.Proofs.ShaCompact.Equivalence
