import TlsMpc.Node.Policy.ReceiveSim

/-!
# T1, item 4: every run, every record, every stream

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

* `run_safe`: from any state the controller reaches (`ReceiveSim.Sim`), with nothing to pass over and
  `mayReveal`, every byte of the run it reveals next (`budget s` bytes, whatever they turn out to be) is
  public in the reference, except that the run's last byte may be the reference's first `error`.
* The record loop (`ReceiveProofs.recordLoop`, `streamRun`) composed with `sim_step` (every byte of a
  run it accepts), `sim_pass` (every byte it passes over, `passBulk` being a run of `passOne`:
  `passRun_bulk`), across any cut into records: **`t1_frames`**, and **`t1_model`** (formerly
  `t1_all`). The same for the loop the session runs (`RecordLoop.run`), with the session's steps
  between records: `ReceiveSession.lean` (`t1_session`, **`t1_all`**).
-/

open TlsMpc TlsMpc.Signal

namespace ReceiveLoop

open PublicReceive ReceiveProofs ReceiveStream ReceiveSimFrame ReceiveSimByte ReceiveComplete
open ReceiveReply ReceiveRequestScan ReceiveSim
open TlsMpc.KernelSpecs.ParseWebSocketFrame (P mb dat ctl Shaped)

/-- Position `i` of `C` may be revealed: it is public, or it is the first `error`. -/
def SafeR (C : List ReceiveSpec.Class) (i : Nat) : Prop :=
  (∃ x, C[i]? = some x ∧ x.secret = false) ∨ (C[i]? = some .error ∧ ∀ j < i, C[j]? ≠ some .error)

/-! ### The budget, by frame position -/

theorem phase_gets {S : FState} (j : Nat) (hP : S.phases = P j) (i : Nat) (hi : i < 5) :
    PublicReceive.get (TlsWebSocketFrame.stateBytes S) i = mb (j == i) := by
  unfold TlsWebSocketFrame.stateBytes
  rw [hP]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem budget_phase {s : State} {S : FState} (hu : s.upgraded = true) (hf : s.frame = TlsWebSocketFrame.stateBytes S)
    (j : Nat) (hP : S.phases = P j) (hj : j < 4) :
    budget s = if j = 0 ∨ j = 2 then 2 else 1 := by
  unfold budget
  rw [hf]
  simp only [hu, Bool.not_true, Bool.false_eq_true, if_false, phase_gets j hP 0 (by omega),
    phase_gets j hP 2 (by omega), phase_gets j hP 4 (by omega), mb_beq_on]
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem budget_payload {s : State} {S : FState} {k : Nat} (hu : s.upgraded = true)
    (hf : s.frame = TlsWebSocketFrame.stateBytes S) (hsh : Shaped S) (hP : S.phases = P 4)
    (hk : TlsWebSocketFrame.wordValue S.high S.low = k) (hk1 : 1 ≤ k) (c : Bool)
    (hlt : S.opcode.toNat < 8 ↔ c = false) :
    budget s = if c then k else
      if s.message == [8, 2] then max 1 (min k (replyBudget s.reply s.openBody))
      else if s.message == [8, 1] then max 1 (min k (fieldMissing s.request))
      else if s.message.isEmpty then min 2 k else 1 := by
  obtain ⟨g4, g7, g8, g10, g11⟩ := frame_gets hsh
  have hrem : S.high.toNat * 256 + S.low.toNat = k := by
    rw [← hk]; unfold TlsWebSocketFrame.wordValue; omega
  have hk0 : (k == 0) = false := by simp; omega
  unfold budget
  rw [hf]
  simp only [hu, Bool.not_true, Bool.false_eq_true, if_false, phase_gets 4 hP 0 (by omega),
    phase_gets 4 hP 2 (by omega), phase_gets 4 hP 4 (by omega), mb_beq_on, g7, g10, g11, hrem, hk0,
    show ((4 : Nat) == 0) = false by rfl, show ((4 : Nat) == 2) = false by rfl, beq_self_eq_true,
    Bool.or_self, Bool.not_true]
  cases c
  · have : S.opcode.toNat < 8 := hlt.mpr rfl
    simp only [Bool.false_eq_true, if_false, ge_iff_le, Nat.not_le.mpr this]
  · have : ¬ S.opcode.toNat < 8 := fun e => by have := hlt.mp e; cases this
    simp only [if_true, ge_iff_le, show 8 ≤ S.opcode.toNat by omega]

/-! ### The reference over a run inside a frame's payload -/

theorem safeR_cons {x : ReceiveSpec.Class} (hx : x ≠ .error) {C : List ReceiveSpec.Class} {i : Nat}
    (h : SafeR C i) : SafeR (x :: C) (i + 1) := by
  rcases h with ⟨y, hy, hs⟩ | ⟨he, hj⟩
  · exact Or.inl ⟨y, by simpa using hy, hs⟩
  · refine Or.inr ⟨by simpa using he, fun j hj' => ?_⟩
    cases j with
    | zero => simp [hx]
    | succ j => simpa using hj j (by omega)

/-- **A run of a data frame's payload bytes**: if the message's classes (with `complete = cpl`, over
the whole message when it is complete) are `Strong` at the run's positions, every byte of the run is
safe in the stream. -/
theorem payload_run_safe (ob f cpl : Bool) (fr : Bool) :
    ∀ (Y : List Byte) (M Z : List Byte) (k : Nat), Y.length ≤ k → 1 ≤ k →
      cpl = (f && decide (k ≤ (Y ++ Z).length)) →
      (∀ i < Y.length, Strong (ReceiveSpec.message ob cpl (M ++ (if cpl then (Y ++ Z).take k else Y)))
        (M.length + i) (i + 1 = Y.length)) →
      ∀ i < Y.length, SafeR (Stream.runF ob (⟨.payload false f cpl k, M, fr⟩, false) (Y ++ Z)) i
  | [], _, _, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | y :: Y', M, Z, k, hYk, hk1, hcpl, hS, i, hi => by
    have hYl : (y :: Y').length = Y'.length + 1 := rfl
    have hYZl : ((y :: Y') ++ Z).length = Y'.length + Z.length + 1 := by
      simp only [List.cons_append, List.length_cons, List.length_append]
    have hc0 : Stream.payloadClass ob cpl M y k =
        ((ReceiveSpec.message ob cpl (M ++ (if cpl then ((y :: Y') ++ Z).take k else y :: Y')))[M.length]?).getD
          .error := by
      unfold Stream.payloadClass
      congr 1
      cases cpl
      · simp only [Bool.false_eq_true, if_false, List.replicate_zero]
        have h1 := congrArg (fun l => l[M.length]?) (message_prefix ob (M ++ [y]) Y')
        have h2 := congrArg (fun l => l[M.length]?) (message_prefix ob (M ++ [y]) [])
        simp only [List.getElem?_take, List.length_append, List.length_singleton,
          show M.length < M.length + 1 by omega, if_true, List.append_nil, List.append_assoc,
          List.cons_append, List.nil_append] at h1 h2
        rw [← h1]
      · simp only [if_true]
        have hk' : k ≤ ((y :: Y') ++ Z).length := by
          have h' := hcpl.symm
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
          exact h'.2
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [List.cons_append, List.take_succ_cons]
        have c1 := message_causal ob true (M ++ [y]) (List.replicate k' 0) ((Y' ++ Z).take k')
          (fun _ => by simp only [List.length_replicate, List.length_take, List.length_append]; omega)
        have := congrArg (fun l => l[M.length]?) c1
        simp only [List.getElem?_take, List.length_append, List.length_singleton,
          show M.length < M.length + 1 by omega, if_true, List.append_assoc, List.cons_append,
          List.nil_append] at this
        simp only [Nat.add_sub_cancel]
        exact this
    have hS0 := hS 0 (by simp)
    rw [Nat.add_zero] at hS0
    -- the first byte's class
    have hfirst : SafeR (Stream.runF ob (⟨.payload false f cpl k, M, fr⟩, false) ((y :: Y') ++ Z)) 0 := by
      rw [List.cons_append, Stream.runF]
      simp only [Stream.stepF, Bool.false_eq_true, if_false]
      rw [(stream_data ob M fr f cpl k y _ hk1).1, hc0]
      rcases hS0 with ⟨x, hx, hs⟩ | ⟨-, he⟩
      · exact Or.inl ⟨x, by rw [hx]; rfl, hs⟩
      · exact Or.inr ⟨by rw [he]; rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    cases i with
    | zero => exact hfirst
    | succ i =>
      have hi' : i + 1 < Y'.length + 1 := by rw [← hYl]; exact hi
      have hYk' : Y'.length + 1 ≤ k := by rw [← hYl]; exact hYk
      have hpub : Stream.payloadClass ob cpl M y k ≠ .error := by
        rw [hc0]
        rcases hS0 with ⟨x, hx, hs⟩ | ⟨hl, -⟩
        · rw [hx]; simp only [Option.getD_some]; intro e; rw [e] at hs; cases hs
        · rw [hYl] at hl; omega
      rw [List.cons_append, Stream.runF]
      simp only [Stream.stepF, Bool.false_eq_true, if_false]
      rw [(stream_data ob M fr f cpl k y _ hk1).1]
      have hnot : decide (Stream.payloadClass ob cpl M y k = .error) = false := by simp [hpub]
      have hstep : (Stream.step ob ⟨.payload false f cpl k, M, fr⟩ y (Y' ++ Z).length).2 =
          ⟨.payload false f cpl (k - 1), M ++ [y], fr⟩ := by
        simp only [Stream.step, Bool.false_eq_true, if_false, if_neg (show ¬ k ≤ 1 by omega)]
      rw [hnot, hstep]
      apply safeR_cons hpub
      apply payload_run_safe ob f cpl fr Y' (M ++ [y]) Z (k - 1) (by omega) (by omega)
        (by rw [hcpl]; congr 1; simp only [decide_eq_decide, hYZl, List.length_append]; omega) _ i (by omega)
      intro i' hi''
      have := hS (i' + 1) (by rw [hYl]; omega)
      have hW : (M ++ (if cpl then ((y :: Y') ++ Z).take k else y :: Y')) =
          (M ++ [y]) ++ (if cpl then (Y' ++ Z).take (k - 1) else Y') := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        cases cpl <;> simp
      rw [hW] at this
      have e1 : (M ++ [y]).length + i' = M.length + (i' + 1) := by simp; omega
      have e2 : (i' + 1 + 1 = (y :: Y').length) ↔ (i' + 1 = Y'.length) := by rw [hYl]; omega
      rw [e1]
      unfold Strong at this ⊢
      rcases this with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨e2.mp h1, h2⟩

/-- A control frame's payload: every byte is `control`. -/
theorem control_run_safe (ob f cpl : Bool) (fr : Bool) :
    ∀ (Y : List Byte) (M Z : List Byte) (k : Nat), Y.length ≤ k → 1 ≤ k →
      ∀ i < Y.length, SafeR (Stream.runF ob (⟨.payload true f cpl k, M, fr⟩, false) (Y ++ Z)) i
  | [], _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | y :: Y', M, Z, k, hYk, hk1, i, hi => by
    rw [List.cons_append, Stream.runF]
    simp only [Stream.stepF, Bool.false_eq_true, if_false]
    have hc : (Stream.step ob ⟨.payload true f cpl k, M, fr⟩ y (Y' ++ Z).length).1 = .control := by
      simp only [Stream.step, if_true]; split <;> rfl
    rw [hc]
    cases i with
    | zero => exact Or.inl ⟨.control, rfl, rfl⟩
    | succ i =>
      have hstep : (Stream.step ob ⟨.payload true f cpl k, M, fr⟩ y (Y' ++ Z).length).2 =
          ⟨.payload true f cpl (k - 1), M, fr⟩ := by
        simp [Stream.step, show ¬ k ≤ 1 by simp at hYk hi; omega]
      rw [hstep, show decide (ReceiveSpec.Class.control = .error) = false by decide]
      exact safeR_cons (by decide) (control_run_safe ob f cpl fr Y' M Z (k - 1) (by simp at hYk; omega)
        (by simp at hYk hi; omega) i (by simpa using hi))

/-- The first two payload bytes of any message are `kind`. -/
theorem message_kind_pos (ob c : Bool) (X : List Byte) (i : Nat) (h2 : i < 2) (hX : i < X.length) :
    (ReceiveSpec.message ob c X)[i]? = some .kind := by
  match X, i with
  | [a], 0 => rfl
  | a :: b :: rest, 0 =>
    rw [message_eq]; split
    · rfl
    · split <;> rfl
  | a :: b :: rest, 1 =>
    rw [message_eq]; split
    · rfl
    · split <;> rfl
  | [a], 1 => simp at hX
  | [], _ => simp at hX
  | _, i + 2 => omega

theorem take_split (Y Z : List Byte) (k : Nat) (h : Y.length ≤ k) : (Y ++ Z).take k = Y ++ Z.take (k - Y.length) := by
  rw [List.take_append, List.take_of_length_le h]

/-! ### Header bytes -/

/-- Not inside a payload. -/
def Hdr (st : Stream.St) : Prop := ∀ c f cpl k, st.phase ≠ .payload c f cpl k

theorem hdr_class {ob : Bool} {st : Stream.St} (h : Hdr st) (b : Byte) (l : Nat) :
    (Stream.step ob st b l).1 = .frameHeader ∨ (Stream.step ob st b l).1 = .error := by
  obtain ⟨ph, m, fr⟩ := st
  cases ph with
  | payload c f cpl k => exact absurd rfl (h c f cpl k)
  | dead => exact Or.inr rfl
  | first => left; simp only [Stream.step]; split <;> rfl
  | second b0 => left; simp only [Stream.step]; split <;> (try split) <;> rfl
  | extHi b0 => exact Or.inl rfl
  | extLo b0 hi => left; simp only [Stream.step]; split <;> rfl

theorem safe0 {ob : Bool} {st : Stream.St} {b : Byte} {rest : List Byte}
    (h : (Stream.step ob st b rest.length).1 = .frameHeader ∨ (Stream.step ob st b rest.length).1 = .error) :
    SafeR (Stream.runF ob (st, false) (b :: rest)) 0 := by
  simp only [Stream.runF, Stream.stepF, Bool.false_eq_true, if_false]
  rcases h with h | h
  · rw [h]; exact Or.inl ⟨_, rfl, rfl⟩
  · rw [h]; exact Or.inr ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem safe1 {ob : Bool} {st : Stream.St} {b0 b1 : Byte} {rest : List Byte}
    (h0 : (Stream.step ob st b0 (rest.length + 1)).1 = .frameHeader)
    (h1 : (Stream.step ob (Stream.step ob st b0 (rest.length + 1)).2 b1 rest.length).1 = .frameHeader ∨
      (Stream.step ob (Stream.step ob st b0 (rest.length + 1)).2 b1 rest.length).1 = .error) :
    SafeR (Stream.runF ob (st, false) (b0 :: b1 :: rest)) 1 := by
  have e : Stream.stepF ob (st, false) b0 (b1 :: rest).length =
      (.frameHeader, ((Stream.step ob st b0 (rest.length + 1)).2, false)) := by
    simp only [Stream.stepF, Bool.false_eq_true, if_false, List.length_cons, h0]
    try rfl
  rw [Stream.runF, e]
  exact safeR_cons (show ReceiveSpec.Class.frameHeader ≠ .error by decide) (safe0 h1)

/-- A run of at most two header bytes, the first a header byte and the next not a payload byte. -/
theorem two_safe {ob : Bool} {st : Stream.St} (h0 : ∀ b l, (Stream.step ob st b l).1 = .frameHeader)
    (h1 : ∀ b l, Hdr (Stream.step ob st b l).2) :
    ∀ (Y Z : List Byte), Y.length ≤ 2 → ∀ i < Y.length, SafeR (Stream.runF ob (st, false) (Y ++ Z)) i
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, _, 0, _ => by rw [List.cons_append]; exact safe0 (Or.inl (h0 _ _))
  | [_], _, _, i + 1, hi => absurd hi (by simp)
  | b0 :: _ :: _, _, _, 1, _ => by
    rw [List.cons_append, List.cons_append]
    exact safe1 (h0 b0 _) (hdr_class (h1 b0 _) _ _)
  | _ :: _ :: _, _, hY, i + 2, hi => by simp only [List.length_cons] at hY hi; omega

/-- A run of at most one byte, not a payload byte. -/
theorem one_safe {ob : Bool} {st : Stream.St} (h : Hdr st) :
    ∀ (Y Z : List Byte), Y.length ≤ 1 → ∀ i < Y.length, SafeR (Stream.runF ob (st, false) (Y ++ Z)) i
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, _, 0, _ => by rw [List.cons_append]; exact safe0 (hdr_class h _ _)
  | _ :: _, _, hY, i + 1, hi => by simp only [List.length_cons] at hY hi; omega

/-! ### A data payload run, at the message level -/

theorem data_budget_le (m : List Byte) (k a b : Nat) (hk : 1 ≤ k) :
    (if m == [8, 2] then max 1 (min k a) else if m == [8, 1] then max 1 (min k b)
      else if m.isEmpty then min 2 k else 1) ≤ k := by
  split
  · exact Nat.max_le.mpr ⟨hk, Nat.min_le_left _ _⟩
  · split
    · exact Nat.max_le.mpr ⟨hk, Nat.min_le_left _ _⟩
    · split
      · exact Nat.min_le_right _ _
      · exact hk

/-- The byte the controller reveals inside a delivered envelope (nothing to pass over) is public. -/
theorem env_strong {ob cpl : Bool} {s : State} {Pre E0 H0 : List Byte} {y : Byte} {bs : Bool} {n : Nat}
    {hd : List Byte} {p r : Nat} {L : List Bool} (hA : EnvAtP s Pre y E0 H0 bs n hd p 0 r L) (b : Byte)
    (Z' : List Byte) (hfit : cpl = true → r ≤ (b :: Z').length) :
    ∃ x, (ReceiveSpec.message ob cpl ((8 :: 1 :: (Pre ++ y :: E0)) ++ (b :: Z')))[(8 :: 1 :: (Pre ++ y :: E0)).length]? =
      some x ∧ x.secret = false := by
  have hW : cpl = true → n ≤ (E0 ++ b :: Z').length := by
    intro e; have := hfit e; have := hA.len; rw [List.length_append]; omega
  obtain ⟨C, hCe, hCl, -⟩ := qshape_body_c hA.shape y hA.scanSkip ob cpl (E0 ++ b :: Z') hW
  rw [hA.path] at hCe
  have e1 : (8 :: 1 :: (Pre ++ y :: E0) : List Byte) ++ b :: Z' = 8 :: 1 :: (Pre ++ y :: (E0 ++ b :: Z')) := by
    simp
  have hn1 : E0.length + 1 ≤ n := by have := hA.len; have := hA.rpos; omega
  have etake : (E0 ++ b :: Z').take n = E0 ++ b :: Z'.take (n - E0.length - 1) := by
    rw [List.take_append, List.take_of_length_le (by omega), show n - E0.length = (n - E0.length - 1) + 1 by omega]
    rfl
  have el : (8 :: 1 :: (Pre ++ y :: E0) : List Byte).length = C.length + E0.length := by
    rw [hCl]; simp only [List.length_cons, List.length_append]; omega
  rw [e1, hCe, etake, el, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  unfold ReceiveSpec.requestBody
  rw [if_pos rfl]
  have hlenA := ReceiveStream.envelope_len ((E0 ++ b :: Z'.take (n - E0.length - 1)).length + 1)
    (E0 ++ b :: Z'.take (n - E0.length - 1))
  rw [List.getElem?_append_left (by rw [hlenA]; simp)]
  exact env_class_public E0 b _ L hd p hA.walk hA.walkLen

/-- **A data payload run, at the message level.** From any message state the controller reaches
(`MsgSim`), with nothing to pass over, every byte of a run within the budget is public in the
reference's classes of the message (the run `Y`, then any `Z'`, which with `complete` holds the open
field), except that the last may be `error`. -/
theorem msg_strong {ob cpl : Bool} {s : State} {M : List Byte} (hM : MsgSim s M) (hsk : s.skip = 0)
    (hob : s.openBody = ob) {k : Nat} (Y Z' : List Byte)
    (hY : Y.length ≤ (if s.message == [8, 2] then max 1 (min k (replyBudget s.reply s.openBody))
      else if s.message == [8, 1] then max 1 (min k (fieldMissing s.request))
      else if s.message.isEmpty then min 2 k else 1))
    (hfit : cpl = true → pendingField s ≤ (Y ++ Z').length) :
    ∀ i < Y.length, Strong (ReceiveSpec.message ob cpl (M ++ (Y ++ Z'))) (M.length + i) (i + 1 = Y.length) := by
  cases hM with
  | empty hm _ =>
    rw [hm, if_neg (by decide), if_neg (by decide), if_pos (show ([] : List Byte).isEmpty = true from rfl)] at hY
    have hY2 := Nat.le_trans hY (Nat.min_le_left _ _)
    intro i hi
    rw [List.nil_append, List.length_nil, Nat.zero_add]
    exact strong_pub _ (message_kind_pos ob cpl _ i (by omega) (by rw [List.length_append]; omega)) rfl
  | @one a hm _ =>
    rw [hm, if_neg (by simp), if_neg (by simp), if_neg (by simp)] at hY
    intro i hi
    rw [show [a].length + i = 1 by simp; omega]
    exact strong_pub _ (message_kind_pos ob cpl _ 1 (by omega) (by simp; omega)) rfl
  | @reply P hR _ _ _ _ =>
    have hm := hR.message
    rw [hm, if_pos (by decide)] at hY
    have hsh := hR.shape [] (by rw [hsk]; rfl)
    rw [List.append_nil, hob] at hsh
    have hpos := rshape_budget_pos hsh
    rw [hob] at hY
    have hY' : Y.length ≤ replyBudget s.reply ob :=
      Nat.le_trans hY (Nat.max_le.mpr ⟨hpos, Nat.min_le_right _ _⟩)
    have hfit' : cpl = true → replyMissing s.reply ob ≤ (Y ++ Z').length := by
      intro e
      have := hfit e
      unfold pendingField at this
      rw [hm, hsk, if_neg (by decide), if_pos (by decide), if_neg (by decide), hob] at this
      exact this
    intro i hi
    have := rshape_run_c (c := cpl) hsh Y Z' hY' hfit' i hi
    rw [show (8 :: 2 :: P : List Byte).length + i = 2 + P.length + i by simp; omega]
    exact this
  | @request P hQ _ _ _ =>
    have hm := hQ.message
    rw [hm, if_neg (by decide), if_pos (by decide)] at hY
    have hsh := hQ.shape [] (by rw [hsk]; rfl)
    rw [List.append_nil] at hsh
    have hY' : Y.length ≤ max 1 (fieldMissing s.request) :=
      Nat.le_trans hY (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (Nat.min_le_right _ _) (Nat.le_max_right _ _)⟩)
    have hfit' : cpl = true → fieldMissing s.request ≤ (Y ++ Z').length := by
      intro e
      have := hfit e
      unfold pendingField at this
      rw [hm, if_pos (by decide), hQ.inner] at this
      dsimp only at this
      rw [hsk, if_neg (by decide)] at this
      exact this
    intro i hi
    have := qshape_run_c hsh ob cpl Y Z' hY' hfit' i hi
    rw [show (8 :: 1 :: P : List Byte).length + i = 2 + P.length + i by simp; omega]
    exact strong_of_pubAt _ this
  | env hE _ _ =>
    obtain ⟨Pre, y, E0, H0, bs, n, hd, p, k0, r, L, rfl, hA⟩ := hE
    have hat := hA.at_
    have hk0 : k0 = 0 := by rw [← hat.skip, hsk]
    subst hk0
    rw [hat.message, if_neg (by decide), if_pos (by decide), hat.missing, Nat.min_zero] at hY
    have hY1 : Y.length ≤ 1 := hY
    intro i hi
    match Y, hY1, hi with
    | [b], _, hi' =>
      obtain rfl : i = 0 := by simp only [List.length_singleton] at hi'; omega
      have hfit' : cpl = true → r ≤ (b :: Z').length := by
        intro e
        have := hfit e
        unfold pendingField at this
        rw [hat.message, if_pos (by decide), hat.inner] at this
        exact this
      obtain ⟨x, hx, hs⟩ := env_strong (ob := ob) hA b Z' hfit'
      rw [Nat.add_zero]
      exact strong_pub _ hx hs

/-- **T1 for one run (every state the controller reaches, every byte string).** With nothing to pass
over, every byte of the run the controller reveals next (`budget s` bytes, whatever they are, followed by
whatever the stream holds) is public in the reference, or is its first `error`. -/
theorem run_safe {ob : Bool} {s : State} {st1 : Stream.St} (Y Z : List Byte)
    (hs : Sim ob s (st1, false) (Y.length + Z.length)) (hsk : s.skip = 0)
    (hY : Y.length ≤ budget s) :
    ∀ i < Y.length, SafeR (Stream.runF ob (st1, false) (Y ++ Z)) i := by
  obtain ⟨S, hf, hfs⟩ := hs.frame
  have hu := hs.up
  have hob := hs.openBody
  have hfits := hs.fits
  have hM := hs.msg
  obtain ⟨phase, M, fr⟩ := st1
  have hph := hfs.phase
  simp only at hph hfits hM
  cases phase with
  | dead => exact absurd hph id
  | first =>
    rw [budget_phase hu hf 0 hph (by omega), if_pos (Or.inl rfl)] at hY
    exact two_safe (fun b l => by simp only [Stream.step]; split <;> rfl)
      (fun b l c f cpl k => by simp only [Stream.step]; split <;> simp) Y Z hY
  | second b0 =>
    rw [budget_phase hu hf 1 (show S.phases = P 1 from hph.1) (by omega), if_neg (by omega)] at hY
    exact one_safe (fun c f cpl k h => by cases h) Y Z hY
  | extHi b0 =>
    rw [budget_phase hu hf 2 (show S.phases = P 2 from hph.1) (by omega), if_pos (Or.inr rfl)] at hY
    exact two_safe (fun b l => rfl) (fun b l c f cpl k h => by cases h) Y Z hY
  | extLo b0 hi =>
    rw [budget_phase hu hf 3 (show S.phases = P 3 from hph.1) (by omega), if_neg (by omega)] at hY
    exact one_safe (fun c f cpl k h => by cases h) Y Z hY
  | payload c f cpl k =>
    obtain ⟨hP, hk, hk1, -, -, hlt, -, hcpl, -⟩ := hph
    rw [budget_payload hu hf hfs.shaped hP hk hk1 c hlt] at hY
    have hcpl' : cpl = (f && decide (k ≤ (Y ++ Z).length)) := by rw [List.length_append]; exact hcpl
    cases c
    · rw [if_neg Bool.false_ne_true] at hY
      have hYk : Y.length ≤ k := Nat.le_trans hY (data_budget_le _ _ _ _ hk1)
      obtain ⟨Z', hZe, hZl⟩ : ∃ Z', (if cpl then (Y ++ Z).take k else Y) = Y ++ Z' ∧
          (cpl = true → (Y ++ Z').length = k) := by
        cases cpl
        · exact ⟨[], by simp, fun e => absurd e Bool.false_ne_true⟩
        · refine ⟨Z.take (k - Y.length), by rw [if_pos (show true = true from rfl), take_split Y Z k hYk],
            fun _ => ?_⟩
          have h' := hcpl'.symm
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_append] at h'
          rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
          omega
      have hfitZ : cpl = true → pendingField s ≤ (Y ++ Z').length := by
        intro e
        subst e
        rw [hZl rfl]
        exact hfits
      have key := msg_strong hM hsk hob Y Z' hY hfitZ
      refine payload_run_safe ob f cpl fr Y M Z k hYk hk1 hcpl' ?_
      rw [hZe]
      exact key
    · rw [if_pos (show true = true from rfl)] at hY
      exact control_run_safe ob f cpl fr Y M Z k hY hk1

/-! ### The whole stream, seen from a position -/

/-- The reference's classes `C` of the whole stream, seen from stream position `p`: `W` is the
stream from there, `st` the reference's state there, and no position before `p` is `error`. -/
def G (ob : Bool) (C : List ReceiveSpec.Class) (p : Nat) (st : Stream.St × Bool) (W : List Byte) : Prop :=
  ∃ Cp : List ReceiveSpec.Class, C = Cp ++ Stream.runF ob st W ∧ Cp.length = p ∧ ∀ x ∈ Cp, x ≠ .error

/-- `T1`'s condition on one revealed position. -/
def Good (C : List ReceiveSpec.Class) (q : Nat) : Prop :=
  ReceiveSpec.allowedIn C q = true ∨ ReceiveSpec.firstError C = some q

theorem g_step {ob : Bool} {C : List ReceiveSpec.Class} {p : Nat} {st1 : Stream.St} {b : Byte} {W : List Byte}
    (hg : G ob C p (st1, false) (b :: W)) (hb : (Stream.stepF ob (st1, false) b W.length).2.2 = false) :
    G ob C (p + 1) (Stream.stepF ob (st1, false) b W.length).2 W := by
  obtain ⟨Cp, hC, hl, hn⟩ := hg
  have hne : (Stream.stepF ob (st1, false) b W.length).1 ≠ .error := by
    simp only [Stream.stepF, Bool.false_eq_true, if_false, decide_eq_false_iff_not] at hb ⊢
    exact hb
  refine ⟨Cp ++ [(Stream.stepF ob (st1, false) b W.length).1], ?_, by rw [List.length_append, hl]; rfl, ?_⟩
  · rw [hC, List.append_assoc]; rfl
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hn x h
    · rw [List.mem_singleton.mp h]; exact hne

theorem findIdx_error : ∀ (C : List ReceiveSpec.Class) (q : Nat), C[q]? = some .error →
    (∀ j < q, C[j]? ≠ some .error) → C.findIdx? (· == .error) = some q
  | [], _, h, _ => by simp at h
  | x :: C, 0, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [List.findIdx?_cons]
  | x :: C, q + 1, h, hj => by
    have hx : x ≠ .error := fun e => hj 0 (by omega) (by simp [e])
    have ih := findIdx_error C q (by simpa using h) (fun j hj' => by simpa using hj (j + 1) (by omega))
    simp [List.findIdx?_cons, hx, ih]

theorem good_of {ob : Bool} {C : List ReceiveSpec.Class} {p : Nat} {st : Stream.St × Bool} {W : List Byte}
    (hg : G ob C p st W) {i : Nat} (h : SafeR (Stream.runF ob st W) i) : Good C (p + i) := by
  obtain ⟨Cp, hC, hl, hn⟩ := hg
  have hat : ∀ j, C[p + j]? = (Stream.runF ob st W)[j]? := by
    intro j; rw [hC, List.getElem?_append_right (by omega), show p + j - Cp.length = j by omega]
  rcases h with ⟨x, hx, hs⟩ | ⟨he, hj⟩
  · left
    unfold ReceiveSpec.allowedIn
    rw [hat i, hx]
    simp [hs]
  · right
    unfold ReceiveSpec.firstError
    apply findIdx_error C (p + i) (by rw [hat i]; exact he)
    intro j hj'
    by_cases hjp : j < p
    · rw [hC, List.getElem?_append_left (by omega)]
      intro e
      exact hn _ (List.mem_iff_getElem?.mpr ⟨j, e⟩) rfl
    · have := hat (j - p)
      rw [show p + (j - p) = j by omega] at this
      rw [this]
      exact hj (j - p) (by omega)

/-! ### Runs of bytes the controller accepts or passes over -/

theorem window_sim {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (Y : List Byte) {s s' : State}
    {st : Stream.St × Bool} {p : Nat} {W : List Byte}, Sim ob s st (Y ++ W).length → G ob C p st (Y ++ W) →
    stepWindow s Y = .ok s' → ∃ st', Sim ob s' st' W.length ∧ G ob C (p + Y.length) st' W
  | [], s, s', st, p, W, hs, hg, h => by
    cases h; exact ⟨st, hs, hg⟩
  | b :: rest, s, s', st, p, W, hs, hg, h => by
    obtain ⟨st1, bad⟩ := st
    have hb0 : bad = false := hs.bad
    subst hb0
    have e : ((b :: rest) ++ W).length = (rest ++ W).length + 1 := by simp
    rw [e] at hs
    unfold stepWindow at h
    cases h1 : step s b with
    | error err => rw [h1] at h; cases h
    | ok r =>
      obtain ⟨next, c⟩ := r
      rw [h1] at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      have hs1 := sim_step hs h1
      have hg1 := g_step (W := rest ++ W) hg hs1.bad
      split at h
      · next he =>
        cases h
        have hr : rest = [] := List.isEmpty_iff.mp he
        subst hr
        exact ⟨_, hs1, hg1⟩
      · split at h
        · obtain ⟨st', hs', hg'⟩ := window_sim rest hs1 hg1 h
          refine ⟨st', hs', ?_⟩
          rw [show p + (b :: rest).length = p + 1 + rest.length by simp; omega]
          exact hg'
        · cases h

theorem pass_sim {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (m : Nat) {s s' : State} {d : Bool}
    {st : Stream.St × Bool} {p : Nat} {W : List Byte}, m ≤ W.length → Sim ob s st W.length → G ob C p st W →
    passRun m s = .ok (s', d) → ∃ st', Sim ob s' st' (W.drop m).length ∧ G ob C (p + m) st' (W.drop m)
  | 0, s, s', d, st, p, W, _, hs, hg, h => by
    cases h; exact ⟨st, hs, hg⟩
  | m + 1, s, s', d, st, p, W, hm, hs, hg, h => by
    obtain ⟨b, W', rfl⟩ : ∃ b W', W = b :: W' := by
      cases W with
      | nil => simp at hm
      | cons b W' => exact ⟨b, W', rfl⟩
    obtain ⟨st1, bad⟩ := st
    have hb0 : bad = false := hs.bad
    subst hb0
    simp only [passRun, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · next r1 h1 =>
      obtain ⟨s1, d1⟩ := r1
      split at h
      · cases h
      · next r2 h2 =>
        obtain ⟨s2, d2⟩ := r2
        cases h
        have hs1 := sim_pass (b := b) (n := W'.length) hs h1
        have hg1 := g_step hg hs1.bad
        obtain ⟨st', hs', hg'⟩ := pass_sim m (by simp at hm; omega) hs1 hg1 h2
        refine ⟨st', ?_, ?_⟩
        · simpa using hs'
        · rw [show p + (m + 1) = p + 1 + m by omega]; simpa using hg'

theorem view_envelopes (s : State) : view s = view { s with envelopes := [] } := rfl

/-! What the session does between records keeps the view, so `Sim` (`sim_congr`). -/
theorem view_requests (s : State) : view s = view { s with requests := [] } := rfl

theorem view_expect (s : State) (id : Nat) : view s = view (expect s id) := by
  unfold expect
  generalize TlsChatResponse.stateBytes _ _ = R
  rfl

/-- `replies` returns `{ s with control := _ }` (its only result), so it keeps the view too (`rfl` on that
state; the lemma about `replies` itself: `view_replies`, `ReceiveSession.lean`). -/
theorem view_control (s : State) (c : List Byte) : view s = view { s with control := c } := rfl

theorem drop_run (r : List Byte) (o m : Nat) : (r.drop o).drop m = r.drop (o + ((r.drop o).take m).length) := by
  rw [List.drop_drop, List.length_take, List.length_drop]
  by_cases h : m ≤ r.length - o
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]

/-! ### One record -/

/-- **The record loop keeps the simulation, and every position it reveals is allowed** (with the
one-byte allowance). From offset `o` of record `r`, the stream from there being `r.drop o ++ Wr`. -/
theorem loop_good {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (fuel : Nat) (s : State) (r : List Byte)
    (o base : Nat) (acc : List Nat) (st : Stream.St × Bool) (Wr : List Byte),
    r.length + 1 ≤ fuel + o → o ≤ r.length → Sim ob s st (r.drop o ++ Wr).length →
    G ob C (base + o) st (r.drop o ++ Wr) → (∀ q ∈ acc, Good C q) →
    (∀ q ∈ (recordLoop fuel s r o base acc).1, Good C q) ∧
      (∀ s', (recordLoop fuel s r o base acc).2 = .ok s' →
        ∃ st', Sim ob s' st' Wr.length ∧ G ob C (base + r.length) st' Wr)
  | 0, _, _, _, _, _, _, _, hf, ho, _, _, _ => by omega
  | fuel + 1, s, r, o, base, acc, st, Wr, hf, ho, hs, hg, hacc => by
    unfold recordLoop
    by_cases hlt : o < r.length
    · rw [if_pos hlt]
      by_cases hsk : s.skip > 0
      · rw [if_pos hsk]
        dsimp only
        have hc1 : 1 ≤ min s.skip (r.length - o) := Nat.le_min.mpr ⟨hsk, by omega⟩
        have hc2 : min s.skip (r.length - o) ≤ r.length - o := Nat.min_le_right _ _
        generalize min s.skip (r.length - o) = count at hc1 hc2 ⊢
        have hbulk : min count (passRoom s) ≤ count := Nat.min_le_left _ _
        have hb := passRun_bulk (min count (passRoom s)) s (Nat.min_le_right _ _)
        have hadd := passRun_add (count - min count (passRoom s)) (min count (passRoom s)) s
        rw [Nat.add_sub_of_le hbulk, hb] at hadd
        split
        · exact ⟨hacc, fun _ h => by cases h⟩
        · next s1 d h1 =>
          have hrun : passRun count s = .ok (s1, false || d) := by
            rw [hadd]; simp only [bind, Except.bind, h1, pure, Except.pure]
          obtain ⟨st', hs', hg'⟩ := pass_sim count (by simp; omega) hs hg hrun
          have hW : (r.drop o ++ Wr).drop count = r.drop (o + count) ++ Wr := by
            rw [List.drop_append_of_le_length (by simp; omega), List.drop_drop]
          rw [hW] at hs' hg'
          exact loop_good fuel { s1 with envelopes := [] } r (o + count) base acc st' Wr (by omega) (by omega)
            (sim_congr (view_envelopes s1) hs') (by rw [← Nat.add_assoc]; exact hg') hacc
      · rw [if_neg hsk]
        have hsk0 : s.skip = 0 := by omega
        by_cases hmr : mayReveal s = true
        · rw [if_neg (by simp [hmr])]
          dsimp only
          have hYZ : r.drop o ++ Wr = (r.drop o).take (budget s) ++ ((r.drop o).drop (budget s) ++ Wr) := by
            rw [← List.append_assoc, List.take_append_drop]
          have hYl : ((r.drop o).take (budget s)).length ≤ r.length - o := by
            rw [List.length_take, List.length_drop]; exact Nat.min_le_right _ _
          have hacc' : ∀ q ∈ acc ++ (List.range ((r.drop o).take (budget s)).length).map (base + o + ·),
              Good C q := by
            intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact hacc q h
            · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
              have hi' := List.mem_range.mp hi
              rw [hYZ] at hs hg
              obtain ⟨st1, bad⟩ := st
              have hb0 : bad = false := hs.bad
              subst hb0
              exact good_of hg (run_safe _ _ (by rw [← List.length_append]; exact hs) hsk0
                (List.length_take_le _ _) i hi')
          split
          · exact ⟨hacc', fun _ h => by cases h⟩
          · next hemp =>
            split
            · exact ⟨hacc', fun _ h => by cases h⟩
            · next s2 h2 =>
              rw [hYZ] at hs hg
              obtain ⟨st'', hs'', hg''⟩ := window_sim _ hs hg h2
              rw [drop_run r o (budget s)] at hs'' hg''
              have hne : ((r.drop o).take (budget s)).length ≠ 0 := by
                intro e0
                exact hemp (List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero e0))
              exact loop_good fuel { s2 with envelopes := [] } r (o + ((r.drop o).take (budget s)).length) base
                _ st'' Wr (by omega) (by omega) (sim_congr (view_envelopes s2) hs'')
                (by rw [← Nat.add_assoc]; exact hg'') hacc'
        · rw [if_pos (by simp [hmr])]
          exact ⟨hacc, fun _ h => by cases h⟩
    · rw [if_neg hlt]
      have ho' : o = r.length := by omega
      subst ho'
      refine ⟨hacc, fun s' h => ?_⟩
      cases h
      rw [List.drop_length, List.nil_append] at hs hg
      exact ⟨st, hs, hg⟩

/-! ### Every record -/

theorem go_good {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (records : List (List Byte)) (s : State) (base : Nat)
    (acc : List Nat) (st : Stream.St × Bool), Sim ob s st records.flatten.length → G ob C base st records.flatten →
    (∀ q ∈ acc, Good C q) → ∀ q ∈ (streamRun.go s records base acc).1, Good C q
  | [], _, _, _, _, _, _, hacc, q, hq => hacc q hq
  | r :: rs, s, base, acc, st, hs, hg, hacc, q, hq => by
    rw [List.flatten_cons] at hs hg
    have hL := loop_good (r.length + 1) s r 0 base acc st rs.flatten (by omega) (by omega)
      (by rw [List.drop_zero]; exact hs) (by rw [List.drop_zero, Nat.add_zero]; exact hg) hacc
    unfold streamRun.go at hq
    split at hq
    · next acc1 e h1 => rw [h1] at hL; exact hL.1 q hq
    · next acc1 s1 h1 =>
      rw [h1] at hL
      obtain ⟨st', hs', hg'⟩ := hL.2 s1 rfl
      exact go_good rs s1 (base + r.length) acc1 st' hs' hg' hL.1 q hq

/-- **T1 from any state that simulates the reference's initial state.** -/
theorem t1_frames (ob : Bool) (s : State) (records : List (List Byte))
    (hs : Sim ob s Stream.init records.flatten.length) : T1 ob s records := by
  intro q hq
  have hC : ReceiveSpec.classifyFrames ob records.flatten = Stream.runF ob Stream.init records.flatten := by
    rw [Stream.classifyFrames_stream]; rfl
  have hg : G ob (ReceiveSpec.classifyFrames ob records.flatten) 0 Stream.init records.flatten :=
    ⟨[], by rw [hC]; rfl, rfl, by simp⟩
  exact go_good records s 0 [] Stream.init hs hg (by simp) q hq

/-- The upgraded starting state simulates the reference's initial state (a frame boundary, no
message), for every stream length. -/
theorem start_sim (ob : Bool) (accept : List Byte) (lenient : Bool) (n : Nat) :
    Sim ob { PublicReceive.start accept with upgraded := true, lenient := lenient, openBody := ob } Stream.init n :=
  ⟨rfl, rfl, rfl,
    ⟨TlsWebSocketFrame.start PublicReceive.fast capacity, rfl,
      ⟨(TlsMpc.KernelSpecs.ParseWebSocketFrame.start_boundary capacity).1, rfl,
        (TlsMpc.KernelSpecs.ParseWebSocketFrame.start_boundary capacity).2⟩⟩,
    MsgSim.empty rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- **T1 for every stream and every cut into records, about the model loop** (`ReceiveProofs.T1`,
with its one-byte allowance), from the upgraded starting state `ReceiveTest.upgraded openBody` (any
`accept`, any `lenient`): every stream position `streamRun` reveals is public in
`ReceiveSpec.classifyFrames openBody records.flatten`, or is that list's first `error`. (Called
`t1_all` until 2026-11-12; `t1_all` is now the statement about the loop the session runs,
`ReceiveSession.lean`.) -/
theorem t1_model : ∀ (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte)),
    T1 openBody { PublicReceive.start accept with upgraded := true, lenient := lenient, openBody } records :=
  fun openBody accept lenient records => t1_frames openBody _ records (start_sim openBody accept lenient _)

end ReceiveLoop

