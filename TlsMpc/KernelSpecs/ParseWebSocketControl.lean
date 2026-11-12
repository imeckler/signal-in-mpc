import TlsMpc.KernelSpecs.ParseWebSocketFrame
import TlsMpc.Node.Policy.Receive

/-!
# The controller's control-frame queue against RFC 6455 sections 5.5 and 5.3

New file; it changes no definition and no emitter imports it.

The controller (`TlsMpc/Node/Policy/Receive.lean`) runs `TlsWebSocketControl.run PublicReceive.fast`
on every server byte, fed the frame parser's `controlData`, `controlDone`, `controlKind` bytes and
the byte itself: it collects a control frame's payload and, at the frame's end, queues the reply the
client owes (up to four). `replies` later turns each queued reply into a client frame with
`TlsWebSocketControl.encode`.

## The reference

RFC 6455 section 5.5.2/5.5.3: a Ping is answered by a Pong "with identical Application data";
section 5.5.1: a Close not preceded by our own Close is answered by a Close (echoing the status code
it received: here the whole received body, which the frame parser has checked is a valid code and
UTF-8 reason); a Pong is not answered (`reply`). Section 5.2/5.3: a client frame is FIN + opcode,
MASK + 7-bit length, the 4-byte masking key, then payload byte `i` XOR key byte `i mod 4`
(`clientFrame`).

## What is proved (standard axioms only; no `sorry`, `native_decide`, `bv_decide`)

* `step_idle`, `step_collect`, `step_finish`, `step_finish_pong`, `step_finish_empty`: one step of
  the queue for each kind of input the frame parser produces (no control data; a payload byte; the
  last byte of a Ping/Close/Pong; the end of a Ping/Close with no payload);
* `control_frame` / `control_frame_pong` / `control_frame_empty`: from an idle queue with room, the
  inputs of one whole control frame, as the frame parser emits them while it stays valid (header
  bytes: nothing; payload bytes: control data; the last byte: control data, control done and the
  opcode as control kind; `rfc_ping_run` in `ParseWebSocketFrame` shows exactly this on RFC 6455's
  Ping example) leave the queue idle again with exactly `reply`'s answer appended: kind 10 for a
  Ping, 8 for a Close, its length, and the payload, padded with zeros, in its 125-byte slot
  (`kindOf_reply`); a Pong appends nothing. Payloads of 0 to 125 bytes;
* `run_stateBytes`: `TlsWebSocketControl.run` on the serialised state is `step`;
* `encode_frame`: `encode` (what `replies` sends) is `clientFrame` for a kind 8 or 10 and a length
  of at most 125, with the queued payload: RFC 6455's masked client frame.

## Finding (RFC 6455 section 5.3), fixed in stage S4

`replies` masked every queued reply of one drain with the same 4-byte key (the controller drew one
key per drain). RFC 6455 section 5.3: "the client MUST pick a fresh masking key ... for each frame".
It happened only when two or more control frames (Ping/Close) arrived in the records read before
one drain. Stage S4 changed `replies` to take one key per queued reply and the controller to draw
each from its own joint randomness (`controlMasks`); the counterexample `replies_reuse_mask` is
replaced by `replies_fresh_masks` (two Pongs, two keys: each frame carries its own) and
`replies_missing_mask` (too few keys: refused). With one queued reply nothing changed on the wire.

Not covered: that the frame parser stays valid on a well-formed control frame (acceptance), so the
composition frame parser → queue is stated on the queue's inputs, not proved from the frame bytes.
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open PublicReceive.PassOver (fast_and fast_const eq_fast select_zero select_ones select_zero' select_ones'
  member_range map_range_get choose_zero choose_ones)
open TlsWebSocketUpgrade (get eq either any member choose initial)
open TlsMpc.KernelSpecs.ParseWebSocketFrame (mb mb_true mb_false eq_mb select_mb and_ones_l and_ones_r
  and_zero_l and_zero_r not_ones not_zero member_mb)
open TlsWebSocketControl (State step)

namespace TlsMpc.KernelSpecs.ParseWebSocketControl

abbrev Byte := BitVec 8

/-! ### The reference -/

/-- RFC 6455 sections 5.5.1–5.5.3: the reply a client owes a control frame, as (opcode, payload). -/
def reply (opcode : Nat) (payload : List Byte) : Option (Nat × List Byte) :=
  if opcode = 9 then some (10, payload) else if opcode = 8 then some (8, payload) else none

/-- RFC 6455 sections 5.2 and 5.3: a final, masked client frame with a payload under 126 bytes. -/
def clientFrame (opcode : Nat) (key payload : List Byte) : List Byte :=
  [BitVec.ofNat 8 (128 + opcode), BitVec.ofNat 8 (128 + payload.length)] ++ key ++
    (List.range payload.length).map (fun i => payload.getD i 0 ^^^ key.getD (i % 4) 0)

/-- Slot `q` (125 bytes) of the 500-byte payload store replaced by `blk`. -/
def blockSet (ps : List Byte) (q : Nat) (blk : List Byte) : List Byte :=
  (List.range 500).map (fun i => if i / 125 = q then blk.getD (i % 125) 0 else ps.getD i 0)

/-! ### List facts -/

theorem get_eq (l : List Byte) (i : Nat) : get fast l i = l.getD i 0 := by
  simp [TlsWebSocketUpgrade.get, fast_const, List.getD_eq_getElem?_getD]

theorem range_set (n : Nat) (hn : n ≤ 256) (l : List Byte) (hl : l.length = n) (c : Byte) (hc : c.toNat < n)
    (b : Byte) :
    (List.range n).map (fun i => TlsInner.select fast (eq fast c i) b (get fast l i)) = l.set c.toNat b := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_set, eq_mb, select_mb]
    have hi : i < l.length := by simp at h1; omega
    by_cases hci : c.toNat = i
    · have : (c == BitVec.ofNat 8 i) = true := by
        simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simp; omega
      simp [this, hci]
    · have : (c == BitVec.ofNat 8 i) = false := by
        rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; intro e; apply hci; rw [e]; simp; omega
      simp [this, hci, TlsWebSocketUpgrade.get, List.getElem?_eq_getElem hi]

theorem range_block (q : Byte) (hq : q.toNat < 4) (blk ps : List Byte) :
    (List.range 500).map (fun i => TlsInner.select fast (eq fast q (i / 125)) (get fast blk (i % 125))
      (get fast ps i)) = blockSet ps q.toNat blk := by
  unfold blockSet
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [eq_mb, select_mb, get_eq, get_eq]
  by_cases h : q.toNat = i / 125
  · have : (q == BitVec.ofNat 8 (i / 125)) = true := by
      simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simp; omega
    simp [this, h]
  · have : (q == BitVec.ofNat 8 (i / 125)) = false := by
      rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; intro e; apply h; rw [e]; simp; omega
    simp [this, h]
    omega

theorem inc_value : ∀ x : Byte, TlsWebSocketControl.inc fast x = BitVec.ofNat 8 (x.toNat + 1) := by
  decide +kernel

/-! ### One step -/

/-- A queue with its lists at their lengths, its counts in range. -/
def Shaped (S : State Byte) : Prop :=
  S.data.length = 125 ∧ S.kinds.length = 4 ∧ S.lengths.length = 4 ∧ S.payloads.length = 500

theorem m255 : member fast 255#8 [0, 255] = 255#8 := by decide
theorem m0 : member fast 0#8 [0, 255] = 255#8 := by decide
theorem member_lt (x : Byte) (n : Nat) (hn : n ≤ 256) (h : x.toNat < n) : member fast x (List.range n) = 255#8 := by
  rw [member_range x n hn, if_pos h]; rfl

/-- No control data, no frame end, no opcode: nothing changes (any byte). -/
theorem step_idle (S : State Byte) (hS : Shaped S) (b : Byte) (hc : S.count.toNat < 126) (hq : S.queued.toNat < 5) :
    step fast S 0#8 0#8 0#8 b = S := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  obtain ⟨valid, count, data, queued, kinds, lengths, payloads⟩ := S
  simp only at hd hk hl hp hc hq
  simp only [step, member_lt count 126 (by decide) hc, member_lt queued 5 (by decide) hq, m0, and_zero_l,
    and_zero_r, select_zero', not_zero, and_ones_l, and_ones_r,
    choose_zero (List.replicate 125 (fast.const 0)) data (by simp [hd]),
    map_range_get _ _ hd, map_range_get _ _ hk, map_range_get _ _ hl, map_range_get _ _ hp]

/-- A payload byte of a control frame (not the last): stored at the count, the count goes up. -/
theorem step_collect (S : State Byte) (hS : Shaped S) (b : Byte) (hc : S.count.toNat < 125)
    (hq : S.queued.toNat < 5) :
    step fast S 255#8 0#8 0#8 b =
      { S with count := BitVec.ofNat 8 (S.count.toNat + 1), data := S.data.set S.count.toNat b } := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  have e125 : eq fast S.count 125 = 0#8 := by
    rw [eq_mb]; have : (S.count == BitVec.ofNat 8 125) = false := by
      rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; intro e; rw [e] at hc; simp at hc
    rw [this]; rfl
  simp only [step, and_ones_l, and_zero_l, select_ones', select_zero',
    member_lt S.count 126 (by decide) (by omega), member_lt S.queued 5 (by decide) hq, m255, m0, e125, inc_value,
    range_set 125 (by decide) S.data hd S.count hc b, not_zero, and_ones_r,
    choose_zero (List.replicate 125 (fast.const 0)) (S.data.set S.count.toNat b) (by simp [hd]),
    map_range_get _ _ hk, map_range_get _ _ hl, map_range_get _ _ hp]

/-- The reply kind queued for a Ping (9) or a Close (8): Pong (10) or Close (8). -/
def kindOf (o : Byte) : Byte := if o = 9#8 then 10#8 else 8#8

theorem e_ne (x : Byte) (n : Nat) (hn : n < 256) (h : x.toNat ≠ n) : eq fast x n = 0#8 := by
  rw [eq_mb]
  have : (x == BitVec.ofNat 8 n) = false := by
    rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; intro e; apply h; rw [e]; simp; omega
  rw [this]; rfl

theorem zeros_eq : List.replicate 125 (fast.const 0) = List.replicate 125 0#8 := by rw [fast_const]

/-- The last payload byte of a Ping or a Close: stored, the reply queued (kind, length, payload in
slot `queued`), the collection reset. -/
theorem step_finish (S : State Byte) (hS : Shaped S) (b o : Byte) (ho : o = 8#8 ∨ o = 9#8)
    (hc : S.count.toNat < 125) (hq : S.queued.toNat < 4) :
    step fast S 255#8 255#8 o b =
      { valid := S.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (S.queued.toNat + 1), kinds := S.kinds.set S.queued.toNat (kindOf o),
        lengths := S.lengths.set S.queued.toNat (BitVec.ofNat 8 (S.count.toNat + 1)),
        payloads := blockSet S.payloads S.queued.toNat (S.data.set S.count.toNat b) } := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  have e125 := e_ne S.count 125 (by decide) (by omega)
  have e4 := e_ne S.queued 4 (by decide) (by omega)
  have a1 : member fast 8#8 [8, 9] = 255#8 := by decide
  have a2 : member fast 8#8 [8, 9, 10] = 255#8 := by decide
  have a3 : eq fast 8#8 9 = 0#8 := by decide
  have b1 : member fast 9#8 [8, 9] = 255#8 := by decide
  have b2 : member fast 9#8 [8, 9, 10] = 255#8 := by decide
  have b3 : eq fast 9#8 9 = 255#8 := by decide
  rcases ho with rfl | rfl <;>
  · simp only [step, and_ones_l, and_zero_l, select_ones', select_zero', a1, a2, a3, b1, b2, b3,
      member_lt S.count 126 (by decide) (by omega), member_lt S.queued 5 (by decide) (by omega), m255, e125, e4,
      inc_value, range_set 125 (by decide) S.data hd S.count hc b, not_zero, not_ones, and_ones_r, fast_const,
      choose_ones (List.replicate 125 0#8) (S.data.set S.count.toNat b) (by simp [hd]),
      range_set 4 (by decide) S.kinds hk S.queued hq, range_set 4 (by decide) S.lengths hl S.queued hq,
      range_block S.queued hq]
    rfl

/-- The last payload byte of a Pong: nothing is queued, the collection is reset. -/
theorem step_finish_pong (S : State Byte) (hS : Shaped S) (b : Byte)
    (hc : S.count.toNat < 125) (hq : S.queued.toNat < 5) :
    step fast S 255#8 255#8 10#8 b = { S with count := 0#8, data := List.replicate 125 0#8 } := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  have e125 := e_ne S.count 125 (by decide) (by omega)
  have m89 : member fast 10#8 [8, 9] = 0#8 := by decide
  have m8910 : member fast 10#8 [8, 9, 10] = 255#8 := by decide
  simp only [step, and_ones_l, and_zero_l, select_ones', select_zero', m89, m8910,
    member_lt S.count 126 (by decide) (by omega), member_lt S.queued 5 (by decide) hq, m255, e125,
    inc_value, range_set 125 (by decide) S.data hd S.count hc b, not_zero, not_ones, and_ones_r, and_zero_r,
    fast_const, choose_ones (List.replicate 125 0#8) (S.data.set S.count.toNat b) (by simp [hd]),
    map_range_get _ _ hk, map_range_get _ _ hl, map_range_get _ _ hp]

/-- The end of a Ping or a Close with no payload (its last header byte): the reply queued with length
0 and the (empty) collected data. -/
theorem step_finish_empty (S : State Byte) (hS : Shaped S) (b o : Byte) (ho : o = 8#8 ∨ o = 9#8)
    (hc : S.count.toNat < 126) (hq : S.queued.toNat < 4) :
    step fast S 0#8 255#8 o b =
      { valid := S.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (S.queued.toNat + 1), kinds := S.kinds.set S.queued.toNat (kindOf o),
        lengths := S.lengths.set S.queued.toNat S.count,
        payloads := blockSet S.payloads S.queued.toNat S.data } := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  have e4 := e_ne S.queued 4 (by decide) (by omega)
  have a1 : member fast 8#8 [8, 9] = 255#8 := by decide
  have a2 : member fast 8#8 [8, 9, 10] = 255#8 := by decide
  have a3 : eq fast 8#8 9 = 0#8 := by decide
  have b1 : member fast 9#8 [8, 9] = 255#8 := by decide
  have b2 : member fast 9#8 [8, 9, 10] = 255#8 := by decide
  have b3 : eq fast 9#8 9 = 255#8 := by decide
  rcases ho with rfl | rfl <;>
  · simp only [step, and_ones_l, and_zero_l, select_ones', select_zero', a1, a2, a3, b1, b2, b3,
      member_lt S.count 126 (by decide) hc, member_lt S.queued 5 (by decide) (by omega), m0, m255, e4,
      inc_value, map_range_get _ _ hd, not_zero, not_ones, and_ones_r, and_zero_r, fast_const,
      choose_ones (List.replicate 125 0#8) S.data (by simp [hd]),
      range_set 4 (by decide) S.kinds hk S.queued hq, range_set 4 (by decide) S.lengths hl S.queued hq,
      range_block S.queued hq]
    rfl

/-! ### A whole control frame -/

/-- The queue over a list of inputs (control data, control done, control kind, byte). -/
def runC : State Byte → List (Byte × Byte × Byte × Byte) → State Byte
  | S, [] => S
  | S, (d, e, o, b) :: xs => runC (step fast S d e o b) xs

theorem runC_append : ∀ (S : State Byte) (a c : List (Byte × Byte × Byte × Byte)),
    runC S (a ++ c) = runC (runC S a) c
  | _, [], _ => rfl
  | S, (d, e, o, b) :: xs, c => by simp only [List.cons_append, runC]; exact runC_append _ xs c

/-- The frame parser's control inputs for a header byte, a payload byte that does not end the frame. -/
def idleIn (h : Byte) : Byte × Byte × Byte × Byte := (0#8, 0#8, 0#8, h)
def collectIn (x : Byte) : Byte × Byte × Byte × Byte := (255#8, 0#8, 0#8, x)

/-- Waiting for a control frame: nothing collected, room for one more reply. -/
def Idle (S : State Byte) : Prop :=
  Shaped S ∧ S.count = 0#8 ∧ S.data = List.replicate 125 0#8 ∧ S.queued.toNat < 4

theorem header_run (S : State Byte) (hS : Shaped S) (hc : S.count.toNat < 126) (hq : S.queued.toNat < 5) :
    ∀ hs : List Byte, runC S (hs.map idleIn) = S
  | [] => rfl
  | h :: hs => by
      simp only [List.map_cons, runC, idleIn]
      rw [step_idle S hS h hc hq]
      exact header_run S hS hc hq hs

theorem set_pad (q0 : List Byte) (m : Nat) (hm : 1 ≤ m) (x : Byte) :
    (q0 ++ List.replicate m 0#8).set q0.length x = (q0 ++ [x]) ++ List.replicate (m - 1) 0#8 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.replicate_succ, List.set_cons_zero]
  simp

theorem collect_run : ∀ (p q0 : List Byte) (S : State Byte), Shaped S →
    S.data = q0 ++ List.replicate (125 - q0.length) 0#8 → S.count = BitVec.ofNat 8 q0.length →
    q0.length + p.length < 125 → S.queued.toNat < 5 →
    runC S (p.map collectIn) =
      { S with count := BitVec.ofNat 8 (q0.length + p.length),
               data := (q0 ++ p) ++ List.replicate (125 - q0.length - p.length) 0#8 }
  | [], q0, S, _, hd, hc, _, _ => by
      simp only [List.map_nil, runC, List.length_nil, Nat.add_zero, List.append_nil, Nat.sub_zero]
      rw [← hd, ← hc]
  | x :: p, q0, S, hS, hd, hc, hl, hq => by
      have hl' : q0.length + p.length + 1 < 125 := by simp only [List.length_cons] at hl; omega
      have hct : S.count.toNat = q0.length := by rw [hc]; simp; omega
      simp only [List.map_cons, runC, collectIn]
      rw [step_collect S hS x (by omega) hq, hct, hd, set_pad q0 _ (by omega) x]
      have ih := collect_run p (q0 ++ [x])
        { S with count := BitVec.ofNat 8 (q0.length + 1),
                 data := q0 ++ [x] ++ List.replicate (125 - q0.length - 1) 0#8 }
        ⟨by obtain ⟨hd', _⟩ := hS; simp; omega, hS.2.1, hS.2.2.1, hS.2.2.2⟩
        (by simp; omega) (by simp) (by simp at hl ⊢; omega) hq
      rw [ih]
      have e1 : (q0 ++ [x]).length + p.length = q0.length + (x :: p).length := by simp; omega
      have e2 : 125 - (q0 ++ [x]).length - p.length = 125 - q0.length - (x :: p).length := by simp; omega
      have e3 : q0 ++ [x] ++ p = q0 ++ x :: p := by simp
      rw [e1, e2, e3]

/-- **`control_frame`.** A Ping or a Close with payload `p ++ [b]` (1 to 125 bytes), from an idle
queue: its header bytes, its payload bytes, the last one ending the frame. The queue is idle again
with `reply`'s answer appended in slot `q`: the kind (`kindOf`: Pong for a Ping, Close for a Close),
the length, and the payload padded with zeros. -/
theorem control_frame (S : State Byte) (hI : Idle S) (hs p : List Byte) (b o : Byte)
    (ho : o = 8#8 ∨ o = 9#8) (hn : p.length + 1 ≤ 125) :
    runC S (hs.map idleIn ++ p.map collectIn ++ [(255#8, 255#8, o, b)]) =
      { valid := S.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (S.queued.toNat + 1), kinds := S.kinds.set S.queued.toNat (kindOf o),
        lengths := S.lengths.set S.queued.toNat (BitVec.ofNat 8 (p.length + 1)),
        payloads := blockSet S.payloads S.queued.toNat ((p ++ [b]) ++ List.replicate (125 - (p.length + 1)) 0#8) } := by
  obtain ⟨hS, hc, hd, hq⟩ := hI
  rw [runC_append, runC_append, header_run S hS (by rw [hc]; decide) (by omega)]
  rw [collect_run p [] S hS (by simpa using hd) (by simpa using hc) (by simp; omega) (by omega)]
  simp only [List.length_nil, Nat.zero_add, List.nil_append, Nat.sub_zero, runC]
  rw [step_finish { S with count := BitVec.ofNat 8 p.length, data := p ++ List.replicate (125 - p.length) 0#8 }
    ⟨by simp; omega, hS.2.1, hS.2.2.1, hS.2.2.2⟩ b o ho (by simp; omega) hq]
  have hp : (BitVec.ofNat 8 p.length).toNat = p.length := by simp; omega
  simp only [hp]
  rw [set_pad p _ (by omega) b, Nat.sub_sub]

/-- A Pong with payload `p ++ [b]`: the queue is unchanged. -/
theorem control_frame_pong (S : State Byte) (hI : Idle S) (hs p : List Byte) (b : Byte)
    (hn : p.length + 1 ≤ 125) :
    runC S (hs.map idleIn ++ p.map collectIn ++ [(255#8, 255#8, 10#8, b)]) = S := by
  obtain ⟨hS, hc, hd, hq⟩ := hI
  rw [runC_append, runC_append, header_run S hS (by rw [hc]; decide) (by omega)]
  rw [collect_run p [] S hS (by simpa using hd) (by simpa using hc) (by simp; omega) (by omega)]
  simp only [List.length_nil, Nat.zero_add, List.nil_append, Nat.sub_zero, runC]
  rw [step_finish_pong { S with count := BitVec.ofNat 8 p.length, data := p ++ List.replicate (125 - p.length) 0#8 }
    ⟨by simp; omega, hS.2.1, hS.2.2.1, hS.2.2.2⟩ b (by simp; omega) (show S.queued.toNat < 5 by omega)]
  obtain ⟨v, c, d, q, k, l, ps⟩ := S
  simp only at hc hd
  subst hc hd
  rfl

/-- A Ping or a Close with no payload: the reply is queued with length 0 and an all-zero slot. -/
theorem control_frame_empty (S : State Byte) (hI : Idle S) (hs : List Byte) (h o : Byte)
    (ho : o = 8#8 ∨ o = 9#8) :
    runC S (hs.map idleIn ++ [(0#8, 255#8, o, h)]) =
      { valid := S.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (S.queued.toNat + 1), kinds := S.kinds.set S.queued.toNat (kindOf o),
        lengths := S.lengths.set S.queued.toNat 0#8,
        payloads := blockSet S.payloads S.queued.toNat (List.replicate 125 0#8) } := by
  obtain ⟨hS, hc, hd, hq⟩ := hI
  rw [runC_append, header_run S hS (by rw [hc]; decide) (by omega)]
  simp only [runC]
  rw [step_finish_empty S hS h o ho (by rw [hc]; decide) hq, hc, hd]

/-! ### `run`, as the controller calls it -/

theorem readState_stateBytes (S : State Byte) (hS : Shaped S) :
    TlsWebSocketControl.readState fast (TlsWebSocketControl.stateBytes S) = S := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  obtain ⟨v, c, d, q, k, l, ps⟩ := S
  simp only at hd hk hl hp
  have e1 : List.drop 126 (d ++ q :: (k ++ (l ++ ps))) = k ++ (l ++ ps) := by
    simp [List.drop_append, hd]
  have e2 : List.drop 130 (d ++ q :: (k ++ (l ++ ps))) = l ++ ps := by
    simp [List.drop_append, hd, hk]
  have e3 : List.drop 134 (d ++ q :: (k ++ (l ++ ps))) = ps := by
    simp [List.drop_append, hd, hk, hl, List.drop_eq_nil_of_le (show d.length ≤ 134 by omega),
      List.drop_eq_nil_of_le (show k.length ≤ 8 by omega)]
  simp [TlsWebSocketControl.readState, TlsWebSocketControl.stateBytes, TlsWebSocketUpgrade.get, hd, hk, hl, hp,
    List.getElem?_append_right, List.getElem?_append_left, e1, e2, e3, List.take_left' hk,
    List.take_of_length_le (show ps.length ≤ 500 by omega)]

theorem stateBytes_length (S : State Byte) (hS : Shaped S) : (TlsWebSocketControl.stateBytes S).length = 636 := by
  obtain ⟨hd, hk, hl, hp⟩ := hS
  simp [TlsWebSocketControl.stateBytes, hd, hk, hl, hp]

/-- **`run_stateBytes`.** `run` on the serialised queue and the four inputs is `step`. -/
theorem run_stateBytes (S : State Byte) (hS : Shaped S) (d e o b : Byte) :
    TlsWebSocketControl.run fast (TlsWebSocketControl.stateBytes S ++ [d, e, o, b]) =
      TlsWebSocketControl.stateBytes (step fast S d e o b) := by
  have hlen := stateBytes_length S hS
  unfold TlsWebSocketControl.run
  rw [List.take_left' hlen, readState_stateBytes S hS]
  simp [TlsWebSocketUpgrade.get, List.getElem?_append_right, hlen]

/-! ### The reply frame -/

theorem xor128 : ∀ x : Byte, x.toNat < 128 → 128#8 ^^^ x = BitVec.ofNat 8 (128 + x.toNat) := by decide +kernel

theorem addSix_fast (x : Byte) : TlsWebSocketControl.addSix fast x = BitVec.ofNat 8 (x.toNat + 6) := by
  rw [PublicReceive.fast_eq]; exact TlsWebSocketControl.addSix_value x

/-- **`encode_frame`.** What `replies` sends for a queued reply (`encode` on the queue's validity
byte 255, a zero, the length, the kind, the masking key and the 125-byte slot): validity 255, then 0
and the frame's length, then RFC 6455's masked client frame with that kind and the slot's first
`length` bytes as payload. -/
theorem encode_frame (kind len : Byte) (hk : kind = 8#8 ∨ kind = 10#8) (hl : len.toNat ≤ 125)
    (key blk : List Byte) (hkey : key.length = 4) (hblk : blk.length = 125) :
    (TlsWebSocketControl.encode fast ([255#8, 0#8, len, kind] ++ key ++ blk)).take 3 =
      [255#8, 0#8, BitVec.ofNat 8 (len.toNat + 6)] ∧
    ((TlsWebSocketControl.encode fast ([255#8, 0#8, len, kind] ++ key ++ blk)).drop 3).take (len.toNat + 6) =
      clientFrame kind.toNat key (blk.take len.toNat) := by
  obtain ⟨k0, k1, k2, k3, rfl⟩ := PublicReceive.PassOver.len4 key hkey
  have hv : TlsWebSocketControl.encode fast ([255#8, 0#8, len, kind] ++ [k0, k1, k2, k3] ++ blk) =
      255#8 :: (0#8 :: BitVec.ofNat 8 (len.toNat + 6) ::
        ([128#8 ^^^ kind, 128#8 ^^^ len, k0, k1, k2, k3] ++
          (List.range 125).map (fun i => blk.getD i 0 ^^^ [k0, k1, k2, k3].getD (i % 4) 0))) := by
    have f125 : TlsWebSocketFrame.fits fast 125 0#8 len = 255#8 := by
      rw [TlsMpc.KernelSpecs.ParseWebSocketFrame.fits_mb 125 (by decide)]
      have : decide (TlsWebSocketFrame.wordValue 0#8 len ≤ 125) = true := by
        simp [TlsWebSocketFrame.wordValue]; omega
      rw [this]; rfl
    have mk : member fast kind [8, 10] = 255#8 := by rcases hk with rfl | rfl <;> decide
    have e255 : eq fast 255#8 255 = 255#8 := by decide
    have hk4 : List.take 4 (List.drop 4 (255#8 :: 0#8 :: len :: kind :: k0 :: k1 :: k2 :: k3 :: blk)) =
        [k0, k1, k2, k3] := rfl
    have hm : (List.range 125).map (fun i =>
        fast.xor ((255#8 :: 0#8 :: len :: kind :: k0 :: k1 :: k2 :: k3 :: blk).getD (8 + i) 0)
          ((255#8 :: 0#8 :: len :: kind :: k0 :: k1 :: k2 :: k3 :: blk).getD (4 + i % 4) 0)) =
        (List.range 125).map (fun i => blk.getD i 0 ^^^ [k0, k1, k2, k3].getD (i % 4) 0) := by
      apply List.map_congr_left
      intro i _
      have g8 : (255#8 :: 0#8 :: len :: kind :: k0 :: k1 :: k2 :: k3 :: blk).getD (8 + i) 0 = blk.getD i 0 := by
        rw [Nat.add_comm]; rfl
      have g4 : (255#8 :: 0#8 :: len :: kind :: k0 :: k1 :: k2 :: k3 :: blk).getD (4 + i % 4) 0 =
          [k0, k1, k2, k3].getD (i % 4) 0 := by
        rcases (show i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 by omega) with h | h | h | h <;> rw [h] <;> rfl
      rw [g8, g4]; rfl
    have ma : ∀ l : List Byte, l.map (fast.and 255#8) = l := by
      intro l; induction l with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons, and_ones_l, ih]
    unfold TlsWebSocketControl.encode
    simp only [get_eq, List.getD_cons_zero, List.getD_cons_succ, List.cons_append, List.nil_append, e255, f125,
      mk, and_ones_l, ByteAuth.release, addSix_fast, fast_const]
    rw [ma, hk4, hm]
    rfl
  rw [hv]
  refine ⟨rfl, ?_⟩
  have hkind : kind.toNat < 128 := by rcases hk with rfl | rfl <;> decide
  have ht : (blk.take len.toNat).length = len.toNat := by simp; omega
  simp only [List.drop_succ_cons, List.drop_zero, clientFrame, ht, xor128 kind hkind, xor128 len (by omega)]
  simp only [show len.toNat + 6 = len.toNat + 1 + 1 + 1 + 1 + 1 + 1 by omega, List.cons_append, List.nil_append,
    List.take_succ_cons, ← List.map_take, List.take_range, Nat.min_eq_left (show len.toNat ≤ 125 by omega),
    List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

/-- What is queued is the reference's reply. -/
theorem kindOf_reply (o : Byte) (ho : o = 8#8 ∨ o = 9#8) (payload : List Byte) :
    reply o.toNat payload = some ((kindOf o).toNat, payload) := by
  rcases ho with rfl | rfl <;> rfl

/-! ### One masking key per reply (RFC 6455 section 5.3; fixed in stage S4)

`replies` took one key for every reply of a drain (the counterexample `replies_reuse_mask`, now
deleted: two Pongs both masked with `01 02 03 04`). Since stage S4 it takes one key per queued reply
(`masks[i]` for reply `i`), and the controller draws each from its own joint randomness
(`controlMasks` in `PublicServiceController.lean`). -/

/-- A queue holding two Pong replies (payloads `A` and `B`), as two Pings would leave it. -/
def twoPongs : List Byte :=
  TlsWebSocketControl.stateBytes
    ({ valid := 255, count := 0, data := List.replicate 125 0, queued := 2, kinds := [10, 10, 0, 0],
       lengths := [1, 1, 0, 0],
       payloads := [0x41] ++ List.replicate 124 0 ++ [0x42] ++ List.replicate 374 0 } : State Byte)

def framesOf (r : Except String (PublicReceive.State × List (Nat × List Byte))) : List (Nat × List Byte) :=
  match r with
  | .ok (_, fs) => fs
  | .error _ => []

/-- **`replies_fresh_masks`.** `PublicReceive.replies` on two queued Pongs with the keys
`01 02 03 04` and `05 06 07 08` masks each frame with its own key (bytes 2–5 of each frame, and the
payloads `A`, `B` XOR their key's first byte). RFC 6455 section 5.3: a fresh masking key for each
frame. -/
theorem replies_fresh_masks :
    framesOf (PublicReceive.replies { PublicReceive.start [] with control := twoPongs } [[1, 2, 3, 4], [5, 6, 7, 8]]) =
      [(10, [0x8a, 0x81, 1, 2, 3, 4, 0x40]), (10, [0x8a, 0x81, 5, 6, 7, 8, 0x47])] := by
  decide +kernel

/-- With fewer keys than queued replies, `replies` refuses (no reply is sent with a missing or
reused key). -/
theorem replies_missing_mask :
    framesOf (PublicReceive.replies { PublicReceive.start [] with control := twoPongs } [[1, 2, 3, 4]]) = [] := by
  decide +kernel

end TlsMpc.KernelSpecs.ParseWebSocketControl
