import TlsMpc.KernelSpecs.ParseWebSocketFrame

/-!
# The controller's WebSocket frame parser accepts RFC 6455's well-formed server frames

New file; it changes no definition and no emitter imports it.

`ParseWebSocketFrame` proved which bytes the deployed frame parser (`TlsWebSocketFrame.step` on
`PublicReceive.fast`, as the controller runs it through `runByte`: `controller_run` there) reports as
payload, gated by its validity byte, and that malformed headers drop that byte. Here: the converse,
that a well-formed frame keeps it at 255 through the whole frame.

## The reference (additions to `parseHeader` / `Header.wellFormed`)

* `Accepts cap c h payload`: `Header.wellFormed` (no reserved bit, a defined opcode, unmasked,
  minimal length encoding, control frames final and at most 125 bytes), not text (opcode 1; this is
  a binary profile), length within `cap`, RFC 6455 section 5.4's fragmentation rules against the
  context `c` (a continuation only inside a fragmented message and within its capacity left, a new
  binary message only outside one), and for a Close (section 5.5.1) a payload that is empty or a
  status code followed by a UTF-8 reason (`CloseBody`).
* `validCloseCode`: section 7.4 and the IANA registry: 1000–1003, 1007–1014, 3000–4999.
* `Utf8Char` / `Utf8`: RFC 3629 section 4's ABNF, one constructor per row; `delta` / `drun` the same
  grammar read left to right (`utf8_drun`).
* `Ctx`, `Ctx.after`: the context between frames (fragmented message in progress, capacity left),
  and how a frame changes it. `Boundary S c closed`: the parser's state at a frame boundary.

## What is proved (standard axioms only; no `sorry`, `native_decide`, `bv_decide`)

* One step per kind of byte, as an equation for the whole event (`acc_first`, `acc_short`,
  `acc_empty_data`, `acc_empty_control`, `acc_extended`, `acc_high`, `acc_low`, `acc_data`,
  `acc_data_last`, `acc_ping`, `acc_ping_last`, `acc_close1`, `acc_close2`, `acc_close2_last`,
  `acc_reason`, `acc_reason_last`); `utf_step`: the parser's UTF-8 automaton is `delta`;
  `closeCode_value`: its status-code check is `validCloseCode`.
* **`frame_accept`**: from a boundary in context `c`, over a frame that `parseHeader` reads (7- or
  16-bit length, `f` exactly header and payload) and that the reference `Accepts`: every event's
  validity byte is 255, and the parser ends at a boundary in context `c.after cap h`, closed exactly
  after a Close. **`frame_exact`**: with `frame_extent`, the `data` / `controlData` / `frameDone`
  bytes are then exactly the reference's. **`frames_accept`**: any sequence of accepted frames
  (`FramesOk`, nothing after a Close).
* Payload-level rejections, one step each (the header-level ones are `reject_*` in
  `ParseWebSocketFrame`): `reject_close_one` (1-byte Close), `reject_message_full` (message capacity
  exhausted), `reject_reason` (a byte no UTF-8 character continues with), `reject_close_code`,
  `reject_reason_code` (invalid code), `reject_reason_unfinished` (reason ends inside a character).

So for the covered shapes (unmasked, 7- or 16-bit lengths: every frame a server may send within
capacity) a frame is accepted iff it is well-formed: acceptance here, and each way of being
malformed has its rejecting step (`reject_*` here and in `ParseWebSocketFrame`). Not proved as one
theorem: the "only if" direction over a whole frame (that the first malformed byte is reached with
the state the acceptance lemmas describe), and that a reason the automaton accepts is RFC 3629
UTF-8 (`drun 0 r = some 0 → Utf8 r`; `utf8_drun` is the other direction).
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open TlsMpc.KernelSpecs.ParseWebSocketFrame
open TlsWebSocketUpgrade (get eq either any member choose initial)
open TlsWebSocketFrame (State Event step wordValue utfStep)
open PublicReceive.PassOver (fast_and fast_const fast_maskBit eq_fast select_zero select_ones select_zero'
  select_ones' and_ones dec_fast hiOf loOf wordValue_of wordValue_lt member_range choose_ones choose_zero
  utfStep_length)

set_option linter.unusedSimpArgs false

namespace TlsMpc.KernelSpecs.ParseWebSocketAccept

theorem initial_length : (initial fast 7).length = 8 := rfl
theorem initial_get0 : (initial fast 7)[0]? = some 255#8 := rfl
theorem fast_and_lit (x y : Nat) : fast.and (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) =
    BitVec.ofNat 8 x &&& BitVec.ofNat 8 y := rfl

/-- The UTF-8 automaton's state `i` (one-hot, 8 states). -/
def U (i : Nat) : List Byte :=
  [mb (i == 0), mb (i == 1), mb (i == 2), mb (i == 3), mb (i == 4), mb (i == 5), mb (i == 6), mb (i == 7)]
theorem U_length (i : Nat) : (U i).length = 8 := rfl
theorem U_get0 (i : Nat) : (U i)[0]? = some (mb (i == 0)) := rfl
theorem any_U : ∀ i, i < 8 → any fast (U i) = 255#8
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | _ + 8, h => by omega
theorem initial_U : initial fast 7 = U 0 := by decide
theorem initial_getElem0 (h : 0 < (initial fast 7).length) : (initial fast 7)[0]'h = 255#8 := rfl
theorem U_getElem0 (h : 0 < (U 0).length) : (U 0)[0]'h = 255#8 := rfl
theorem U_getElem (i : Nat) (h : 0 < (U i).length) : (U i)[0]'h = mb (i == 0) := rfl

theorem len_eq1 : ∀ x : Byte, (fast.and x 127#8 == 1#8) = (x.toNat % 128 == 1) := by decide +kernel

syntax "acc_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| acc_simp [$ts,*]) => `(tactic|
       simp [TlsWebSocketFrame.step, P, TlsWebSocketUpgrade.get, and_mb, not_mb, either, eq_mb,
        maskBit_mb, member_mb, select_mb, fast_const, TlsWebSocketFrame.zero, TlsWebSocketFrame.one,
        TlsWebSocketFrame.dataKind, TlsWebSocketFrame.control,
        and_ones_l, and_ones_r, and_zero_l, and_zero_r, not_ones, not_zero, select_ones', select_zero',
        beq_mb_zero, beq_mb_ones, choose_zero, choose_ones, utfStep_length, initial_length, fast_and_lit,
        initial_get0, U_length, U_get0, initial_getElem0, U_getElem0, $ts,*])

/-- The first header byte of a frame: FIN, no reserved bit, opcode `k`. -/
def firstByte (fin : Bool) (k : Nat) : Byte := BitVec.ofNat 8 ((if fin then 128 else 0) + k)

/-- RFC 6455 sections 5.2, 5.4, 5.5 on the first header byte, in this profile: a continuation only
inside a fragmented message, a new binary message only outside one, a control frame final. -/
def FirstOk (frag fin : Bool) (k : Nat) : Prop :=
  (k = 0 ∧ frag = true) ∨ (k = 2 ∧ frag = false) ∨ ((k = 8 ∨ k = 9 ∨ k = 10) ∧ fin = true)

theorem acc_first (cap : Nat) (op fn : Byte) (frag : Bool) (hi lo mh ml pf ps ch cv : Byte) (u : List Byte)
    (hu : u.length = 8) (fin : Bool) (k : Nat) (hk : FirstOk frag fin k) :
    step fast cap ⟨P 0, 255#8, 0#8, op, fn, mb frag, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ (firstByte fin k) =
      ⟨⟨P 1, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, mb frag, hi, lo,
        if k = 2 then BitVec.ofNat 8 (cap / 256) else mh, if k = 2 then BitVec.ofNat 8 cap else ml,
        pf, ps, ch, cv, u⟩, 0#8, 0#8, mb (k == 2), 0#8, 0#8, 0#8, 0#8⟩ := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hk, rfl⟩
  · cases fin <;> acc_simp [firstByte, hu]
  · cases fin <;> acc_simp [firstByte, hu]
  · rcases hk with rfl | rfl | rfl <;> acc_simp [firstByte, hu]

/-- An opcode of this profile: continuation, binary, Close, Ping, Pong. -/
def Op (k : Nat) : Prop := k = 0 ∨ k = 2 ∨ k = 8 ∨ k = 9 ∨ k = 10

/-- Second header byte, unmasked, 7-bit length 1–125 within capacity (not 1 for a Close, whose
payload is empty or starts with a 2-byte code): the payload comes next. -/
theorem acc_short (cap : Nat) (hcap : cap < 65536) (k : Nat) (hk : Op k) (fn fr hi lo mh ml pf ps ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hm : x.toNat < 128) (hl : x.toNat ≤ 125) (hz : x.toNat ≠ 0)
    (hc : x.toNat ≤ cap) (h1 : k = 8 → x.toNat ≠ 1) :
    step fast cap ⟨P 1, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, 0#8, fast.and x 127#8, mh, ml, 255#8, 0#8, 0#8, 0#8,
        initial fast 7⟩, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  have h126 : (x.toNat % 128 == 126) = false := by rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; omega
  have h127 : (x.toNat % 128 == 127) = false := by rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; omega
  have h0 : (x.toNat % 128 == 0) = false := by rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  have hf : TlsWebSocketFrame.fits fast cap 0#8 (fast.and x 127#8) = 255#8 := by
    rw [fits_mb cap hcap, word_short, decide_eq_true (by omega)]; rfl
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · acc_simp [hu, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7, hf]
  · acc_simp [hu, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7, hf]
  · have h1' : (x.toNat % 128 == 1) = false := by
      have := h1 rfl; rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; omega
    acc_simp [hu, len_eq x, len_eq7 x, len_eq0 x, len_eq1 x, bit7 x, h126, h127, h0, h7, hf, h1']
  · acc_simp [hu, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7, hf]
  · acc_simp [hu, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7, hf]

/-- Second header byte, unmasked, length 0, data frame: the frame ends here. -/
theorem acc_empty_data (cap : Nat) (hcap : cap < 65536) (k : Nat) (hk : k = 0 ∨ k = 2) (fin : Bool)
    (fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte) (hu : u.length = 8) :
    step fast cap ⟨P 1, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ 0#8 =
      ⟨⟨P 0, 255#8, 0#8, 0#8, 0#8, mb (!fin), 0#8, 0#8,
        if fin then BitVec.ofNat 8 (cap / 256) else mh, if fin then BitVec.ofNat 8 cap else ml,
        0#8, 0#8, 0#8, 0#8, initial fast 7⟩, 0#8, 0#8, 0#8, 255#8, mb fin, 0#8, 0#8⟩ := by
  have hf : TlsWebSocketFrame.fits fast cap 0#8 0#8 = 255#8 := by
    rw [fits_mb cap hcap]; simp [wordValue]
  rcases hk with rfl | rfl <;> cases fin <;> acc_simp [hu, hf]

/-- Second header byte, unmasked, length 0, control frame: the frame ends here; a Close closes. -/
theorem acc_empty_control (cap : Nat) (hcap : cap < 65536) (k : Nat) (hk : k = 8 ∨ k = 9 ∨ k = 10)
    (fn fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte) (hu : u.length = 8) :
    step fast cap ⟨P 1, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ 0#8 =
      ⟨⟨P 0, 255#8, mb (k == 8), 0#8, 0#8, fr, 0#8, 0#8, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩,
        0#8, 0#8, 0#8, 255#8, 0#8, 255#8, BitVec.ofNat 8 k⟩ := by
  have hf : TlsWebSocketFrame.fits fast cap 0#8 0#8 = 255#8 := by
    rw [fits_mb cap hcap]; simp [wordValue]
  rcases hk with rfl | rfl | rfl <;> acc_simp [hu, hf]

/-- Second header byte, unmasked, 16-bit length code, data frame. -/
theorem acc_extended (cap : Nat) (k : Nat) (hk : k = 0 ∨ k = 2)
    (fn fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte) (hu : u.length = 8) :
    step fast cap ⟨P 1, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ 126#8 =
      ⟨⟨P 2, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩,
        0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  rcases hk with rfl | rfl <;> acc_simp [hu]

/-- The 16-bit length's high byte. -/
theorem acc_high (cap : Nat) (k : Nat) (hk : k = 0 ∨ k = 2)
    (fn fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte) (hu : u.length = 8) (x : Byte) :
    step fast cap ⟨P 2, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 3, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, x, lo, mh, ml, pf, ps, ch, cv, u⟩,
        0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  rcases hk with rfl | rfl <;> acc_simp [hu]

/-- The 16-bit length's low byte: canonical (at least 126) and within capacity. -/
theorem acc_low (cap : Nat) (hcap : cap < 65536) (k : Nat) (hk : k = 0 ∨ k = 2)
    (fn fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte) (hu : u.length = 8) (x : Byte)
    (h126 : 126 ≤ wordValue hi x) (hc : wordValue hi x ≤ cap) :
    step fast cap ⟨P 3, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, x, mh, ml, 255#8, 0#8, 0#8, 0#8, initial fast 7⟩,
        0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  have hf : TlsWebSocketFrame.fits fast cap hi x = 255#8 := by
    rw [fits_mb cap hcap, decide_eq_true hc]; rfl
  have hz : (hi == 0#8 && x == 0#8) = false := by rw [zero_word]; simp; omega
  by_cases h0 : hi = 0#8
  · subst h0
    have hx : x.toNat ≥ 126 := by simp [wordValue] at h126; omega
    have hm : member fast x (List.range 126) = 0#8 := by
      rw [member_range x 126 (by decide), if_neg (by omega)]; rfl
    have hx0 : (x == 0#8) = false := by
      rw [Bool.eq_false_iff]; intro e; simp at e; subst e; simp at hx
    rcases hk with rfl | rfl <;> acc_simp [hu, hf, hm, hx0]
  · have h0' : (hi == 0#8) = false := by simpa using h0
    rcases hk with rfl | rfl <;> acc_simp [hu, hf, h0', hz]

/-! ### Payload bytes -/

theorem one_false (hi lo : Byte) (h : 2 ≤ wordValue hi lo) : (hi == 0#8 && lo == 1#8) = false := by
  rw [one_word]; simp; omega
theorem one_true (hi lo : Byte) (h : wordValue hi lo = 1) : (hi == 0#8 && lo == 1#8) = true := by
  rw [one_word]; simp; omega
theorem zero_false (hi lo : Byte) (h : 1 ≤ wordValue hi lo) : (hi == 0#8 && lo == 0#8) = false := by
  rw [zero_word]; simp; omega

/-- A data payload byte that is not the frame's last, message capacity left. -/
theorem acc_data (cap : Nat) (k : Nat) (hk : k = 0 ∨ k = 2) (fn fr hi lo mh ml pf ps ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hn : 2 ≤ wordValue hi lo) (hm : 1 ≤ wordValue mh ml) :
    step fast cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hiOf (wordValue hi lo - 1), loOf (wordValue hi lo - 1),
        hiOf (wordValue mh ml - 1), loOf (wordValue mh ml - 1), 0#8, pf, ch, cv, u⟩,
        255#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  rcases hk with rfl | rfl <;>
    acc_simp [hu, one_false hi lo hn, zero_false mh ml hm, dec_fast hi lo (by omega), dec_fast mh ml hm]

/-- The last payload byte of a data frame: the frame ends; a final frame ends the message (its
capacity is restored), a non-final one leaves it fragmented. -/
theorem acc_data_last (cap : Nat) (k : Nat) (hk : k = 0 ∨ k = 2) (fin : Bool) (fr hi lo mh ml pf ps ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hn : wordValue hi lo = 1) (hm : 1 ≤ wordValue mh ml) :
    step fast cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 0, 255#8, 0#8, 0#8, 0#8, mb (!fin), hiOf 0, loOf 0,
        if fin then BitVec.ofNat 8 (cap / 256) else hiOf (wordValue mh ml - 1),
        if fin then BitVec.ofNat 8 cap else loOf (wordValue mh ml - 1), 0#8, 0#8, 0#8, 0#8, initial fast 7⟩,
        255#8, 0#8, 0#8, 255#8, mb fin, 0#8, 0#8⟩ := by
  rcases hk with rfl | rfl <;> cases fin <;>
    acc_simp [hu, one_true hi lo hn, zero_false mh ml hm, dec_fast hi lo (by omega), dec_fast mh ml hm, hn]

/-- A Ping or Pong payload byte that is not the frame's last. -/
theorem acc_ping (cap : Nat) (k : Nat) (hk : k = 9 ∨ k = 10) (fn fr hi lo mh ml pf ps ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hn : 2 ≤ wordValue hi lo) :
    step fast cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hiOf (wordValue hi lo - 1), loOf (wordValue hi lo - 1),
        mh, ml, 0#8, pf, ch, cv, u⟩, 0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  rcases hk with rfl | rfl <;> acc_simp [hu, one_false hi lo hn, dec_fast hi lo (by omega)]

/-- The last payload byte of a Ping or Pong: the frame and the control frame end. -/
theorem acc_ping_last (cap : Nat) (k : Nat) (hk : k = 9 ∨ k = 10) (fn fr hi lo mh ml pf ps ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hn : wordValue hi lo = 1) :
    step fast cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ x =
      ⟨⟨P 0, 255#8, 0#8, 0#8, 0#8, fr, hiOf 0, loOf 0, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩,
        0#8, 255#8, 0#8, 255#8, 0#8, 255#8, BitVec.ofNat 8 k⟩ := by
  rcases hk with rfl | rfl <;> acc_simp [hu, one_true hi lo hn, dec_fast hi lo (by omega), hn]

/-- A Close's first payload byte (the status code's high byte; never the last, the payload being
empty or at least 2 bytes). -/
theorem acc_close1 (cap : Nat) (fn fr hi lo mh ml ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hn : 2 ≤ wordValue hi lo) :
    step fast cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 255#8, 0#8, ch, cv, u⟩ x =
      ⟨⟨P 4, 255#8, 0#8, 8#8, fn, fr, hiOf (wordValue hi lo - 1), loOf (wordValue hi lo - 1),
        mh, ml, 0#8, 255#8, x, cv, u⟩, 0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  acc_simp [hu, one_false hi lo hn, dec_fast hi lo (by omega)]

/-- A Close's second payload byte, more to come (a reason): the code is checked. -/
theorem acc_close2 (cap : Nat) (fn fr hi lo mh ml ch cv : Byte)
    (u : List Byte) (hu : u.length = 8) (x : Byte) (hn : 2 ≤ wordValue hi lo)
    (hcode : TlsWebSocketFrame.closeCode fast ch x = 255#8) :
    step fast cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 255#8, ch, cv, u⟩ x =
      ⟨⟨P 4, 255#8, 0#8, 8#8, fn, fr, hiOf (wordValue hi lo - 1), loOf (wordValue hi lo - 1),
        mh, ml, 0#8, 0#8, ch, 255#8, u⟩, 0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  acc_simp [hu, one_false hi lo hn, dec_fast hi lo (by omega), hcode]

/-- A Close's second payload byte, the last (no reason): the code is checked, the connection closes. -/
theorem acc_close2_last (cap : Nat) (fn fr hi lo mh ml ch cv : Byte) (x : Byte) (hn : wordValue hi lo = 1)
    (hcode : TlsWebSocketFrame.closeCode fast ch x = 255#8) :
    step fast cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 255#8, ch, cv, initial fast 7⟩ x =
      ⟨⟨P 0, 255#8, 255#8, 0#8, 0#8, fr, hiOf 0, loOf 0, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩,
        0#8, 255#8, 0#8, 255#8, 0#8, 255#8, 8#8⟩ := by
  acc_simp [one_true hi lo hn, dec_fast hi lo (by omega), hn, hcode]

/-- A byte of a Close's reason, not the last: the UTF-8 automaton moves from state `i` to `j`. -/
theorem acc_reason (cap : Nat) (fn fr hi lo mh ml ch : Byte) (i j : Nat) (hj8 : j < 8) (x : Byte)
    (hn : 2 ≤ wordValue hi lo) (hj : utfStep fast (U i) x = U j) :
    step fast cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 0#8, ch, 255#8, U i⟩ x =
      ⟨⟨P 4, 255#8, 0#8, 8#8, fn, fr, hiOf (wordValue hi lo - 1), loOf (wordValue hi lo - 1),
        mh, ml, 0#8, 0#8, ch, 255#8, U j⟩, 0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ := by
  acc_simp [one_false hi lo hn, dec_fast hi lo (by omega), hj, any_U j hj8]

/-- The last byte of a Close's reason: the automaton accepts, the connection closes. -/
theorem acc_reason_last (cap : Nat) (fn fr hi lo mh ml ch : Byte) (i : Nat) (x : Byte)
    (hn : wordValue hi lo = 1) (hj : utfStep fast (U i) x = U 0) :
    step fast cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 0#8, ch, 255#8, U i⟩ x =
      ⟨⟨P 0, 255#8, 255#8, 0#8, 0#8, fr, hiOf 0, loOf 0, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩,
        0#8, 255#8, 0#8, 255#8, 0#8, 255#8, 8#8⟩ := by
  acc_simp [one_true hi lo hn, dec_fast hi lo (by omega), hn, hj, any_U 0 (by decide)]

/-! ### UTF-8 (RFC 3629 section 4) -/

/-- `UTF8-tail = %x80-BF`. -/
def tail (b : Byte) : Prop := 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF

/-- RFC 3629 section 4, `UTF8-char`, one alternative per constructor (the ABNF's rows). -/
inductive Utf8Char : List Byte → Prop
  | one (a : Byte) : a.toNat ≤ 0x7F → Utf8Char [a]
  | two (a b : Byte) : 0xC2 ≤ a.toNat → a.toNat ≤ 0xDF → tail b → Utf8Char [a, b]
  | e0 (a b c : Byte) : a.toNat = 0xE0 → 0xA0 ≤ b.toNat → b.toNat ≤ 0xBF → tail c → Utf8Char [a, b, c]
  | e1 (a b c : Byte) : 0xE1 ≤ a.toNat → a.toNat ≤ 0xEC → tail b → tail c → Utf8Char [a, b, c]
  | ed (a b c : Byte) : a.toNat = 0xED → 0x80 ≤ b.toNat → b.toNat ≤ 0x9F → tail c → Utf8Char [a, b, c]
  | ee (a b c : Byte) : 0xEE ≤ a.toNat → a.toNat ≤ 0xEF → tail b → tail c → Utf8Char [a, b, c]
  | f0 (a b c d : Byte) : a.toNat = 0xF0 → 0x90 ≤ b.toNat → b.toNat ≤ 0xBF → tail c → tail d →
      Utf8Char [a, b, c, d]
  | f1 (a b c d : Byte) : 0xF1 ≤ a.toNat → a.toNat ≤ 0xF3 → tail b → tail c → tail d → Utf8Char [a, b, c, d]
  | f4 (a b c d : Byte) : a.toNat = 0xF4 → 0x80 ≤ b.toNat → b.toNat ≤ 0x8F → tail c → tail d →
      Utf8Char [a, b, c, d]

/-- RFC 3629 section 4, `UTF8-octets = *( UTF8-char )`. -/
inductive Utf8 : List Byte → Prop
  | nil : Utf8 []
  | cons (c w : List Byte) : Utf8Char c → Utf8 w → Utf8 (c ++ w)

/-- The grammar read left to right: which bytes may come next, after a prefix that is whole
characters (0), or inside a character (1–3: that many tail bytes still due; 4–7: after E0, ED, F0,
F4, whose second byte has a narrower range). `none`: no character can continue this way. -/
def delta (i : Nat) (x : Byte) : Option Nat :=
  match i with
  | 0 => if x.toNat ≤ 0x7F then some 0 else if 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF then some 1
      else if x.toNat = 0xE0 then some 4
      else if (0xE1 ≤ x.toNat ∧ x.toNat ≤ 0xEC) ∨ (0xEE ≤ x.toNat ∧ x.toNat ≤ 0xEF) then some 2
      else if x.toNat = 0xED then some 5
      else if x.toNat = 0xF0 then some 6 else if 0xF1 ≤ x.toNat ∧ x.toNat ≤ 0xF3 then some 3
      else if x.toNat = 0xF4 then some 7 else none
  | 1 => if 0x80 ≤ x.toNat ∧ x.toNat ≤ 0xBF then some 0 else none
  | 2 => if 0x80 ≤ x.toNat ∧ x.toNat ≤ 0xBF then some 1 else none
  | 3 => if 0x80 ≤ x.toNat ∧ x.toNat ≤ 0xBF then some 2 else none
  | 4 => if 0xA0 ≤ x.toNat ∧ x.toNat ≤ 0xBF then some 1 else none
  | 5 => if 0x80 ≤ x.toNat ∧ x.toNat ≤ 0x9F then some 1 else none
  | 6 => if 0x90 ≤ x.toNat ∧ x.toNat ≤ 0xBF then some 2 else none
  | 7 => if 0x80 ≤ x.toNat ∧ x.toNat ≤ 0x8F then some 2 else none
  | _ => none

def uOf : Option Nat → List Byte
  | some j => U j
  | none => List.replicate 8 0#8

theorem member_shift (x : Byte) (low count : Nat) (h : low + count ≤ 256) :
    member fast x ((List.range count).map (· + low)) =
      if low ≤ x.toNat ∧ x.toNat < low + count then 255#8 else 0#8 := by
  rw [member_mb]
  have hx := x.isLt
  have e : ((List.range count).map (· + low)).any (fun n => x == BitVec.ofNat 8 n) =
      decide (low ≤ x.toNat ∧ x.toNat < low + count) := by
    rw [Bool.eq_iff_iff]
    simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨m, hm, rfl⟩
      simp only [BitVec.toNat_ofNat]; omega
    · rintro ⟨h1, h2⟩
      exact ⟨x.toNat - low, by omega, by apply BitVec.eq_of_toNat_eq; simp; omega⟩
  rw [e]; by_cases c : low ≤ x.toNat ∧ x.toNat < low + count <;> simp [c]

theorem member_range0 (x : Byte) (count : Nat) (h : count ≤ 256) :
    member fast x ((List.range count).map (· + 0)) = if x.toNat < count then 255#8 else 0#8 := by
  rw [member_shift x 0 count (by omega)]; simp

theorem eq_nat (x : Byte) (n : Nat) (hn : n < 256) : eq fast x n = if x.toNat = n then 255#8 else 0#8 := by
  rw [eq_fast]
  by_cases h : x.toNat = n
  · rw [if_pos h, if_pos (by apply BitVec.eq_of_toNat_eq; simp; omega)]; rfl
  · rw [if_neg h, if_neg (by intro e; apply h; rw [e]; simp; omega)]; rfl

theorem delta_lt (i : Nat) (x : Byte) (j : Nat) (h : delta i x = some j) : j < 8 := by
  unfold delta at h
  split at h <;> (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

theorem utf_step (i : Nat) (x : Byte) (j : Nat) (h : delta i x = some j) : utfStep fast (U i) x = U j := by
  unfold delta at h
  split at h <;> (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    (simp only [utfStep, U, TlsWebSocketUpgrade.get, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.reduceBEq, mb_true, mb_false]
     simp (disch := omega) only [member_shift, eq_nat, if_pos, if_neg]
     try simp only [either, and_ones_l, and_ones_r, and_zero_l, and_zero_r, not_ones, not_zero])
  all_goals
    by_cases c1 : 225 ≤ x.toNat ∧ x.toNat < 225 + 12 <;>
    simp (disch := omega) only [if_pos, if_neg] <;>
    simp only [either, and_ones_l, and_ones_r, and_zero_l, and_zero_r, not_ones, not_zero]

/-- The automaton of `delta`, run over a list: the state at its end, `none` once stuck. -/
def drun : Nat → List Byte → Option Nat
  | i, [] => some i
  | i, x :: xs => match delta i x with
    | some j => drun j xs
    | none => none

theorem drun_some {i : Nat} {x : Byte} {xs : List Byte} {j : Nat} (h : delta i x = some j) :
    drun i (x :: xs) = drun j xs := by simp [drun, h]

theorem char_drun (c : List Byte) (hc : Utf8Char c) (w : List Byte) : drun 0 (c ++ w) = drun 0 w := by
  cases hc with
  | one a h =>
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | two a b h1 h2 hb =>
    obtain ⟨b1, b2⟩ := hb
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | e0 a b c h1 h2 h3 hc =>
    obtain ⟨c1, c2⟩ := hc
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 4) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | e1 a b c h1 h2 hb hc =>
    obtain ⟨b1, b2⟩ := hb; obtain ⟨c1, c2⟩ := hc
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 2) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | ed a b c h1 h2 h3 hc =>
    obtain ⟨c1, c2⟩ := hc
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 5) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | ee a b c h1 h2 hb hc =>
    obtain ⟨b1, b2⟩ := hb; obtain ⟨c1, c2⟩ := hc
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 2) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | f0 a b c d h1 h2 h3 hc hd =>
    obtain ⟨c1, c2⟩ := hc; obtain ⟨d1, d2⟩ := hd
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 6) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 2) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | f1 a b c d h1 h2 hb hc hd =>
    obtain ⟨b1, b2⟩ := hb; obtain ⟨c1, c2⟩ := hc; obtain ⟨d1, d2⟩ := hd
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 3) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 2) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]
  | f4 a b c d h1 h2 h3 hc hd =>
    obtain ⟨c1, c2⟩ := hc; obtain ⟨d1, d2⟩ := hd
    simp only [List.cons_append, List.nil_append]
    rw [drun_some (j := 7) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 2) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 1) (by simp (disch := omega) only [delta, if_pos, if_neg]),
      drun_some (j := 0) (by simp (disch := omega) only [delta, if_pos, if_neg])]

theorem utf8_drun {w : List Byte} (h : Utf8 w) : drun 0 w = some 0 := by
  induction h with
  | nil => rfl
  | cons c w hc _ ih => rw [char_drun c hc w, ih]

/-! ### Close status codes (RFC 6455 section 7.4) -/

/-- The status codes a Close may carry (RFC 6455 sections 7.4.1, 7.4.2 and the IANA "WebSocket Close
Code Number Registry"): 1000–1003 and 1007–1014 (defined; 1004–1006 and 1015 MUST NOT be sent),
3000–4999 (registered and private use). 0–999, 1016–2999 and 5000+ are not used. -/
def validCloseCode (c : Nat) : Prop := (1000 ≤ c ∧ c ≤ 1003) ∨ (1007 ≤ c ∧ c ≤ 1014) ∨ (3000 ≤ c ∧ c ≤ 4999)

instance : DecidablePred validCloseCode := fun c => by unfold validCloseCode; infer_instance

theorem member_list (x : Byte) (ns : List Nat) (h : ∀ n ∈ ns, n < 256) :
    member fast x ns = mb (decide (x.toNat ∈ ns)) := by
  rw [member_mb]
  congr 1
  have hx := x.isLt
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have := h n hn
    simpa [Nat.mod_eq_of_lt this] using hn
  · intro hm
    exact ⟨x.toNat, hm, by apply BitVec.eq_of_toNat_eq; simp⟩

theorem shift_mb (x : Byte) (low count : Nat) (h : low + count ≤ 256) :
    member fast x ((List.range count).map (· + low)) = mb (decide (low ≤ x.toNat ∧ x.toNat < low + count)) := by
  rw [member_shift x low count h]; by_cases c : low ≤ x.toNat ∧ x.toNat < low + count <;> simp [c]

theorem range_mb (x : Byte) (n : Nat) (h : n ≤ 256) : member fast x (List.range n) = mb (decide (x.toNat < n)) := by
  rw [member_range x n h]; by_cases c : x.toNat < n <;> simp [c]

theorem eq_dec (x : Byte) (n : Nat) (hn : n < 256) : eq fast x n = mb (decide (x.toNat = n)) := by
  rw [eq_nat x n hn]; by_cases c : x.toNat = n <;> simp [c]

/-- **`closeCode_value`.** The parser's status-code check is RFC 6455's list. -/
theorem closeCode_value (hi lo : Byte) :
    TlsWebSocketFrame.closeCode fast hi lo = mb (decide (validCloseCode (wordValue hi lo))) := by
  unfold TlsWebSocketFrame.closeCode
  rw [eq_dec hi 3 (by decide), eq_dec hi 11 (by decide), eq_dec hi 19 (by decide),
    member_list lo _ (by decide), shift_mb lo 184 72 (by decide), shift_mb hi 12 7 (by decide),
    range_mb lo 136 (by decide)]
  simp only [and_mb, either_mb]
  congr 1
  have a := hi.isLt; have b := lo.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
    validCloseCode, wordValue]
  constructor
  · intro h
    rcases h with ⟨h3, hl⟩ | ⟨h11, hl1, hl2⟩ | ⟨h12, h18⟩ | ⟨h19, hl⟩
    · simp only [or_false] at hl
      rcases hl with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
    · omega
    · omega
    · omega
  · intro h
    rcases h with h | h | h
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · right
      by_cases a11 : hi.toNat = 11
      · exact Or.inl ⟨a11, by omega, by omega⟩
      · right
        by_cases a19 : hi.toNat = 19
        · exact Or.inr ⟨a19, by omega⟩
        · exact Or.inl ⟨by omega, by omega⟩

/-! ### Payload runs -/

/-- Every event of the run keeps the validity byte at 255. -/
def AllValid (es : List (Event Byte)) : Prop := ∀ e ∈ es, e.state.valid = 255#8

/-- The control-queue inputs the controller takes from an event and its byte. -/
def cin (e : Event Byte) (b : Byte) : Byte × Byte × Byte × Byte := (e.controlData, e.controlDone, e.controlKind, b)

theorem allValid_cons {e : Event Byte} {es : List (Event Byte)} (h : e.state.valid = 255#8) (hs : AllValid es) :
    AllValid (e :: es) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hs x hx

theorem allValid_nil : AllValid [] := fun _ h => absurd h List.not_mem_nil

theorem data_run (cap : Nat) (k : Nat) (hk : k = 0 ∨ k = 2) (fin : Bool) :
    ∀ (p : List Byte) (fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte), u.length = 8 →
    wordValue hi lo = p.length → 1 ≤ p.length → p.length ≤ wordValue mh ml →
    AllValid (events cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ p) ∧
    finalState cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ p =
      ⟨P 0, 255#8, 0#8, 0#8, 0#8, mb (!fin), hiOf 0, loOf 0,
        if fin then BitVec.ofNat 8 (cap / 256) else hiOf (wordValue mh ml - p.length),
        if fin then BitVec.ofNat 8 cap else loOf (wordValue mh ml - p.length), 0#8, 0#8, 0#8, 0#8, initial fast 7⟩
  | [], _, _, _, _, _, _, _, _, _, _, _, _, h1, _ => absurd h1 (by simp)
  | [x], fr, hi, lo, mh, ml, pf, ps, ch, cv, u, hu, hn, _, hm => by
      simp only [List.length_singleton] at hn hm
      simp only [events, finalState, acc_data_last cap k hk fin fr hi lo mh ml pf ps ch cv u hu x hn hm]
      exact ⟨allValid_cons rfl allValid_nil, rfl⟩
  | x :: y :: rest, fr, hi, lo, mh, ml, pf, ps, ch, cv, u, hu, hn, _, hm => by
      have hn2 : 2 ≤ wordValue hi lo := by simp at hn; omega
      have hm1 : 1 ≤ wordValue mh ml := by simp at hm; omega
      have l1 := wordValue_lt hi lo
      have l2 := wordValue_lt mh ml
      have ih := data_run cap k hk fin (y :: rest) fr (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1))
        (hiOf (wordValue mh ml - 1)) (loOf (wordValue mh ml - 1)) 0#8 pf ch cv u hu
        (by rw [wordValue_of _ (by omega)]; simp at hn ⊢; omega) (by simp)
        (by rw [wordValue_of _ (by omega)]; simp at hm ⊢; omega)
      rw [wordValue_of _ (by omega)] at ih
      have e : wordValue mh ml - 1 - (y :: rest).length = wordValue mh ml - (x :: y :: rest).length := by
        simp; omega
      rw [e] at ih
      simp only [events, finalState, acc_data cap k hk (mb fin) fr hi lo mh ml pf ps ch cv u hu x hn2 hm1]
      exact ⟨allValid_cons rfl ih.1, ih.2⟩

/-- The control-queue inputs of a payload byte that does not end the frame (`collectIn`). -/
def col (x : Byte) : Byte × Byte × Byte × Byte := (255#8, 0#8, 0#8, x)

theorem ping_run (cap : Nat) (k : Nat) (hk : k = 9 ∨ k = 10) :
    ∀ (q : List Byte) (b fn fr hi lo mh ml pf ps ch cv : Byte) (u : List Byte), u.length = 8 →
    wordValue hi lo = q.length + 1 →
    AllValid (events cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ (q ++ [b])) ∧
    finalState cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩ (q ++ [b]) =
      ⟨P 0, 255#8, 0#8, 0#8, 0#8, fr, hiOf 0, loOf 0, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩ ∧
    List.zipWith cin (events cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u⟩
      (q ++ [b])) (q ++ [b]) = q.map col ++ [(255#8, 255#8, BitVec.ofNat 8 k, b)]
  | [], b, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u, hu, hn => by
      simp only [List.length_nil, Nat.zero_add] at hn
      simp only [List.nil_append, events, finalState, acc_ping_last cap k hk fn fr hi lo mh ml pf ps ch cv u hu b hn]
      exact ⟨allValid_cons rfl allValid_nil, by first | rfl | trivial, by first | rfl | trivial⟩
  | x :: q, b, fn, fr, hi, lo, mh, ml, pf, ps, ch, cv, u, hu, hn => by
      have hn2 : 2 ≤ wordValue hi lo := by simp at hn; omega
      have l1 := wordValue_lt hi lo
      have ih := ping_run cap k hk q b fn fr (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1)) mh ml 0#8 pf
        ch cv u hu (by rw [wordValue_of _ (by omega)]; simp at hn ⊢; omega)
      simp only [List.cons_append, events, finalState, acc_ping cap k hk fn fr hi lo mh ml pf ps ch cv u hu x hn2,
        List.zipWith_cons_cons, List.map_cons]
      exact ⟨allValid_cons rfl ih.1, ih.2.1, by rw [ih.2.2]; rfl⟩

theorem drun_cons {i : Nat} {x : Byte} {xs : List Byte} (h : drun i (x :: xs) = some 0) :
    ∃ j, delta i x = some j ∧ drun j xs = some 0 := by
  simp only [drun] at h
  split at h
  · next j hj => exact ⟨j, hj, h⟩
  · cases h

theorem reason_run (cap : Nat) :
    ∀ (r : List Byte) (b : Byte) (i : Nat) (fn fr hi lo mh ml ch : Byte), drun i (r ++ [b]) = some 0 →
    wordValue hi lo = r.length + 1 →
    AllValid (events cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 0#8, ch, 255#8, U i⟩ (r ++ [b])) ∧
    finalState cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 0#8, ch, 255#8, U i⟩ (r ++ [b]) =
      ⟨P 0, 255#8, 255#8, 0#8, 0#8, fr, hiOf 0, loOf 0, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩ ∧
    List.zipWith cin (events cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 0#8, 0#8, ch, 255#8, U i⟩
      (r ++ [b])) (r ++ [b]) = r.map col ++ [(255#8, 255#8, 8#8, b)]
  | [], b, i, fn, fr, hi, lo, mh, ml, ch, hd, hn => by
      simp only [List.length_nil, Nat.zero_add, List.nil_append] at hn hd ⊢
      obtain ⟨j, hj, hr⟩ := drun_cons hd
      simp only [drun, Option.some.injEq] at hr
      subst hr
      simp only [events, finalState, acc_reason_last cap fn fr hi lo mh ml ch i b hn (utf_step i b 0 hj)]
      exact ⟨allValid_cons rfl allValid_nil, by first | rfl | trivial, by first | rfl | trivial⟩
  | x :: r, b, i, fn, fr, hi, lo, mh, ml, ch, hd, hn => by
      have hn2 : 2 ≤ wordValue hi lo := by simp at hn; omega
      have l1 := wordValue_lt hi lo
      simp only [List.cons_append] at hd
      obtain ⟨j, hj, hr⟩ := drun_cons hd
      have ih := reason_run cap r b j fn fr (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1)) mh ml ch hr
        (by rw [wordValue_of _ (by omega)]; simp at hn ⊢; omega)
      simp only [List.cons_append, events, finalState,
        acc_reason cap fn fr hi lo mh ml ch i j (delta_lt i x j hj) x hn2 (utf_step i x j hj),
        List.zipWith_cons_cons, List.map_cons]
      exact ⟨allValid_cons rfl ih.1, ih.2.1, by rw [ih.2.2]; rfl⟩

theorem getLast_snoc {α : Type} : ∀ (l : List α) (b : α) (h : l ++ [b] ≠ []), (l ++ [b]).getLast h = b
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: l, b, _ => by
      simp only [List.cons_append]
      rw [List.getLast_cons_cons]
      exact getLast_snoc (y :: l) b (by simp)

/-- A Close payload: a status code RFC 6455 allows, then a UTF-8 reason (possibly empty). -/
theorem close_run (cap : Nat) (c1 c2 : Byte) (r : List Byte) (hcode : validCloseCode (wordValue c1 c2))
    (hr : Utf8 r) (fn fr hi lo mh ml : Byte) (hn : wordValue hi lo = r.length + 2) :
    AllValid (events cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 255#8, 0#8, 0#8, 0#8, initial fast 7⟩
      (c1 :: c2 :: r)) ∧
    finalState cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 255#8, 0#8, 0#8, 0#8, initial fast 7⟩
      (c1 :: c2 :: r) =
      ⟨P 0, 255#8, 255#8, 0#8, 0#8, fr, hiOf 0, loOf 0, mh, ml, 0#8, 0#8, 0#8, 0#8, initial fast 7⟩ ∧
    List.zipWith cin (events cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 255#8, 0#8, 0#8, 0#8,
      initial fast 7⟩ (c1 :: c2 :: r)) (c1 :: c2 :: r) =
      (c1 :: c2 :: r).dropLast.map col ++ [(255#8, 255#8, 8#8, (c1 :: c2 :: r).getLast (by simp))] := by
  have hc : TlsWebSocketFrame.closeCode fast c1 c2 = 255#8 := by rw [closeCode_value, decide_eq_true hcode]; rfl
  have l1 := wordValue_lt hi lo
  have h2 : 2 ≤ wordValue hi lo := by omega
  have w1 : wordValue (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1)) = r.length + 1 := by
    rw [wordValue_of _ (by omega)]; omega
  simp only [events, finalState, acc_close1 cap fn fr hi lo mh ml 0#8 0#8 (initial fast 7) rfl c1 h2]
  rcases List.eq_nil_or_concat r with rfl | ⟨r', b, rfl⟩
  · simp only [acc_close2_last cap fn fr _ _ mh ml c1 0#8 c2 (by simpa using w1) hc, events, finalState]
    exact ⟨allValid_cons rfl (allValid_cons rfl allValid_nil), by first | rfl | trivial,
      by first | rfl | trivial⟩
  · rw [List.concat_eq_append] at *
    have w2 : 2 ≤ wordValue (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1)) := by
      rw [w1]; simp
    have l2 := wordValue_lt (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1))
    have hd : drun 0 (r' ++ [b]) = some 0 := utf8_drun hr
    have ih := reason_run cap r' b 0 fn fr
      (hiOf (wordValue (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1)) - 1))
      (loOf (wordValue (hiOf (wordValue hi lo - 1)) (loOf (wordValue hi lo - 1)) - 1)) mh ml c1 hd
      (by rw [wordValue_of _ (by omega), w1]; simp)
    rw [initial_U] at ih ⊢
    simp only [acc_close2 cap fn fr _ _ mh ml c1 0#8 (U 0) rfl c2 w2 hc]
    refine ⟨allValid_cons rfl (allValid_cons rfl ih.1), ih.2.1, ?_⟩
    simp only [List.zipWith_cons_cons]
    rw [ih.2.2]
    have e1 : (c1 :: c2 :: (r' ++ [b])).dropLast = c1 :: c2 :: r' := by
      rw [← List.cons_append, ← List.cons_append, List.dropLast_concat]
    simp [e1, col, cin]
    exact (getLast_snoc (c2 :: r') b (by simp)).symm

theorem dropLast_getLast_snoc {α : Type} (L q : List α) (b : α) (he : L = q ++ [b]) (pf : L ≠ []) :
    L.dropLast = q ∧ L.getLast pf = b := by
  subst he; exact ⟨List.dropLast_concat, getLast_snoc q b pf⟩

/-- `close_run`'s control-queue inputs, the payload written as `q ++ [b]`. -/
theorem close_run_inputs (cap : Nat) (c1 c2 : Byte) (r : List Byte) (hcode : validCloseCode (wordValue c1 c2))
    (hr : Utf8 r) (fn fr hi lo mh ml : Byte) (hn : wordValue hi lo = r.length + 2) (q : List Byte) (b : Byte)
    (he : c1 :: c2 :: r = q ++ [b]) :
    List.zipWith cin (events cap ⟨P 4, 255#8, 0#8, 8#8, fn, fr, hi, lo, mh, ml, 255#8, 0#8, 0#8, 0#8,
      initial fast 7⟩ (c1 :: c2 :: r)) (c1 :: c2 :: r) = q.map col ++ [(255#8, 255#8, 8#8, b)] := by
  obtain ⟨-, -, h3⟩ := close_run cap c1 c2 r hcode hr fn fr hi lo mh ml hn
  obtain ⟨e1, e2⟩ := dropLast_getLast_snoc (c1 :: c2 :: r) q b he (by simp)
  rw [h3, e1, e2]

/-! ### Whole frames -/

/-- What the reference keeps between frames (RFC 6455 section 5.4): whether a fragmented binary
message is in progress, and how much of the message capacity is left. -/
structure Ctx where
  fragmented : Bool
  left : Nat

/-- The parser at a frame boundary, valid, as the context says (and closed or not). -/
def Boundary (S : State Byte) (c : Ctx) (closed : Bool) : Prop :=
  S.phases = P 0 ∧ S.valid = 255#8 ∧ S.closed = mb closed ∧ S.fragmented = mb c.fragmented ∧
    wordValue S.messageHigh S.messageLow = c.left ∧ S.utfPhases.length = 8

/-- A Close's payload (RFC 6455 section 5.5.1): empty, or a status code and a UTF-8 reason. -/
def CloseBody (p : List Byte) : Prop :=
  p = [] ∨ ∃ c1 c2 r, p = c1 :: c2 :: r ∧ validCloseCode (wordValue c1 c2) ∧ Utf8 r

/-- The context after a frame with opcode `k`, FIN `fin`, `n` payload bytes, `m` being the message
capacity left when its payload starts: a final data frame ends the message, a non-final one
continues it; control frames leave it as it is. -/
def afterK (cap k : Nat) (fin frag : Bool) (m n : Nat) : Ctx :=
  if k = 0 ∨ k = 2 then (if fin then ⟨false, cap⟩ else ⟨true, m - n⟩) else ⟨frag, m⟩

theorem cap_word (cap : Nat) (hcap : cap < 65536) :
    wordValue (BitVec.ofNat 8 (cap / 256)) (BitVec.ofNat 8 cap) = cap := by
  simp only [wordValue, BitVec.toNat_ofNat]; omega

theorem hiOf_zero : hiOf 0 = 0#8 := rfl
theorem loOf_zero : loOf 0 = 0#8 := rfl

/-- **`payload_accept`.** From the payload phase right after the header (count `p.length ≥ 1`), a
payload that the reference accepts (a data payload within the message capacity left, any Ping or
Pong payload, a Close payload with a valid code and UTF-8 reason) keeps the validity byte at 255
and ends at a frame boundary with the reference's context. -/
theorem payload_accept (cap : Nat) (hcap : cap < 65536) (k : Nat) (hk : Op k) (fin frag : Bool)
    (p : List Byte) (hi lo mh ml : Byte) (hn : wordValue hi lo = p.length) (h1 : 1 ≤ p.length)
    (hdata : k = 0 ∨ k = 2 → p.length ≤ wordValue mh ml) (hclose : k = 8 → CloseBody p) :
    AllValid (events cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, mb frag, hi, lo, mh, ml, 255#8, 0#8, 0#8,
      0#8, initial fast 7⟩ p) ∧
    Boundary (finalState cap ⟨P 4, 255#8, 0#8, BitVec.ofNat 8 k, mb fin, mb frag, hi, lo, mh, ml, 255#8, 0#8,
      0#8, 0#8, initial fast 7⟩ p) (afterK cap k fin frag (wordValue mh ml) p.length) (k == 8) := by
  have lm := wordValue_lt mh ml
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hv, hf⟩ := data_run cap 0 (Or.inl rfl) fin p (mb frag) hi lo mh ml 255#8 0#8 0#8 0#8 (initial fast 7)
      rfl hn h1 (hdata (Or.inl rfl))
    refine ⟨hv, ?_⟩
    rw [hf]
    cases fin
    · refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
      simp only [afterK, if_pos (Or.inl rfl : 0 = 0 ∨ 0 = 2)]
      exact wordValue_of _ (by omega)
    · exact ⟨rfl, rfl, rfl, rfl, cap_word cap hcap, rfl⟩
  · obtain ⟨hv, hf⟩ := data_run cap 2 (Or.inr rfl) fin p (mb frag) hi lo mh ml 255#8 0#8 0#8 0#8 (initial fast 7)
      rfl hn h1 (hdata (Or.inr rfl))
    refine ⟨hv, ?_⟩
    rw [hf]
    cases fin
    · refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
      simp only [afterK, if_pos (Or.inr rfl : 2 = 0 ∨ 2 = 2)]
      exact wordValue_of _ (by omega)
    · exact ⟨rfl, rfl, rfl, rfl, cap_word cap hcap, rfl⟩
  · rcases hclose rfl with hp | ⟨c1, c2, r, rfl, hcode, hr⟩
    · subst hp; simp at h1
    · obtain ⟨hv, hf, -⟩ := close_run cap c1 c2 r hcode hr (mb fin) (mb frag) hi lo mh ml (by simpa using hn)
      exact ⟨hv, by rw [hf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨q, b, rfl⟩ : ∃ q b, p = q ++ [b] := by
      rcases List.eq_nil_or_concat p with rfl | ⟨q, b, rfl⟩
      · simp at h1
      · exact ⟨q, b, List.concat_eq_append⟩
    obtain ⟨hv, hf, -⟩ := ping_run cap 9 (Or.inl rfl) q b (mb fin) (mb frag) hi lo mh ml 255#8 0#8 0#8 0#8
      (initial fast 7) rfl (by simpa using hn)
    exact ⟨hv, by rw [hf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨q, b, rfl⟩ : ∃ q b, p = q ++ [b] := by
      rcases List.eq_nil_or_concat p with rfl | ⟨q, b, rfl⟩
      · simp at h1
      · exact ⟨q, b, List.concat_eq_append⟩
    obtain ⟨hv, hf, -⟩ := ping_run cap 10 (Or.inr rfl) q b (mb fin) (mb frag) hi lo mh ml 255#8 0#8 0#8 0#8
      (initial fast 7) rfl (by simpa using hn)
    exact ⟨hv, by rw [hf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- RFC 6455's requirements on a server frame in this profile, given the context: `wellFormed`
(no reserved bit, a defined opcode, unmasked, minimal length encoding, control frames final and at
most 125 bytes), not text (opcode 1 is outside this binary profile), within the capacity, a
continuation only inside a fragmented message and within its capacity left, a new binary message
only outside one (section 5.4), and a Close's payload empty or a valid code and UTF-8 reason. -/
def Accepts (cap : Nat) (c : Ctx) (h : Header) (payload : List Byte) : Prop :=
  h.wellFormed ∧ h.opcode ≠ 1 ∧ h.length ≤ cap ∧
    (h.opcode = 0 → c.fragmented = true ∧ h.length ≤ c.left) ∧ (h.opcode = 2 → c.fragmented = false) ∧
    (h.opcode = 8 → CloseBody payload)

/-- The context after an accepted frame. -/
def Ctx.after (cap : Nat) (c : Ctx) (h : Header) : Ctx :=
  afterK cap h.opcode h.fin c.fragmented (if h.opcode = 2 then cap else c.left) h.length

theorem parse_cases (f : List Byte) (h : Header) (hp : parseHeader f = some h) (hm : h.masked = false)
    (hf : h.form ≠ 64) :
    ∃ b0 b1 rest, f = b0 :: b1 :: rest ∧ b1.toNat < 128 ∧ h.fin = decide (128 ≤ b0.toNat) ∧
      h.rsv = b0.toNat / 16 % 8 ∧ h.opcode = b0.toNat % 16 ∧
      ((b1.toNat ≤ 125 ∧ h.size = 2 ∧ h.length = b1.toNat ∧ h.form = 7) ∨
       (b1.toNat = 126 ∧ h.size = 4 ∧ h.form = 16 ∧
        ∃ hi lo payload, rest = hi :: lo :: payload ∧ h.length = wordValue hi lo)) := by
  match f, hp with
  | b0 :: b1 :: rest, hp =>
    simp only [parseHeader] at hp
    split at hp
    · next hl =>
      cases hp
      simp only [decide_eq_false_iff_not, Nat.not_le] at hm
      refine ⟨b0, b1, rest, rfl, hm, rfl, rfl, rfl, Or.inl ⟨by omega, ?_, by show b1.toNat % 128 = b1.toNat; omega, rfl⟩⟩
      simp only [decide_eq_true_eq]; split <;> omega
    · next hl =>
      split at hp
      · next he =>
        split at hp
        · next hr =>
          cases hp
          simp only [decide_eq_false_iff_not, Nat.not_le] at hm
          refine ⟨b0, b1, rest, rfl, hm, rfl, rfl, rfl, Or.inr ⟨by omega, ?_, rfl, ?_⟩⟩
          · simp only [decide_eq_true_eq]; split <;> omega
          · match rest, hr with
            | hi :: lo :: payload, _ =>
              exact ⟨hi, lo, payload, rfl, by simp [bigEndian, wordValue]⟩
        · cases hp
      · split at hp
        · cases hp; exact absurd rfl hf
        · cases hp
  | [], hp => simp [parseHeader] at hp
  | [_], hp => simp [parseHeader] at hp

theorem first_eq (b0 : Byte) (hr : b0.toNat / 16 % 8 = 0) :
    b0 = firstByte (decide (128 ≤ b0.toNat)) (b0.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := b0.isLt
  unfold firstByte
  by_cases h : 128 ≤ b0.toNat <;> simp [h] <;> omega

theorem byte_eq (x : Byte) (n : Nat) (hn : n < 256) (h : x.toNat = n) : x = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- **`frame_accept`.** From a frame boundary (valid, not closed, the context `c`), over a frame
that `parseHeader` reads (`f` exactly its header and payload) and that RFC 6455 accepts in context
(`Accepts`): every event keeps the validity byte at 255, and the parser ends at a frame boundary
with the reference's next context, closed exactly after a Close. -/
theorem frame_accept (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx) (hS : Boundary S c false)
    (f : List Byte) (h : Header) (hp : parseHeader f = some h) (hn : f.length = h.size + h.length)
    (hA : Accepts cap c h (f.drop h.size)) :
    AllValid (events cap S f) ∧ Boundary (finalState cap S f) (c.after cap h) (h.opcode == 8) := by
  obtain ⟨⟨hrsv, hops, hmask, h16, h64, hctl⟩, h1, hlc, hcont, hbin, hclose⟩ := hA
  have hf : h.form ≠ 64 := by intro e; have := (h64 e).1; omega
  obtain ⟨b0, b1, rest, rfl, hb1, hfin, hr, hop, hcase⟩ := parse_cases f h hp hmask hf
  obtain ⟨ph, v, cl, op, fn, fr, hi0, lo0, mh, ml, pf, ps, ch, cv, u⟩ := S
  obtain ⟨hph, hv, hcl, hfr, hm, hu⟩ := hS
  simp only at hph hv hcl hfr hm hu
  subst hph hv hcl hfr
  have hb0 := first_eq b0 (by omega)
  rw [← hfin, ← hop] at hb0
  have hk : Op h.opcode := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hops
    rcases hops with e | e | e | e | e | e
    · exact Or.inl e
    · exact absurd e h1
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
  have hfirst : FirstOk c.fragmented h.fin h.opcode := by
    rcases hk with e | e | e | e | e
    · exact Or.inl ⟨e, (hcont e).1⟩
    · exact Or.inr (Or.inl ⟨e, hbin e⟩)
    · exact Or.inr (Or.inr ⟨Or.inl e, (hctl (by omega)).1⟩)
    · exact Or.inr (Or.inr ⟨Or.inr (Or.inl e), (hctl (by omega)).1⟩)
    · exact Or.inr (Or.inr ⟨Or.inr (Or.inr e), (hctl (by omega)).1⟩)
  have lmsg := wordValue_lt mh ml
  -- the message capacity left when the payload starts
  have hmsg : wordValue (if h.opcode = 2 then BitVec.ofNat 8 (cap / 256) else mh)
      (if h.opcode = 2 then BitVec.ofNat 8 cap else ml) = if h.opcode = 2 then cap else c.left := by
    by_cases e : h.opcode = 2
    · simp only [if_pos e]; exact cap_word cap hcap
    · simp only [if_neg e]; exact hm
  simp only [events, finalState, mb_false, Ctx.after]
  rw [hb0, acc_first cap op fn c.fragmented hi0 lo0 mh ml pf ps ch cv u hu h.fin h.opcode hfirst]
  simp only [List.length_cons] at hn
  have hclose' : h.opcode = 8 → CloseBody (List.drop h.size (b0 :: b1 :: rest)) := hclose
  have hcont' : h.opcode = 0 → h.length ≤ c.left := fun e => (hcont e).2
  clear hfirst hcont hbin hclose hb0 hop hfin hr h1 hops
  generalize h.opcode = k at *
  generalize h.fin = fin at *
  rcases hcase with ⟨hl, hsz, hlen, h7⟩ | ⟨he, hsz, h16', hi, lo, payload, rfl, hlen⟩
  · -- 7-bit length
    rw [hsz] at hclose'
    simp only [List.drop_succ_cons, List.drop_zero] at hclose'
    by_cases hz : b1.toNat = 0
    · -- empty payload
      have hr0 : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr0
      rw [byte_eq b1 0 (by decide) hz]
      rcases hk with e | e | e | e | e
      · subst e
        rw [acc_empty_data cap hcap 0 (Or.inl rfl) fin (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu]
        refine ⟨allValid_cons rfl (allValid_cons rfl allValid_nil), ?_⟩
        simp only [events, finalState]
        cases fin
        · exact ⟨rfl, rfl, rfl, rfl, by simpa [afterK, hlen, hz] using hmsg, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl, by simpa [afterK] using cap_word cap hcap, rfl⟩
      · subst e
        rw [acc_empty_data cap hcap 2 (Or.inr rfl) fin (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu]
        refine ⟨allValid_cons rfl (allValid_cons rfl allValid_nil), ?_⟩
        simp only [events, finalState]
        cases fin
        · exact ⟨rfl, rfl, rfl, rfl, by simpa [afterK, hlen, hz] using hmsg, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl, by simpa [afterK] using cap_word cap hcap, rfl⟩
      all_goals
        subst e
        rw [acc_empty_control cap hcap _ (by decide) (mb fin) (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu]
        refine ⟨allValid_cons rfl (allValid_cons rfl allValid_nil), ?_⟩
        simp only [events, finalState]
        exact ⟨rfl, rfl, rfl, rfl, by simpa [afterK] using hm, rfl⟩
    · -- payload of 1 to 125 bytes
      have hrl : rest.length = b1.toNat := by omega
      have hne : 1 ≤ rest.length := by omega
      have h1' : k = 8 → b1.toNat ≠ 1 := by
        intro e1 e2
        rcases hclose' e1 with e | ⟨c1, c2, r, e, -, -⟩
        · rw [e] at hrl; simp at hrl; omega
        · rw [e] at hrl; simp at hrl; omega
      rw [acc_short cap hcap k hk (mb fin) (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu b1 hb1 hl hz
        (by omega) h1']
      have hw : wordValue 0#8 (fast.and b1 127#8) = rest.length := by rw [word_short]; omega
      obtain ⟨hv, hb⟩ := payload_accept cap hcap k hk fin c.fragmented rest 0#8 (fast.and b1 127#8) _ _ hw hne
        (by
          intro hd; rw [hmsg]
          rcases hd with e | e
          · subst e; simp only [show (0 = 2) = False from by decide, if_false]; have := hcont' rfl; omega
          · subst e; simp only [if_true]; omega)
        (fun e => hclose' e)
      refine ⟨allValid_cons rfl (allValid_cons rfl hv), ?_⟩
      rw [hmsg, hrl, ← hlen] at hb
      exact hb
  · -- 16-bit length: a data frame
    have hkd : k = 0 ∨ k = 2 := by
      rcases hk with e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr e
      all_goals (have := hctl (by omega); have := h16 h16'; omega)
    rw [byte_eq b1 126 (by decide) he, acc_extended cap k hkd (mb fin) (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu]
    simp only [events, finalState]
    rw [acc_high cap k hkd (mb fin) (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu hi]
    simp only [events, finalState]
    simp only [List.length_cons] at hn
    have h126 := h16 h16'
    rw [acc_low cap hcap k hkd (mb fin) (mb c.fragmented) hi lo0 _ _ pf ps ch cv u hu lo (by omega) (by omega)]
    have hw : wordValue hi lo = payload.length := by omega
    obtain ⟨hv, hb⟩ := payload_accept cap hcap k (by rcases hkd with e | e <;> simp [Op, e]) fin c.fragmented
      payload hi lo _ _ hw (by omega)
      (by
        intro hd; rw [hmsg]
        rcases hd with e | e
        · subst e; simp only [show (0 = 2) = False from by decide, if_false]; have := hcont' rfl; omega
        · subst e; simp only [if_true]; omega)
      (by intro e; rcases hkd with e' | e' <;> omega)
    refine ⟨allValid_cons rfl (allValid_cons rfl (allValid_cons rfl (allValid_cons rfl hv))), ?_⟩
    rw [hmsg, ← hw, ← hlen] at hb
    exact hb

theorem allValid_append {a b : List (Event Byte)} (ha : AllValid a) (hb : AllValid b) : AllValid (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact ha e h
  · exact hb e h

/-- **`frame_exact`.** With `frame_extent`: over an accepted frame, the deployed parser's `data`,
`controlData`, `frameDone` bytes are exactly the reference's (255 where the reference says so, 0
elsewhere), every event valid. -/
theorem matches_allValid : ∀ (es : List (Event Byte)) (ts : List (Bool × Bool × Bool)), Matches es ts →
    AllValid es → es.map (fun e => (e.data, e.controlData, e.frameDone)) = ts.map (fun t => (mb t.1, mb t.2.1, mb t.2.2))
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [Matches] at h
  | _ :: _, [], h, _ => by simp [Matches] at h
  | e :: es, (d, c, f) :: ts, ⟨⟨h1, h2, h3⟩, hm⟩, hv => by
      have v : e.state.valid = 255#8 := hv e (List.mem_cons_self ..)
      have ih := matches_allValid es ts hm (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, ih, h1, h2, h3, v, and_ones_l]

theorem frame_exact (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx) (hS : Boundary S c false)
    (f : List Byte) (h : Header) (hp : parseHeader f = some h) (hn : f.length = h.size + h.length)
    (hA : Accepts cap c h (f.drop h.size)) :
    (events cap S f).map (fun e => (e.data, e.controlData, e.frameDone)) =
      (expectedFlags h).map (fun t => (mb t.1, mb t.2.1, mb t.2.2)) ∧
    AllValid (events cap S f) ∧ Boundary (finalState cap S f) (c.after cap h) (h.opcode == 8) := by
  have hf : h.form ≠ 64 := by intro e; have := (hA.1.2.2.2.2.1 e).1; have := hA.2.2.1; omega
  obtain ⟨m, -, -⟩ := frame_extent cap S hS.1 f h hp hn hA.1.2.2.1 hf
  obtain ⟨v, b⟩ := frame_accept cap hcap S c hS f h hp hn hA
  exact ⟨matches_allValid _ _ m v, v, b⟩

/-- A sequence of frames, each accepted in the context the ones before it leave, none after a Close. -/
def FramesOk (cap : Nat) : Ctx → List (Header × List Byte) → Prop
  | _, [] => True
  | c, (h, f) :: fs => parseHeader f = some h ∧ f.length = h.size + h.length ∧ Accepts cap c h (f.drop h.size) ∧
      (fs ≠ [] → h.opcode ≠ 8) ∧ FramesOk cap (c.after cap h) fs

/-- **`frames_accept`.** Over a sequence of accepted frames, every event is valid. -/
theorem frames_accept (cap : Nat) (hcap : cap < 65536) : ∀ (fs : List (Header × List Byte)) (S : State Byte) (c : Ctx),
    Boundary S c false → FramesOk cap c fs →
    AllValid (events cap S (fs.flatMap Prod.snd)) ∧ ∃ c' cl, Boundary (finalState cap S (fs.flatMap Prod.snd)) c' cl
  | [], S, c, hS, _ => ⟨allValid_nil, c, false, hS⟩
  | (h, f) :: fs, S, c, hS, ⟨hp, hn, hA, hlast, hrest⟩ => by
      obtain ⟨v1, b1⟩ := frame_accept cap hcap S c hS f h hp hn hA
      simp only [List.flatMap_cons]
      rw [events_append, finalState_append]
      rcases fs with _ | ⟨g, gs⟩
      · simp only [List.flatMap_nil, events, finalState, List.append_nil]
        exact ⟨v1, _, _, b1⟩
      · have e8 : (h.opcode == 8) = false := by simpa using hlast (by simp)
        rw [e8] at b1
        obtain ⟨v2, b2⟩ := frames_accept cap hcap (g :: gs) _ _ b1 hrest
        exact ⟨allValid_append v1 v2, b2⟩

/-! ### Payload-level rejections (one step each) -/

theorem utf_dead (i : Nat) (hi : i < 8) (x : Byte) (h : delta i x = none) : any fast (utfStep fast (U i) x) = 0#8 := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [delta] at h <;> (repeat' split at h) <;> simp only [reduceCtorEq] at h <;>
    (simp only [utfStep, U, TlsWebSocketUpgrade.get, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.reduceBEq, mb_true, mb_false]
     simp (disch := omega) only [member_shift, eq_nat, if_pos, if_neg]
     simp only [either, and_ones_l, and_ones_r, and_zero_l, and_zero_r, not_ones, not_zero, any, List.foldl,
       fast_const]
     try rfl)

/-- A Close with a 1-byte payload (section 5.5.1: a body starts with a 2-byte code). -/
theorem reject_close_one (cap : Nat) (S : State Byte) (h : S.phases = P 1) (ho : S.opcode = 8#8) :
    (step fast cap S 1#8).state.valid = 0#8 := by
  acc_simp [h, ho]

/-- A data payload byte beyond the message's capacity. -/
theorem reject_message_full (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (ho : S.opcode = 0#8 ∨ S.opcode = 2#8) (hm : wordValue S.messageHigh S.messageLow = 0) :
    (step fast cap S x).state.valid = 0#8 := by
  have hz : (S.messageHigh == 0#8 && S.messageLow == 0#8) = true := by rw [zero_word]; simpa using hm
  rcases ho with o | o <;> acc_simp [h, o, hz]

/-- A byte of a Close's reason that no UTF-8 character can continue with. -/
theorem reject_reason (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4) (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 0#8) (i : Nat) (hi : i < 8) (hu : S.utfPhases = U i)
    (hd : delta i x = none) :
    (step fast cap S x).state.valid = 0#8 := by
  acc_simp [h, ho, h1, h2, hu, utf_dead i hi x hd]

/-- The last byte of a 2-byte Close payload, the code not one RFC 6455 allows. -/
theorem reject_close_code (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4) (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 255#8) (hcv : S.closeCodeValid = 0#8)
    (hn : wordValue S.high S.low = 1) (hc : ¬ validCloseCode (wordValue S.closeCodeHigh x)) :
    (step fast cap S x).state.valid = 0#8 := by
  have hcode : TlsWebSocketFrame.closeCode fast S.closeCodeHigh x = 0#8 := by
    rw [closeCode_value, decide_eq_false hc]; rfl
  acc_simp [h, ho, h1, h2, hcv, one_true S.high S.low hn, hcode]

/-- The last byte of a Close with a reason, the code invalid (`closeCodeValid` 0). -/
theorem reject_reason_code (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4) (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 0#8) (hn : wordValue S.high S.low = 1)
    (hc : S.closeCodeValid = 0#8) :
    (step fast cap S x).state.valid = 0#8 := by
  acc_simp [h, ho, h1, h2, one_true S.high S.low hn, hc]

/-- The last byte of a Close's reason, leaving a UTF-8 character unfinished. -/
theorem reject_reason_unfinished (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4) (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 0#8) (hn : wordValue S.high S.low = 1)
    (i j : Nat) (hu : S.utfPhases = U i) (hd : delta i x = some j) (hj : j ≠ 0) :
    (step fast cap S x).state.valid = 0#8 := by
  have hj' : (j == 0) = false := by simpa using hj
  acc_simp [h, ho, h1, h2, one_true S.high S.low hn, hu, utf_step i x j hd, hj', U_getElem]

end TlsMpc.KernelSpecs.ParseWebSocketAccept
