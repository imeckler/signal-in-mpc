import TlsMpc.Node.PassOver

/-!
# The controller's WebSocket frame parser against RFC 6455 section 5.2

New file; it changes no definition and no emitter imports it.

The controller (`TlsMpc/Node/Policy/Receive.lean`, `step`, `stepPassed`, `stepSkipped`) parses every
server frame in the clear with `TlsWebSocketFrame.runByte PublicReceive.fast capacity`, one byte at a
time, on its 26-byte state. That function reads the state, runs `TlsWebSocketFrame.step` on the byte
and writes the state back (`runByte_active` below). So what follows is about `step` on
`PublicReceive.fast` (equal to `ByteAuth.concrete`, `PublicReceive.fast_eq`), iterated over a list of
bytes (`events`, `finalState`), and then about `runByte` iterated the way the controller does it
(`controller_run`).

## The reference

`parseHeader` reads RFC 6455 section 5.2's base framing header from a list of bytes, written from the
RFC's figure and text, independently of the deployed parser: FIN (bit 7 of byte 0), RSV1–3 (bits
6–4), opcode (bits 3–0); MASK (bit 7 of byte 1), payload length (bits 6–0): 0–125 is the length;
126 means the next 2 bytes are a 16-bit big-endian length; 127 means the next 8 bytes are a 64-bit
big-endian length; then the 4-byte masking key if MASK is set. `Header.size` is the header's length
in bytes, `Header.length` the payload's.

## What is proved (standard axioms only; no `sorry`, `native_decide`, `bv_decide`)

**Which bytes are payload (`frame_extent`).** From any state at a frame boundary (phase vector
`P 0`: what `start` has, and what every frame leaves, `frame_extent`'s second conclusion), for every
byte list `f` that `parseHeader` reads as an UNMASKED header with a 7-bit or 16-bit length
(`form ≠ 64`, so any payload length below 2^16) and that is exactly that header and its payload
(`f.length = size + length`), iterating the deployed step over `f`:
* the per-byte `data` / `controlData` / `frameDone` events are, byte for byte, the validity bit of
  the state after that byte, AND-ed with the reference's answer: `data` on exactly the payload bytes
  of a data frame (opcode 0 or 2), `controlData` on exactly the payload bytes of a control frame
  (opcode 8, 9, 10), `frameDone` on exactly the frame's last byte (`expectedFlags`);
* after the frame the parser is at a frame boundary again with opcode 0.

So frames chain (`frames_extent`: any concatenation of such frames). Every frame shape the server
can send in this profile is covered except: masked frames, 64-bit lengths (both rejected, below).
Non-canonical 16-bit lengths, reserved bits, unknown opcodes and so on are covered by
`frame_extent` too (the extent is right) and are rejected by the validity bit (below).

**Malformed headers are rejected (`reject_*`).** The step's new validity byte is 0 when: the state
was already invalid (`reject_sticky`: once 0, it stays 0, and every event is gated by it); a first
header byte has a reserved bit set, an opcode other than 0, 2, 8, 9, 10 (text, 1, is outside this
binary profile), or is a control opcode without FIN (`reject_first`); the second header byte has
MASK set (RFC 6455 section 5.1: a client MUST fail on a masked server frame) or the 64-bit length
code 127 (`reject_second`); a control frame uses the 16-bit length code (`reject_control_extended`,
section 5.5: control payloads are at most 125); a 16-bit length is below 126 (`reject_noncanonical`,
section 5.2: "the minimal number of bytes MUST be used"); a length exceeds the capacity
(`reject_capacity7`, `reject_capacity16`).

**The controller's loop (`controller_run`).** Iterating `runByte` as the controller does (feed
`state ++ [255, byte]`, keep the first 8 output bytes as the event, the rest as the next state) from
the serialised state is the serialisation of iterating `step`, each event being `valid` then the seven
event flags gated by `valid`. The controller throws at the first byte whose output byte 0 is not 255.

**RFC 6455 section 5.7's examples (kernel evaluation).** `rfc_examples`: the reference reads the
RFC's example headers; `rfc_ping_run`: the deployed parser, as the controller runs it, on the
unmasked Ping "Hello"; `rfc_text_rejected`, `rfc_masked_rejected`: the text frame and the masked
Pong are rejected.

Not covered here: acceptance (that a well-formed frame keeps the validity byte at 255, which also
depends on the message, fragmentation and close-code state), the close frame's code and UTF-8 checks.
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open PublicReceive.PassOver (fast_and fast_const fast_maskBit eq_fast select_zero select_ones select_zero'
  select_ones' and_ones dec_fast hiOf loOf wordValue_of wordValue_lt member_range choose_ones)
open TlsWebSocketUpgrade (get eq either any member choose initial)
open TlsWebSocketFrame (State Event step wordValue)

namespace TlsMpc.KernelSpecs.ParseWebSocketFrame

abbrev Byte := BitVec 8

/-! ### The reference: RFC 6455 section 5.2 -/

structure Header where
  fin : Bool
  /-- RSV1, RSV2, RSV3 as a 3-bit number. -/
  rsv : Nat
  opcode : Nat
  masked : Bool
  /-- Payload length. -/
  length : Nat
  /-- Header length in bytes, masking key included. -/
  size : Nat
  /-- The payload length's encoding: 7, 16 or 64 bits. -/
  form : Nat
  deriving DecidableEq, Repr

/-- A network-byte-order number. -/
def bigEndian (l : List Byte) : Nat := l.foldl (fun n b => 256 * n + b.toNat) 0

def parseHeader : List Byte → Option Header
  | b0 :: b1 :: rest =>
    let fin := decide (128 ≤ b0.toNat)
    let rsv := b0.toNat / 16 % 8
    let opcode := b0.toNat % 16
    let masked := decide (128 ≤ b1.toNat)
    let len7 := b1.toNat % 128
    let key := if masked then 4 else 0
    if len7 ≤ 125 then some ⟨fin, rsv, opcode, masked, len7, 2 + key, 7⟩
    else if len7 = 126 then
      if 2 ≤ rest.length then some ⟨fin, rsv, opcode, masked, bigEndian (rest.take 2), 4 + key, 16⟩ else none
    else if 8 ≤ rest.length then some ⟨fin, rsv, opcode, masked, bigEndian (rest.take 8), 10 + key, 64⟩
    else none
  | _ => none

/-- RFC 6455's requirements on a frame a server sends (sections 5.1, 5.2, 5.5): no reserved bit
(no extension is negotiated), a defined opcode, not masked, the minimal length encoding (and the
64-bit length's top bit clear), control frames final and at most 125 bytes. -/
def Header.wellFormed (h : Header) : Prop :=
  h.rsv = 0 ∧ h.opcode ∈ [0, 1, 2, 8, 9, 10] ∧ h.masked = false ∧
  (h.form = 16 → 126 ≤ h.length) ∧ (h.form = 64 → 65536 ≤ h.length ∧ h.length < 2 ^ 63) ∧
  (8 ≤ h.opcode → h.fin = true ∧ h.length ≤ 125)

def Header.dataBit (h : Header) : Bool := h.opcode == 0 || h.opcode == 2
def Header.controlBit (h : Header) : Bool := h.opcode == 8 || (h.opcode == 9 || h.opcode == 10)

/-- The flags (data, controlData, frameDone) the reference assigns to the payload bytes of a frame
of `n` payload bytes: every payload byte is data (or control data), the last one ends the frame. -/
def payloadFlags (d c : Bool) : Nat → List (Bool × Bool × Bool)
  | 0 => []
  | 1 => [(d, c, true)]
  | n + 2 => (d, c, false) :: payloadFlags d c (n + 1)

/-- The flags of every byte of a frame with header `h`: header bytes carry no payload; the frame
ends at its last header byte if the payload is empty, else at its last payload byte. -/
def expectedFlags (h : Header) : List (Bool × Bool × Bool) :=
  List.replicate (h.size - 1) (false, false, false) ++ [(false, false, h.length == 0)] ++
    payloadFlags h.dataBit h.controlBit h.length

/-! ### Masks -/

def mb (b : Bool) : Byte := if b then 255 else 0

@[simp] theorem mb_true : mb true = 255#8 := rfl
@[simp] theorem mb_false : mb false = 0#8 := rfl
theorem and_mb (a b : Bool) : fast.and (mb a) (mb b) = mb (a && b) := by cases a <;> cases b <;> rfl
theorem not_mb (a : Bool) : fast.not (mb a) = mb (!a) := by cases a <;> rfl
theorem eq_mb (x : Byte) (n : Nat) : eq fast x n = mb (x == BitVec.ofNat 8 n) := by
  rw [eq_fast]; by_cases h : x = BitVec.ofNat 8 n <;> simp [h, mb]
theorem maskBit_mb (x : Byte) (i : Nat) : fast.maskBit x i = mb (x.getLsbD i) := by
  rw [fast_maskBit]; cases x.getLsbD i <;> rfl
theorem const_0 : fast.const 0 = mb false := by decide
theorem select_mb (c : Bool) (y n : Byte) : TlsInner.select fast (mb c) y n = if c then y else n := by
  cases c
  · exact select_zero y n
  · exact select_ones y n
theorem either_mb (a b : Bool) : either fast (mb a) (mb b) = mb (a || b) := by cases a <;> cases b <;> rfl
theorem fold_either (p : Nat → Bool) (acc : Bool) : ∀ ns : List Nat,
    (ns.map (fun n => mb (p n))).foldl (either fast) (mb acc) = mb (acc || ns.any p)
  | [] => by simp
  | n :: ns => by
      simp only [List.map_cons, List.foldl_cons, either_mb, List.any_cons]
      rw [fold_either p (acc || p n) ns, Bool.or_assoc]
theorem member_mb (x : Byte) (ns : List Nat) :
    member fast x ns = mb (ns.any (fun n => x == BitVec.ofNat 8 n)) := by
  unfold member any
  have : ns.map (eq fast x) = ns.map (fun n => mb (x == BitVec.ofNat 8 n)) := by
    apply List.map_congr_left; intro n _; exact eq_mb x n
  rw [this, const_0, fold_either]; simp
theorem and_ones_l (y : Byte) : fast.and 255#8 y = y := by
  rw [fast_and]; exact (BitVec.and_comm _ _).trans (and_ones y)
theorem and_ones_r (y : Byte) : fast.and y 255#8 = y := by rw [fast_and]; exact and_ones y
theorem and_zero_l (y : Byte) : fast.and 0#8 y = 0#8 := by rw [fast_and]; simp
theorem and_zero_r (y : Byte) : fast.and y 0#8 = 0#8 := by rw [fast_and]; simp
theorem not_ones : fast.not 255#8 = 0#8 := by decide
theorem not_zero : fast.not 0#8 = 255#8 := by decide
theorem beq_mb_zero (c : Bool) : (mb c == 0#8) = !c := by cases c <;> decide
theorem beq_mb_ones (c : Bool) : (mb c == 255#8) = c := by cases c <;> decide

/-! ### One step, by phase

The state's `phases` is one-hot: which header or payload byte comes next (first header byte,
second header byte, extended length high, extended length low, payload). `P i` is phase `i`. -/

def P (i : Nat) : List Byte := [mb (i == 0), mb (i == 1), mb (i == 2), mb (i == 3), mb (i == 4)]

/-- The part of the state that decides where frames begin and end. -/
structure Core where
  phases : List Byte
  high : Byte
  low : Byte
  opcode : Byte

def core (S : State Byte) : Core := ⟨S.phases, S.high, S.low, S.opcode⟩

/-- An event's `data`, `controlData`, `frameDone` are the new validity byte AND-ed with `d`, `c`,
`f`. -/
def Flags (e : Event Byte) (d c f : Bool) : Prop :=
  e.data = fast.and e.state.valid (mb d) ∧ e.controlData = fast.and e.state.valid (mb c) ∧
  e.frameDone = fast.and e.state.valid (mb f)

theorem len_eq : ∀ x : Byte, (fast.and x 127#8 == 126#8) = (x.toNat % 128 == 126) := by decide +kernel
theorem len_eq7 : ∀ x : Byte, (fast.and x 127#8 == 127#8) = (x.toNat % 128 == 127) := by decide +kernel
theorem len_eq0 : ∀ x : Byte, (fast.and x 127#8 == 0#8) = (x.toNat % 128 == 0) := by decide +kernel
theorem bit7 : ∀ x : Byte, x[7] = decide (128 ≤ x.toNat) := by decide +kernel

theorem zero_word (hi lo : Byte) : (hi == 0#8 && lo == 0#8) = (wordValue hi lo == 0) := by
  have a := hi.isLt; have b := lo.isLt
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, wordValue]
  constructor
  · rintro ⟨rfl, rfl⟩; rfl
  · intro h; constructor <;> apply BitVec.eq_of_toNat_eq <;> simp <;> omega

theorem one_word (hi lo : Byte) : (hi == 0#8 && lo == 1#8) = (wordValue hi lo == 1) := by
  have a := hi.isLt; have b := lo.isLt
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, wordValue]
  constructor
  · rintro ⟨rfl, rfl⟩; rfl
  · intro h; constructor <;> apply BitVec.eq_of_toNat_eq <;> simp <;> omega

syntax "frame_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| frame_simp [$ts,*]) => `(tactic|
      (refine ⟨?_, ?_, ?_, ?_⟩ <;>
       simp [core, Flags, TlsWebSocketFrame.step, P, TlsWebSocketUpgrade.get, and_mb, not_mb, either, eq_mb,
        maskBit_mb, member_mb, select_mb, fast_const, TlsWebSocketFrame.zero, TlsWebSocketFrame.one,
        TlsWebSocketFrame.dataKind, TlsWebSocketFrame.control,
        and_ones_l, and_ones_r, and_zero_l, and_zero_r, not_ones, not_zero, select_ones', select_zero',
        beq_mb_zero, beq_mb_ones, $ts,*]))

/-- First header byte: the opcode is kept, the second header byte comes next. -/
theorem step_first (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 0) :
    core (step fast cap S x).state = ⟨P 1, S.high, S.low, fast.and x 15#8⟩ ∧
    Flags (step fast cap S x) false false false := by
  frame_simp [h]

/-- Second header byte, unmasked, 7-bit length 1–125: the payload comes next, its count is the
length. -/
theorem step_second_short (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 1) (hm : x.toNat < 128)
    (hl : x.toNat % 128 ≤ 125) (hz : x.toNat % 128 ≠ 0) :
    core (step fast cap S x).state = ⟨P 4, 0#8, fast.and x 127#8, S.opcode⟩ ∧
    Flags (step fast cap S x) false false false := by
  have h126 : (x.toNat % 128 == 126) = false := by simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by simp; omega
  have h0 : (x.toNat % 128 == 0) = false := by simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  frame_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7]

/-- Second header byte, unmasked, length 0: the frame ends here. -/
theorem step_second_empty (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 1) (hm : x.toNat < 128)
    (hz : x.toNat % 128 = 0) :
    core (step fast cap S x).state = ⟨P 0, 0#8, fast.and x 127#8, 0#8⟩ ∧
    Flags (step fast cap S x) false false true := by
  have h126 : (x.toNat % 128 == 126) = false := by simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by simp; omega
  have h0 : (x.toNat % 128 == 0) = true := by simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  frame_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7]

/-- Second header byte, unmasked, length code 126: the 16-bit length's high byte comes next. -/
theorem step_second_extended (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 1) (hm : x.toNat < 128)
    (he : x.toNat % 128 = 126) :
    core (step fast cap S x).state = ⟨P 2, S.high, S.low, S.opcode⟩ ∧
    Flags (step fast cap S x) false false false := by
  have h126 : (x.toNat % 128 == 126) = true := by simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by simp; omega
  have h0 : (x.toNat % 128 == 0) = false := by simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  frame_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7]

/-- The 16-bit length's high byte. -/
theorem step_high (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 2) :
    core (step fast cap S x).state = ⟨P 3, x, S.low, S.opcode⟩ ∧
    Flags (step fast cap S x) false false false := by
  frame_simp [h]

/-- The 16-bit length's low byte, length not 0: the payload comes next. -/
theorem step_low (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 3) (hw : wordValue S.high x ≠ 0) :
    core (step fast cap S x).state = ⟨P 4, S.high, x, S.opcode⟩ ∧
    Flags (step fast cap S x) false false false := by
  have hz : (S.high == 0#8 && x == 0#8) = false := by rw [zero_word]; simpa using hw
  frame_simp [h, hz]

/-- The 16-bit length's low byte, length 0: the frame ends here. -/
theorem step_low_empty (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 3) (hw : wordValue S.high x = 0) :
    core (step fast cap S x).state = ⟨P 0, S.high, x, 0#8⟩ ∧
    Flags (step fast cap S x) false false true := by
  have hz : (S.high == 0#8 && x == 0#8) = true := by rw [zero_word]; simpa using hw
  frame_simp [h, hz]

def dat (op : Byte) : Bool := op == 0#8 || op == 2#8
def ctl (op : Byte) : Bool := op == 8#8 || (op == 9#8 || op == 10#8)

/-- A payload byte that is not the last: the count goes down by one. -/
theorem step_payload (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4) (hw : 2 ≤ wordValue S.high S.low) :
    core (step fast cap S x).state =
      ⟨P 4, hiOf (wordValue S.high S.low - 1), loOf (wordValue S.high S.low - 1), S.opcode⟩ ∧
    Flags (step fast cap S x) (dat S.opcode) (ctl S.opcode) false := by
  have hz : (S.high == 0#8 && S.low == 1#8) = false := by rw [one_word]; simp; omega
  frame_simp [h, hz, dec_fast _ _ (show 1 ≤ wordValue S.high S.low by omega), dat, ctl]

/-- The last payload byte: the frame ends. -/
theorem step_payload_last (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (hw : wordValue S.high S.low = 1) :
    core (step fast cap S x).state = ⟨P 0, hiOf 0, loOf 0, 0#8⟩ ∧
    Flags (step fast cap S x) (dat S.opcode) (ctl S.opcode) true := by
  have hz : (S.high == 0#8 && S.low == 1#8) = true := by rw [one_word]; simp; omega
  frame_simp [h, hz, dec_fast _ _ (show 1 ≤ wordValue S.high S.low by omega), hw, dat, ctl]

/-! ### Iterating the step -/

def events (cap : Nat) : State Byte → List Byte → List (Event Byte)
  | _, [] => []
  | S, x :: xs => step fast cap S x :: events cap (step fast cap S x).state xs

def finalState (cap : Nat) : State Byte → List Byte → State Byte
  | S, [] => S
  | S, x :: xs => finalState cap (step fast cap S x).state xs

/-- Event by event, the flags are the reference's, gated by the event's validity byte. -/
def Matches : List (Event Byte) → List (Bool × Bool × Bool) → Prop
  | [], [] => True
  | e :: es, (d, c, f) :: ts => Flags e d c f ∧ Matches es ts
  | _, _ => False

theorem events_append (cap : Nat) : ∀ (S : State Byte) (a b : List Byte),
    events cap S (a ++ b) = events cap S a ++ events cap (finalState cap S a) b
  | _, [], _ => rfl
  | S, x :: xs, b => by
      simp only [List.cons_append, events, finalState]
      rw [events_append cap _ xs b]

theorem finalState_append (cap : Nat) : ∀ (S : State Byte) (a b : List Byte),
    finalState cap S (a ++ b) = finalState cap (finalState cap S a) b
  | _, [], _ => rfl
  | S, x :: xs, b => by
      simp only [List.cons_append, finalState]
      rw [finalState_append cap _ xs b]

theorem matches_append : ∀ (es fs : List (Event Byte)) (ts us : List (Bool × Bool × Bool)),
    Matches es ts → Matches fs us → Matches (es ++ fs) (ts ++ us)
  | [], fs, [], us, _, h => by simpa using h
  | [], _, _ :: _, _, h, _ => by simp [Matches] at h
  | _ :: _, _, [], _, h, _ => by simp [Matches] at h
  | e :: es, fs, (d, c, f) :: ts, us, ⟨h1, h2⟩, h => ⟨h1, matches_append es fs ts us h2 h⟩

theorem core_eq {S : State Byte} {ph : List Byte} {hi lo op : Byte} (h : core S = ⟨ph, hi, lo, op⟩) :
    S.phases = ph ∧ S.high = hi ∧ S.low = lo ∧ S.opcode = op := by
  simp only [core, Core.mk.injEq] at h; exact h

theorem matches_nil : Matches [] [] := trivial
theorem matches_cons {e : Event Byte} {es : List (Event Byte)} {d c f : Bool} {ts : List (Bool × Bool × Bool)}
    (h1 : Flags e d c f) (h2 : Matches es ts) : Matches (e :: es) ((d, c, f) :: ts) := ⟨h1, h2⟩

/-- A whole payload of `n ≥ 1` bytes, from the payload phase with count `n`. -/
theorem payload_run (cap : Nat) : ∀ (p : List Byte) (S : State Byte), S.phases = P 4 →
    wordValue S.high S.low = p.length → 1 ≤ p.length →
    Matches (events cap S p) (payloadFlags (dat S.opcode) (ctl S.opcode) p.length) ∧
    (finalState cap S p).phases = P 0 ∧ (finalState cap S p).opcode = 0#8
  | [], _, _, _, h1 => absurd h1 (by simp)
  | [x], S, hS, hw, _ => by
      obtain ⟨hc, hf⟩ := step_payload_last cap S x hS (by simpa using hw)
      obtain ⟨hp, -, -, ho⟩ := core_eq hc
      exact ⟨matches_cons hf matches_nil, hp, ho⟩
  | x :: y :: rest, S, hS, hw, _ => by
      have hw2 : 2 ≤ wordValue S.high S.low := by simp at hw; omega
      obtain ⟨hc, hf⟩ := step_payload cap S x hS hw2
      obtain ⟨hp, hh, hl, ho⟩ := core_eq hc
      have hlt := wordValue_lt S.high S.low
      have hw' : wordValue (step fast cap S x).state.high (step fast cap S x).state.low = (y :: rest).length := by
        rw [hh, hl, wordValue_of _ (by omega)]; simp at hw ⊢; omega
      obtain ⟨m, fp, fo⟩ := payload_run cap (y :: rest) (step fast cap S x).state hp hw' (by simp)
      rw [ho] at m
      refine ⟨?_, fp, fo⟩
      have hlen : (x :: y :: rest).length = rest.length + 2 := by simp
      rw [hlen, payloadFlags]
      exact matches_cons hf (by simpa using m)

/-! ### The reference's unmasked headers -/

theorem opcode_dat : ∀ x : Byte, dat (fast.and x 15#8) = (x.toNat % 16 == 0 || x.toNat % 16 == 2) := by
  decide +kernel
theorem opcode_ctl : ∀ x : Byte,
    ctl (fast.and x 15#8) = (x.toNat % 16 == 8 || (x.toNat % 16 == 9 || x.toNat % 16 == 10)) := by
  decide +kernel
theorem word_short : ∀ x : Byte, wordValue 0#8 (fast.and x 127#8) = x.toNat % 128 := by decide +kernel

/-- An unmasked header with a 7- or 16-bit length, as `parseHeader` reads it. -/
theorem parseHeader_unmasked (f : List Byte) (h : Header) (hp : parseHeader f = some h)
    (hm : h.masked = false) (hf : h.form ≠ 64) :
    ∃ b0 b1 rest, f = b0 :: b1 :: rest ∧ b1.toNat < 128 ∧ h.opcode = b0.toNat % 16 ∧
      ((b1.toNat % 128 ≤ 125 ∧ h.size = 2 ∧ h.length = b1.toNat % 128) ∨
       (b1.toNat % 128 = 126 ∧ h.size = 4 ∧
        ∃ hi lo payload, rest = hi :: lo :: payload ∧ h.length = wordValue hi lo)) := by
  match f, hp with
  | b0 :: b1 :: rest, hp =>
    simp only [parseHeader] at hp
    split at hp
    · next hl =>
      cases hp
      simp only [decide_eq_false_iff_not, Nat.not_le] at hm
      refine ⟨b0, b1, rest, rfl, hm, rfl, Or.inl ⟨hl, ?_, rfl⟩⟩
      simp only [decide_eq_true_eq]; split <;> omega
    · next hl =>
      split at hp
      · next he =>
        split at hp
        · next hr =>
          cases hp
          simp only [decide_eq_false_iff_not, Nat.not_le] at hm
          refine ⟨b0, b1, rest, rfl, hm, rfl, Or.inr ⟨he, ?_, ?_⟩⟩
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

/-! ### Which bytes are payload -/

/-- **`frame_extent`.** From a frame boundary, over a frame that RFC 6455 section 5.2 reads as an
unmasked header (7- or 16-bit length) followed by exactly its payload, the deployed parser's
`data`, `controlData` and `frameDone` events are the reference's (`expectedFlags`: payload bytes of a
data frame, payload bytes of a control frame, the last byte), gated byte by byte by the validity
byte; and the parser ends at a frame boundary with opcode 0. -/
theorem frame_extent (cap : Nat) (S : State Byte) (hS : S.phases = P 0) (f : List Byte) (h : Header)
    (hp : parseHeader f = some h) (hn : f.length = h.size + h.length) (hm : h.masked = false)
    (hf : h.form ≠ 64) :
    Matches (events cap S f) (expectedFlags h) ∧
    (finalState cap S f).phases = P 0 ∧ (finalState cap S f).opcode = 0#8 := by
  obtain ⟨b0, b1, rest, rfl, hb1, hop, hcase⟩ := parseHeader_unmasked f h hp hm hf
  have hd : h.dataBit = dat (fast.and b0 15#8) := by rw [opcode_dat, Header.dataBit, hop]
  have hc : h.controlBit = ctl (fast.and b0 15#8) := by rw [opcode_ctl, Header.controlBit, hop]
  obtain ⟨c0, f0⟩ := step_first cap S b0 hS
  obtain ⟨p1, -, -, o1⟩ := core_eq c0
  rcases hcase with ⟨hl, hsz, hlen⟩ | ⟨he, hsz, hi, lo, payload, rfl, hlen⟩
  · -- 7-bit length
    simp only [List.length_cons] at hn
    by_cases hz : b1.toNat % 128 = 0
    · obtain ⟨c1, f1⟩ := step_second_empty cap _ b1 p1 hb1 hz
      obtain ⟨p2, -, -, o2⟩ := core_eq c1
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      refine ⟨?_, p2, o2⟩
      simp only [expectedFlags, hsz, hlen, hz, events]
      exact matches_cons f0 (matches_cons f1 matches_nil)
    · have hr : b1.toNat % 128 = rest.length := by omega
      obtain ⟨c1, f1⟩ := step_second_short cap _ b1 p1 hb1 hl hz
      obtain ⟨p2, h2, l2, o2⟩ := core_eq c1
      have hw : wordValue (step fast cap (step fast cap S b0).state b1).state.high
          (step fast cap (step fast cap S b0).state b1).state.low = rest.length := by
        rw [h2, l2, word_short]; omega
      obtain ⟨m, fp, fo⟩ := payload_run cap rest _ p2 hw (by omega)
      rw [o2, o1] at m
      refine ⟨?_, fp, fo⟩
      have hz' : (rest.length == 0) = false := by
        rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; omega
      rw [show b0 :: b1 :: rest = [b0, b1] ++ rest from rfl, events_append]
      simp only [expectedFlags, hsz, hlen, hd, hc, hr, hz']
      exact matches_append _ _ [(false, false, false), (false, false, false)] _
        (matches_cons f0 (matches_cons f1 matches_nil)) m
  · -- 16-bit length
    simp only [List.length_cons] at hn
    obtain ⟨c1, f1⟩ := step_second_extended cap _ b1 p1 hb1 he
    obtain ⟨p2, -, -, o2⟩ := core_eq c1
    obtain ⟨c2, f2⟩ := step_high cap _ hi p2
    obtain ⟨p3, h3, -, o3⟩ := core_eq c2
    by_cases hz : wordValue hi lo = 0
    · obtain ⟨c3, f3⟩ := step_low_empty cap _ lo p3 (by rw [h3]; exact hz)
      obtain ⟨p4, -, -, o4⟩ := core_eq c3
      have hr : payload = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      refine ⟨?_, p4, o4⟩
      simp only [expectedFlags, hsz, hlen, hz, events]
      exact matches_cons f0 (matches_cons f1 (matches_cons f2 (matches_cons f3 matches_nil)))
    · have hr : wordValue hi lo = payload.length := by omega
      obtain ⟨c3, f3⟩ := step_low cap _ lo p3 (by rw [h3]; exact hz)
      obtain ⟨p4, h4, l4, o4⟩ := core_eq c3
      have hw : wordValue
          (step fast cap (step fast cap (step fast cap (step fast cap S b0).state b1).state hi).state lo).state.high
          (step fast cap (step fast cap (step fast cap (step fast cap S b0).state b1).state hi).state lo).state.low =
          payload.length := by
        rw [h4, l4, h3]; omega
      obtain ⟨m, fp, fo⟩ := payload_run cap payload _ p4 hw (by omega)
      rw [o4, o3, o2, o1] at m
      refine ⟨?_, ?_, ?_⟩
      · have hz' : (payload.length == 0) = false := by
          rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; omega
        rw [show b0 :: b1 :: hi :: lo :: payload = [b0, b1, hi, lo] ++ payload from rfl, events_append]
        simp only [expectedFlags, hsz, hlen, hd, hc, hr, hz']
        exact matches_append _ _ [(false, false, false), (false, false, false), (false, false, false),
          (false, false, false)] _
          (matches_cons f0 (matches_cons f1 (matches_cons f2 (matches_cons f3 matches_nil)))) m
      · rw [show b0 :: b1 :: hi :: lo :: payload = [b0, b1, hi, lo] ++ payload from rfl, finalState_append]
        exact fp
      · rw [show b0 :: b1 :: hi :: lo :: payload = [b0, b1, hi, lo] ++ payload from rfl, finalState_append]
        exact fo

/-- Frames one after the other: a list of (header, frame bytes) pairs, each as in `frame_extent`. -/
def Framed (fs : List (Header × List Byte)) : Prop :=
  ∀ p ∈ fs, parseHeader p.2 = some p.1 ∧ p.2.length = p.1.size + p.1.length ∧ p.1.masked = false ∧
    p.1.form ≠ 64

/-- **`frames_extent`.** Over any sequence of such frames, from a frame boundary, the events are the
reference's frame by frame, and the parser ends at a frame boundary. -/
theorem frames_extent (cap : Nat) : ∀ (fs : List (Header × List Byte)) (S : State Byte), S.phases = P 0 →
    Framed fs →
    Matches (events cap S (fs.flatMap Prod.snd)) (fs.flatMap (fun p => expectedFlags p.1)) ∧
    (finalState cap S (fs.flatMap Prod.snd)).phases = P 0
  | [], S, hS, _ => ⟨matches_nil, hS⟩
  | (h, f) :: fs, S, hS, hF => by
      obtain ⟨hp, hn, hm, hf⟩ := hF (h, f) (by simp)
      obtain ⟨m1, p1, -⟩ := frame_extent cap S hS f h hp hn hm hf
      obtain ⟨m2, p2⟩ := frames_extent cap fs (finalState cap S f) p1 (fun q hq => hF q (by simp [hq]))
      simp only [List.flatMap_cons]
      rw [events_append, finalState_append]
      exact ⟨matches_append _ _ _ _ m1 m2, p2⟩

/-! ### Malformed headers are rejected

Each lemma: the step's new validity byte is 0. Every event of that step is gated by it, and so is
every later one (`reject_sticky`). -/

syntax "valid_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| valid_simp [$ts,*]) => `(tactic|
       simp [TlsWebSocketFrame.step, P, TlsWebSocketUpgrade.get, and_mb, not_mb, either, eq_mb,
        maskBit_mb, member_mb, select_mb, fast_const, TlsWebSocketFrame.zero, TlsWebSocketFrame.one,
        TlsWebSocketFrame.dataKind, TlsWebSocketFrame.control,
        and_ones_l, and_ones_r, and_zero_l, and_zero_r, not_ones, not_zero, select_ones', select_zero',
        beq_mb_zero, beq_mb_ones, $ts,*])

/-- Once invalid, always invalid. -/
theorem reject_sticky (cap : Nat) (S : State Byte) (x : Byte) (h : S.valid = 0#8) :
    (step fast cap S x).state.valid = 0#8 := by
  simp only [TlsWebSocketFrame.step, h, and_zero_l]

/-- After a close frame (`closed` set), any byte is rejected. -/
theorem reject_closed (cap : Nat) (S : State Byte) (x : Byte) (h : S.closed = 255#8) :
    (step fast cap S x).state.valid = 0#8 := by
  simp only [TlsWebSocketFrame.step, h, not_ones, and_zero_r, and_zero_l]

theorem rsv_eq : ∀ x : Byte, (fast.and x 112#8 == 0#8) = (x.toNat / 16 % 8 == 0) := by decide +kernel
theorem op_eq0 : ∀ x : Byte, (fast.and x 15#8 == 0#8) = (x.toNat % 16 == 0) := by decide +kernel
theorem op_eq2 : ∀ x : Byte, (fast.and x 15#8 == 2#8) = (x.toNat % 16 == 2) := by decide +kernel
theorem op_eq8 : ∀ x : Byte, (fast.and x 15#8 == 8#8) = (x.toNat % 16 == 8) := by decide +kernel
theorem op_eq9 : ∀ x : Byte, (fast.and x 15#8 == 9#8) = (x.toNat % 16 == 9) := by decide +kernel
theorem op_eq10 : ∀ x : Byte, (fast.and x 15#8 == 10#8) = (x.toNat % 16 == 10) := by decide +kernel

/-- First header byte with a reserved bit set (RFC 6455 section 5.2: no extension is negotiated). -/
theorem reject_rsv (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 0) (hr : x.toNat / 16 % 8 ≠ 0) :
    (step fast cap S x).state.valid = 0#8 := by
  have hr' : (x.toNat / 16 % 8 == 0) = false := by
    rw [Bool.eq_false_iff]; simp only [ne_eq, beq_iff_eq]; exact hr
  valid_simp [h, rsv_eq x, hr']

/-- First header byte with an opcode other than 0, 2, 8, 9, 10 (reserved opcodes, section 5.2; and
text, 1, outside this binary profile). -/
theorem reject_opcode (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 0)
    (ho : x.toNat % 16 ≠ 0 ∧ x.toNat % 16 ≠ 2 ∧ x.toNat % 16 ≠ 8 ∧ x.toNat % 16 ≠ 9 ∧ x.toNat % 16 ≠ 10) :
    (step fast cap S x).state.valid = 0#8 := by
  obtain ⟨a, b, c, d, e⟩ := ho
  have a' : (x.toNat % 16 == 0) = false := by rw [Bool.eq_false_iff]; simpa using a
  have b' : (x.toNat % 16 == 2) = false := by rw [Bool.eq_false_iff]; simpa using b
  have c' : (x.toNat % 16 == 8) = false := by rw [Bool.eq_false_iff]; simpa using c
  have d' : (x.toNat % 16 == 9) = false := by rw [Bool.eq_false_iff]; simpa using d
  have e' : (x.toNat % 16 == 10) = false := by rw [Bool.eq_false_iff]; simpa using e
  valid_simp [h, op_eq0 x, op_eq2 x, op_eq8 x, op_eq9 x, op_eq10 x, a', b', c', d', e']

/-- A control frame (opcode 8, 9, 10) without FIN (section 5.5: control frames are not fragmented). -/
theorem reject_control_fragment (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 0)
    (ho : x.toNat % 16 = 8 ∨ x.toNat % 16 = 9 ∨ x.toNat % 16 = 10) (hf : x.toNat < 128) :
    (step fast cap S x).state.valid = 0#8 := by
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  have a' : (x.toNat % 16 == 0) = false := by rw [Bool.eq_false_iff]; simp; omega
  have b' : (x.toNat % 16 == 2) = false := by rw [Bool.eq_false_iff]; simp; omega
  rcases ho with o | o | o <;> valid_simp [h, op_eq0 x, op_eq2 x, op_eq8 x, op_eq9 x, op_eq10 x, a', b', o,
    bit7 x, h7]

/-- A continuation frame (opcode 0) with no fragmented message in progress (section 5.4). -/
theorem reject_continuation (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 0)
    (hfr : S.fragmented = 0#8) (ho : x.toNat % 16 = 0) :
    (step fast cap S x).state.valid = 0#8 := by
  have a' : (x.toNat % 16 == 0) = true := by simp; omega
  valid_simp [h, hfr, op_eq0 x, a']

/-- A new binary message (opcode 2) while a fragmented message is in progress (section 5.4). -/
theorem reject_interleaved (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 0)
    (hfr : S.fragmented = 255#8) (ho : x.toNat % 16 = 2) :
    (step fast cap S x).state.valid = 0#8 := by
  have a' : (x.toNat % 16 == 2) = true := by simp; omega
  have b' : (x.toNat % 16 == 0) = false := by rw [Bool.eq_false_iff]; simp; omega
  valid_simp [h, hfr, op_eq0 x, op_eq2 x, a', b']

/-- Second header byte with MASK set (section 5.1: a client MUST close the connection on a masked
server frame) or with the 64-bit length code 127 (beyond this profile's capacity). -/
theorem reject_second (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 1)
    (hx : 128 ≤ x.toNat ∨ x.toNat % 128 = 127) :
    (step fast cap S x).state.valid = 0#8 := by
  rcases hx with m | l
  · have h7 : decide (128 ≤ x.toNat) = true := by simpa using m
    valid_simp [h, bit7 x, h7]
  · have l' : (x.toNat % 128 == 127) = true := by simpa using l
    valid_simp [h, len_eq7 x, l']

/-- A control frame (the opcode just read is 8, 9 or 10) with the 16-bit length code (section 5.5:
control payloads are at most 125 bytes). -/
theorem reject_control_extended (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 1)
    (ho : S.opcode = 8#8 ∨ S.opcode = 9#8 ∨ S.opcode = 10#8) (he : x.toNat % 128 = 126) :
    (step fast cap S x).state.valid = 0#8 := by
  have e' : (x.toNat % 128 == 126) = true := by simpa using he
  rcases ho with o | o | o <;> valid_simp [h, o, len_eq x, e']

/-- A 16-bit length below 126 (section 5.2: the minimal number of bytes MUST be used). -/
theorem reject_noncanonical (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 3)
    (hh : S.high = 0#8) (hx : x.toNat < 126) :
    (step fast cap S x).state.valid = 0#8 := by
  have m : member fast x (List.range 126) = 255#8 := by
    rw [member_range x 126 (by decide), if_pos hx]; rfl
  valid_simp [h, hh, m]

theorem ite_mb (c : Prop) [Decidable c] : (if c then (255 : Byte) else 0) = mb (decide c) := by
  by_cases h : c <;> simp [h]

/-- `fits`: the length is at most the capacity (for a capacity below 2^16). -/
theorem fits_mb (cap : Nat) (hc : cap < 65536) (hi lo : Byte) :
    TlsWebSocketFrame.fits fast cap hi lo = mb (decide (wordValue hi lo ≤ cap)) := by
  unfold TlsWebSocketFrame.fits
  rw [member_range hi (cap / 256) (by omega), member_range lo (cap % 256 + 1) (by omega), ite_mb, ite_mb,
    eq_mb, and_mb, either_mb]
  congr 1
  have a := hi.isLt; have b := lo.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, wordValue]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · omega
    · have : hi.toNat = cap / 256 := by rw [h1, BitVec.toNat_ofNat]; omega
      omega
  · intro h1
    by_cases h2 : hi.toNat < cap / 256
    · exact Or.inl h2
    · refine Or.inr ⟨?_, by omega⟩
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega

/-- A 7-bit length above the capacity. -/
theorem reject_capacity7 (cap : Nat) (hc : cap < 65536) (S : State Byte) (x : Byte) (h : S.phases = P 1)
    (hm : x.toNat < 128) (hl : x.toNat % 128 ≤ 125) (hx : cap < x.toNat % 128) :
    (step fast cap S x).state.valid = 0#8 := by
  have h126 : (x.toNat % 128 == 126) = false := by rw [Bool.eq_false_iff]; simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by rw [Bool.eq_false_iff]; simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  have hd : decide (x.toNat % 128 ≤ cap) = false := by simp; omega
  have hf : TlsWebSocketFrame.fits fast cap 0#8 (fast.and x 127#8) = 0#8 := by
    rw [fits_mb cap hc, word_short, hd]; rfl
  valid_simp [h, len_eq x, len_eq7 x, bit7 x, h126, h127, h7, hf]

/-- A 16-bit length above the capacity. -/
theorem reject_capacity16 (cap : Nat) (hc : cap < 65536) (S : State Byte) (x : Byte) (h : S.phases = P 3)
    (hx : cap < wordValue S.high x) :
    (step fast cap S x).state.valid = 0#8 := by
  have hd : decide (wordValue S.high x ≤ cap) = false := by simp; omega
  have hf : TlsWebSocketFrame.fits fast cap S.high x = 0#8 := by
    rw [fits_mb cap hc, hd]; rfl
  valid_simp [h, hf]

/-! ### `runByte`, as the controller calls it -/

theorem len5 {α : Type} : ∀ (l : List α), l.length = 5 → ∃ a b c d e, l = [a, b, c, d, e]
  | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by
      simp at h

/-- The state's two lists have their lengths (what `start` gives and every step keeps). -/
def Shaped (S : State Byte) : Prop := S.phases.length = 5 ∧ S.utfPhases.length = 8

theorem stateBytes_length (S : State Byte) (h : Shaped S) : (TlsWebSocketFrame.stateBytes S).length = 26 := by
  obtain ⟨h5, h8⟩ := h
  simp [TlsWebSocketFrame.stateBytes, h5, h8]

theorem readState_stateBytes (S : State Byte) (h : Shaped S) :
    TlsWebSocketFrame.readState fast (TlsWebSocketFrame.stateBytes S) = S := by
  obtain ⟨h5, h8⟩ := h
  obtain ⟨ph, valid, closed, opcode, fin, fragmented, high, low, mh, ml, pf, ps, cch, ccv, utf⟩ := S
  obtain ⟨a, b, c, d, e, rfl⟩ := len5 ph h5
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, rfl⟩ := PublicReceive.PassOver.len8 utf h8
  simp [TlsWebSocketFrame.readState, TlsWebSocketFrame.stateBytes, TlsWebSocketUpgrade.get]

theorem step_shaped (cap : Nat) (S : State Byte) (x : Byte) (h : Shaped S) : Shaped (step fast cap S x).state := by
  obtain ⟨_, h8⟩ := h
  refine ⟨rfl, ?_⟩
  simp [TlsWebSocketFrame.step, choose, initial, List.length_zipWith, h8, PublicReceive.PassOver.utfStep_length]

theorem stateSelect_ones (yes no : State Byte) (hy : Shaped yes) (hn : Shaped no) :
    TlsWebSocketFrame.stateSelect fast 255#8 yes no = yes := by
  obtain ⟨y5, y8⟩ := hy
  obtain ⟨n5, n8⟩ := hn
  simp only [TlsWebSocketFrame.stateSelect, select_ones', choose_ones yes.phases no.phases (by omega),
    choose_ones yes.utfPhases no.utfPhases (by omega)]

/-- An event as the controller receives it: the validity byte, then the seven event bytes gated by
it (`ByteAuth.release`). -/
def eventBytes (e : Event Byte) : List Byte :=
  e.state.valid :: [e.data, e.controlData, e.messageStart, e.frameDone, e.messageDone, e.controlDone,
    e.controlKind].map (fast.and e.state.valid)

/-- **`runByte_active`.** On an active byte (`255`), `runByte` is `step` on the serialised state:
the event's bytes, then the new state serialised. -/
theorem runByte_active (cap : Nat) (S : State Byte) (h : Shaped S) (x : Byte) :
    TlsWebSocketFrame.runByte fast cap (TlsWebSocketFrame.stateBytes S ++ [255#8, x]) =
      eventBytes (step fast cap S x) ++ TlsWebSocketFrame.stateBytes (step fast cap S x).state := by
  have hl := stateBytes_length S h
  unfold TlsWebSocketFrame.runByte
  have t : (TlsWebSocketFrame.stateBytes S ++ [255#8, x]).take TlsWebSocketFrame.stateSize =
      TlsWebSocketFrame.stateBytes S := by
    rw [TlsWebSocketFrame.stateSize, ← hl, List.take_left]
  have g1 : get fast (TlsWebSocketFrame.stateBytes S ++ [255#8, x]) TlsWebSocketFrame.stateSize = 255#8 := by
    simp [TlsWebSocketUpgrade.get, TlsWebSocketFrame.stateSize, hl]
  have g2 : get fast (TlsWebSocketFrame.stateBytes S ++ [255#8, x]) (TlsWebSocketFrame.stateSize + 1) = x := by
    simp [TlsWebSocketUpgrade.get, TlsWebSocketFrame.stateSize, hl]
  have e255 : eq fast 255#8 255 = 255#8 := by rw [eq_mb]; rfl
  have e0 : eq fast 255#8 0 = 0#8 := by rw [eq_mb]; rfl
  simp only [t, g1, g2, readState_stateBytes S h, e255, e0,
    stateSelect_ones _ _ (step_shaped cap S x h) h, either, not_ones, not_zero, and_zero_r,
    and_ones_r, ByteAuth.release, eventBytes, List.cons_append]
  try rfl

/-- The controller's loop over a run of active bytes: feed `state ++ [255, byte]`, keep the first 8
output bytes as the byte's event, the rest as the next state. -/
def controllerRun (cap : Nat) (raw : List Byte) : List Byte → List (List Byte) × List Byte
  | [] => ([], raw)
  | x :: xs =>
    let out := TlsWebSocketFrame.runByte fast cap (raw ++ [255#8, x])
    let rest := controllerRun cap (out.drop 8) xs
    (out.take 8 :: rest.1, rest.2)

theorem eventBytes_length (e : Event Byte) : (eventBytes e).length = 8 := rfl

/-- **`controller_run`.** The controller's loop from a serialised state is the serialisation of
`events` and `finalState`. -/
theorem controller_run (cap : Nat) : ∀ (f : List Byte) (S : State Byte), Shaped S →
    controllerRun cap (TlsWebSocketFrame.stateBytes S) f =
      ((events cap S f).map eventBytes, TlsWebSocketFrame.stateBytes (finalState cap S f))
  | [], _, _ => rfl
  | x :: xs, S, h => by
      simp only [controllerRun, runByte_active cap S h x, events, finalState, List.map_cons]
      rw [List.drop_append_of_le_length (by rw [eventBytes_length]; exact Nat.le_refl 8),
        List.take_append_of_le_length (by rw [eventBytes_length]; exact Nat.le_refl 8)]
      rw [show (eventBytes (step fast cap S x)).drop 8 = [] from rfl,
        show (eventBytes (step fast cap S x)).take 8 = eventBytes (step fast cap S x) from rfl,
        List.nil_append, controller_run cap xs _ (step_shaped cap S x h)]

/-- The controller's starting state is shaped and at a frame boundary. -/
theorem start_boundary (cap : Nat) :
    Shaped (TlsWebSocketFrame.start fast cap) ∧ (TlsWebSocketFrame.start fast cap).phases = P 0 := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  simp [TlsWebSocketFrame.start, initial, P, fast_const]

/-! ### RFC 6455 section 5.7's examples -/

/-- The reference reads the RFC's example headers. -/
theorem rfc_examples :
    parseHeader [0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] = some ⟨true, 0, 1, false, 5, 2, 7⟩ ∧
    parseHeader [0x01, 0x03, 0x48, 0x65, 0x6c] = some ⟨false, 0, 1, false, 3, 2, 7⟩ ∧
    parseHeader [0x80, 0x02, 0x6c, 0x6f] = some ⟨true, 0, 0, false, 2, 2, 7⟩ ∧
    parseHeader [0x89, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] = some ⟨true, 0, 9, false, 5, 2, 7⟩ ∧
    parseHeader [0x8a, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] =
      some ⟨true, 0, 10, true, 5, 6, 7⟩ ∧
    parseHeader ([0x82, 0x7e, 0x01, 0x00] ++ List.replicate 256 0) = some ⟨true, 0, 2, false, 256, 4, 16⟩ ∧
    parseHeader [0x82, 0x7f, 0, 0, 0, 0, 0, 1, 0, 0] = some ⟨true, 0, 2, false, 65536, 10, 64⟩ := by
  decide +kernel

/-- The deployed parser, as the controller runs it (capacity 16384, from its start state), on the
RFC's unmasked Ping "Hello": valid throughout, control data on the five payload bytes, the frame
and the control frame end at the last byte, whose control kind is 9 (Ping). -/
theorem rfc_ping_run :
    (controllerRun 16384 (TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start fast 16384))
      [0x89, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]).1 =
    [[255, 0, 0, 0, 0, 0, 0, 0], [255, 0, 0, 0, 0, 0, 0, 0], [255, 0, 255, 0, 0, 0, 0, 0],
     [255, 0, 255, 0, 0, 0, 0, 0], [255, 0, 255, 0, 0, 0, 0, 0], [255, 0, 255, 0, 0, 0, 0, 0],
     [255, 0, 255, 0, 255, 0, 255, 9]] := by
  decide +kernel

/-- The RFC's single-frame text message is rejected at its first byte (text is outside this
binary profile), and nothing is reported. -/
theorem rfc_text_rejected :
    (controllerRun 16384 (TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start fast 16384))
      [0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]).1 = List.replicate 7 (List.replicate 8 0) := by
  decide +kernel

/-- The RFC's masked Pong (a client's frame) is rejected at its second byte when a server sends it. -/
theorem rfc_masked_rejected :
    ((controllerRun 16384 (TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start fast 16384))
      [0x8a, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]).1.map (·.head!)) =
      [255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

end TlsMpc.KernelSpecs.ParseWebSocketFrame
