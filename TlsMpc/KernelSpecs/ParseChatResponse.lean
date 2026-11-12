import TlsMpc.Node.PassOver

/-!
# The controller's service-response parser: which bytes are the body

New file; it changes no definition and no emitter imports it.

The controller (`TlsMpc/Node/Policy/Receive.lean`, `step` / `stepPassed`) runs
`TlsChatResponse.runByte` (on `VarintDecode.Spqr.concrete`, `Word64.fast`, `PublicReceive.fast`,
capacity 16384) over every byte of the WebSocket message that answers a pending request, fed the
frame parser's flags `[data, messageStart, messageDone]` and the byte (a zero in place of a body byte
it passes over unrevealed). The parser's state is 932 bytes (`TlsChatResponse.stateBytes`); its
output bytes are `valid, finished, successful, bodyData, bodyReset, headerData`. Here: what it does
on the bytes of a service response, against Signal's schema.

## The reference

Schema: `/Users/izzy/repos/Signal-Server/websocket-resources/src/main/proto/WebSocketProtocol.proto`
(proto2): `WebSocketMessage { optional Type type = 1; optional WebSocketRequestMessage request = 2;
optional WebSocketResponseMessage response = 3; }`, `WebSocketResponseMessage { optional uint64 id
= 1; optional uint32 status = 2; optional string message = 3; repeated string headers = 5; optional
bytes body = 4; }`, `WebSocketRequestMessage { optional string verb = 1; optional string path = 2;
optional bytes body = 3; repeated string headers = 5; optional uint64 id = 4; }`. The server builds a
response in `ProtobufWebSocketMessageFactory.createResponse` (same repository,
`websocket-resources/src/main/java/org/whispersystems/websocket/messages/protobuf/`): `type =
RESPONSE (2)`, `id`, `status`, `message` always set, `body` if present, then the headers;
protobuf-java writes fields in field-number order with minimal varints.

* `varint`: protobuf's varint encoding (minimal). `bodyField body`: field 4 as written: key `22`,
  `varint body.length`, the body.
* `readVarint`, `readFields`, `wsMessage`: an independent decoder of the wire format and of
  `WebSocketMessage` / `WebSocketResponseMessage` / `WebSocketRequestMessage`, returning each field's
  value or, for a length-delimited field, its extent (offset and length) in the message. The body's
  extent is what decides which bytes are passed over unrevealed.

## What is proved (standard axioms only; no `sorry`, `native_decide`, `bv_decide`)

* `process_active`: on a payload byte that neither starts nor ends the message (flags `255 0 0`),
  `process` is `step`; `runByte_process`: `runByte` on the serialised state is `process`;
  `respRun_active`: the controller's loop over such bytes is `step` iterated (`sEvents`, `sFinal`).
* One step per kind of byte at the header-to-body transition, as an equation for the whole event:
  `key_body` (key `22` at a field boundary of the inner response), `varint_more` (a varint byte
  with bit 7 set, any group `j < 9`), `length_end_body` (the length's last byte: the body starts,
  `bodyReset`), `body_byte` (any value: only counted, reported as body), `body_last`,
  `body_last_close` (the body's last byte; the latter also the inner response's last).
* `body_len_run`: the body's length read from `varint n` in any number of bytes (up to 9 groups),
  `payload_toNat` / `or_payload_toNat`: the decoder's arithmetic. `body_run`, `body_run_close`: any
  body.
* **`body_field`** / **`body_field_close`**: from any field boundary of the inner response (`KeyIn`)
  with enough of the inner response and of the budget left, over `bodyField body` (any non-empty
  body, any length up to the capacity): every event valid; `bodyData` is 255 on exactly the
  body's bytes and 0 on the key and the length; `bodyReset` exactly on the length's last byte;
  afterwards at a field boundary again (or, for `_close`, outside the inner response), with the
  counts lowered by the field's size and the body's length recorded. **`body_field_runByte`**: the
  same through the deployed `runByte` as the controller iterates it (output bytes 0, 1, 3, 4).
* Fail closed: `reject_body_length` (a declared body length beyond what is left of the inner
  response drops the validity byte at the length's last byte, before any byte is reported as body),
  `reject_end_in_field` (a message that ends inside a field, e.g. a truncated body, is not
  completed: `finish` drops the validity byte).
* Vectors through `runByte` (`ParseChatResponseVectors`): whole messages, byte by byte.

## Covered shapes and what is not proved

The general theorems cover the body field wherever it sits in the inner response (field order is
irrelevant to them: they start from any field boundary), with a body of any length whose varint has
at most 9 groups (the capacity bounds it to 3). Not proved in general (pinned by the vectors only):
the outer fields (`type`, the `response` length), `id` / `status` / `message` and the headers before
completion, `finish`'s checks (`id` = the expected one, status 100–999), and that every malformed
message fails closed (proved here for the body's length and for a message ending inside a field).
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open PublicReceive.PassOver (fast_and fast_not fast_const fast_maskBit eq_fast select_zero' select_ones'
  choose_zero choose_ones zipWith_zero fastSelect_zero fastSelect_ones w_select w_sub w_const weq_fast
  writeStack_zero and_ones xor_ones_ones utfStep_length readState_stateBytes stateBytes_length)

set_option linter.unusedSimpArgs false

namespace TlsMpc.KernelSpecs.ParseChatResponse

abbrev Byte := BitVec 8
abbrev Word := BitVec 64

/-! ### The reference decoder -/

/-- A protobuf varint at `pos`: its value and the position after it (at most 10 bytes). -/
def readVarint (buf : List Byte) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, pos =>
    match buf[pos]? with
    | none => none
    | some b =>
      if b.toNat < 128 then some (b.toNat, pos + 1)
      else match readVarint buf fuel (pos + 1) with
        | none => none
        | some (v, p) => some (b.toNat % 128 + 128 * v, p)

/-- A field's value as the wire format gives it: a varint, or the extent (offset, length) of a
length-delimited field's content. -/
inductive Wire where
  | varint (v : Nat)
  | bytes (start len : Nat)
  deriving DecidableEq, Repr

/-- The fields between `pos` and `stop` (exactly), as (field number, value); wire types other than
varint and length-delimited (which the service does not send) are rejected. -/
def readFields (buf : List Byte) (stop : Nat) : Nat → Nat → Option (List (Nat × Wire))
  | 0, _ => none
  | fuel + 1, pos =>
    if pos = stop then some [] else
    match readVarint buf 10 pos with
    | none => none
    | some (key, p) =>
      if key / 8 = 0 then none else
      if key % 8 = 0 then
        match readVarint buf 10 p with
        | none => none
        | some (v, q) => if q ≤ stop then (readFields buf stop fuel q).map ((key / 8, .varint v) :: ·) else none
      else if key % 8 = 2 then
        match readVarint buf 10 p with
        | none => none
        | some (n, q) => if q + n ≤ stop then
            (readFields buf stop fuel (q + n)).map ((key / 8, .bytes q n) :: ·) else none
      else none

/-- The last value of field `n` (protobuf: the last occurrence of a non-repeated field wins). -/
def lastField (fs : List (Nat × Wire)) (n : Nat) : Option Wire :=
  (fs.filter (·.1 = n)).getLast?.map (·.2)

/-- What the reference reads from a `WebSocketMessage`. -/
structure Decoded where
  type : Option Nat
  request : Bool
  id : Option Nat
  status : Option Nat
  message : Option (Nat × Nat)
  body : Option (Nat × Nat)
  headers : List (Nat × Nat)
  deriving DecidableEq, Repr

def asVarint : Option Wire → Option Nat
  | some (.varint v) => some v
  | _ => none

def asBytes : Option Wire → Option (Nat × Nat)
  | some (.bytes s n) => some (s, n)
  | _ => none

/-- `WebSocketMessage` (and, inside it, `WebSocketResponseMessage`) per WebSocketProtocol.proto:
`type` field 1, `request` field 2, `response` field 3; in the response `id` 1 (uint64), `status` 2
(uint32: low 32 bits), `message` 3, `body` 4, `headers` 5 (repeated). -/
def wsMessage (buf : List Byte) : Option Decoded := do
  let fs ← readFields buf buf.length (buf.length + 1) 0
  let inner ← match asBytes (lastField fs 3) with
    | some (s, n) => readFields buf (s + n) (n + 1) s
    | none => some []
  pure { type := asVarint (lastField fs 1), request := (lastField fs 2).isSome,
         id := asVarint (lastField inner 1), status := (asVarint (lastField inner 2)).map (· % 2 ^ 32),
         message := asBytes (lastField inner 3), body := asBytes (lastField inner 4),
         headers := (inner.filter (·.1 = 5)).filterMap (fun f => asBytes (some f.2)) }
abbrev RState := TlsChatResponse.State Byte Word

/-- The response parser's lists have their lengths. -/
def Shaped (S : RState) : Prop :=
  S.modes.length = 4 ∧ S.positions.length = 10 ∧ S.kinds.length = 4 ∧ S.stack.length = 100 ∧ S.utf.length = 8

theorem zipWith_ones : ∀ (yes no : List Word), yes.length ≤ no.length →
    List.zipWith (Word64.fastSelect 255#8) yes no = yes
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | y :: ys, n :: ns, h => by
      rw [List.zipWith_cons_cons, fastSelect_ones, zipWith_ones ys ns (by simp at h; omega)]

theorem stateSelect_zero (yes no : RState) (hy : Shaped yes) (hn : Shaped no) :
    TlsChatResponse.stateSelect Word64.fast fast 0#8 yes no = no := by
  obtain ⟨y1, y2, y3, y4, y5⟩ := hy
  obtain ⟨n1, n2, n3, n4, n5⟩ := hn
  simp only [TlsChatResponse.stateSelect, TlsChatResponse.headerSelect, select_zero', w_select, fastSelect_zero,
    choose_zero yes.modes no.modes (by omega), choose_zero yes.positions no.positions (by omega),
    choose_zero yes.kinds no.kinds (by omega), choose_zero yes.utf no.utf (by omega),
    zipWith_zero yes.stack no.stack (by omega)]

theorem stateSelect_ones (yes no : RState) (hy : Shaped yes) (hn : Shaped no) :
    TlsChatResponse.stateSelect Word64.fast fast 255#8 yes no = yes := by
  obtain ⟨y1, y2, y3, y4, y5⟩ := hy
  obtain ⟨n1, n2, n3, n4, n5⟩ := hn
  simp only [TlsChatResponse.stateSelect, TlsChatResponse.headerSelect, select_ones', w_select, fastSelect_ones,
    choose_ones yes.modes no.modes (by omega), choose_ones yes.positions no.positions (by omega),
    choose_ones yes.kinds no.kinds (by omega), choose_ones yes.utf no.utf (by omega),
    zipWith_ones yes.stack no.stack (by omega)]

abbrev d := VarintDecode.Spqr.concrete
abbrev o := Word64.fast

theorem step_shaped (S : RState) (hS : Shaped S) (x : Byte) : Shaped (TlsChatResponse.step d o fast S x).state := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [TlsChatResponse.step, TlsWebSocketUpgrade.choose, TlsWebSocketUpgrade.initial, TlsChatResponse.writeStack,
      List.length_zipWith, h2, h3, h4, h5, utfStep_length]

theorem finish_shaped (S : RState) (hS : Shaped S) : Shaped (TlsChatResponse.finish o fast S) := hS

theorem and_idem (v y : Byte) : fast.and v (fast.and v y) = fast.and v y := by
  simp only [fast_and, ← BitVec.and_assoc, BitVec.and_self]

theorem canonical_ok (a b e : Byte) (ha : a = 0#8 ∨ a = 255#8) (hb : b = 0#8 ∨ b = 255#8) (he : e = 0#8 ∨ e = 255#8) :
    ([a, b, e]).foldl (fun valid mask => fast.and valid (TlsWebSocketUpgrade.either fast
      (TlsWebSocketUpgrade.eq fast mask 0) (TlsWebSocketUpgrade.eq fast mask 255))) (fast.const 0xff) = 255#8 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases he with rfl | rfl <;> decide

theorem eq00 : TlsWebSocketUpgrade.eq fast 0#8 255 = 0#8 := by decide
theorem eq11 : TlsWebSocketUpgrade.eq fast 255#8 255 = 255#8 := by decide
theorem and255 (v : Byte) : fast.and v 255#8 = v := by rw [fast_and]; exact and_ones v

/-- **`process_active`.** A payload byte that neither starts nor ends the message: `process` is `step`. -/
theorem process_active (cap : Nat) (S : RState) (hS : Shaped S) (x : Byte) :
    TlsChatResponse.process d o fast cap S 255#8 0#8 0#8 x =
      ⟨(TlsChatResponse.step d o fast S x).state, (TlsChatResponse.step d o fast S x).bodyData,
       (TlsChatResponse.step d o fast S x).bodyReset, (TlsChatResponse.step d o fast S x).headerData⟩ := by
  have hs := step_shaped S hS x
  have hc := canonical_ok 255#8 0#8 0#8 (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  unfold TlsChatResponse.process
  have hf : ∀ (v sn : Byte) (e : Word), Shaped { TlsChatResponse.initial o fast cap e with valid := v, seen := sn } :=
    fun _ _ _ => ⟨rfl, rfl, rfl, by simp [TlsChatResponse.initial], rfl⟩
  simp only [eq00, eq11, hc, stateSelect_zero _ S (hf _ _ _) hS, stateSelect_ones _ S hs hS, and255]
  have hsel : Shaped { (TlsChatResponse.step d o fast S x).state with
      valid := (TlsChatResponse.step d o fast S x).state.valid } := hs
  rw [stateSelect_zero _ _ (finish_shaped _ hsel) hsel]
  simp only [TlsChatResponse.step, and_idem]

open PublicReceive.PassOver (weq_ne sub_one_word)

def mb (b : Bool) : Byte := if b then 255 else 0

/-- The varint group `j` is next (one-hot over ten groups). -/
def Pos (j : Nat) : List Byte :=
  [mb (j == 0), mb (j == 1), mb (j == 2), mb (j == 3), mb (j == 4), mb (j == 5), mb (j == 6), mb (j == 7),
   mb (j == 8), mb (j == 9)]

theorem pos0 : TlsWebSocketUpgrade.initial fast 9 = Pos 0 := by decide

theorem o_shift (x : Word) (n : Nat) : o.shift x n = x >>> n := rfl
theorem o_band (x y : Word) : o.band x y = x &&& y := rfl
theorem o_add (x y : Word) : o.add x y = x + y := rfl
theorem o_ule (x y : Word) : o.ule x y = if x.toNat ≤ y.toNat then 255#8 else 0#8 := rfl
theorem d_orWord (x y : Word) : d.orWord x y = x ||| y := rfl

theorem contribution_22 :
    TlsChatResponse.contribution d fast [255#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] 0x22#8 = 34#64 := by
  decide

syntax "resp_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| resp_simp [$ts,*]) => `(tactic|
       simp [TlsChatResponse.step, TlsWebSocketUpgrade.get, TlsWebSocketUpgrade.either, TlsWebSocketUpgrade.any,
        TlsChatResponse.wmember, fast_and, fast_not, fast_const, fast_maskBit, select_zero', select_ones',
        eq_fast, weq_fast, w_select, w_sub, w_const, fastSelect_zero, fastSelect_ones, writeStack_zero,
        choose_zero, choose_ones, utfStep_length, TlsChatResponse.headerSelect, o_shift, o_band, o_add, o_ule,
        d_orWord, Pos, mb, TlsWebSocketUpgrade.initial, and_ones, xor_ones_ones, $ts,*])

/-- Inside the inner response, at a field key: the key `22` (field 4, the body, length-delimited). -/
theorem key_body (S : RState) (hv : S.valid = 255#8) (hs : S.seen = 255#8) (hf : S.finished = 0#8)
    (hm : S.modes = [255#8, 0#8, 0#8, 0#8]) (hp : S.positions = Pos 0) (hval : S.value = 0#64)
    (hi : S.inner = 255#8) (hd : S.depth = 0#64) (hrem : S.responseRemaining.toNat ≠ 1)
    (hbud : S.budget.toNat ≠ 0) (hS : Shaped S) :
    TlsChatResponse.step d o fast S 0x22#8 =
      ⟨{ S with
          modes := [0#8, 0#8, 255#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
          responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }, 0#8, 0#8, 0#8⟩ := by
  have c := contribution_22
  have w1 := weq_ne S.responseRemaining 1 hrem (by decide)
  have w0 := weq_ne S.budget 0 hbud (by decide)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hv hs hf hm hp hval hi hd w1 w0 h1 h2 h3 h4 h5
  subst hv hs hf hm hp hval hi hd
  resp_simp [c, w1, w0, Pos, mb, h1, h2, h3, h4, h5]

theorem payload_zero (i : Nat) : VarintDecode.Spqr.payload 0#8 i = 0#64 := by
  simp [VarintDecode.Spqr.payload]

theorem d_payload (x : Byte) (i : Nat) : d.payload x i = VarintDecode.Spqr.payload x i := rfl
theorem d_zero : d.zero = 0#64 := rfl
theorem bit7_true : ∀ x : Byte, 128 ≤ x.toNat → x.getLsbD 7 = true := by decide
theorem bit7_false : ∀ x : Byte, x.toNat < 128 → x.getLsbD 7 = false := by decide
theorem bit7_false' : ∀ x : Byte, x.toNat < 128 → x[7] = false := by decide
theorem bit7_true' : ∀ x : Byte, 128 ≤ x.toNat → x[7] = true := by decide

theorem contribution_pos (j : Nat) (hj : j < 10) (x : Byte) :
    TlsChatResponse.contribution d fast (Pos j) x = VarintDecode.Spqr.payload x j := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TlsChatResponse.contribution, Pos, mb, TlsWebSocketUpgrade.get, List.range_succ, d_orWord, d_payload,
      fast_and, payload_zero, d_zero]

/-- A varint byte that is not the last (bit 7 set), in the scalar or length mode, group `j < 9`. -/
theorem varint_more (S : RState) (m : List Byte) (hmode : m = [0#8, 255#8, 0#8, 0#8] ∨ m = [0#8, 0#8, 255#8, 0#8])
    (hv : S.valid = 255#8) (hs : S.seen = 255#8) (hf : S.finished = 0#8)
    (hm : S.modes = m) (j : Nat) (hj : j < 9) (hp : S.positions = Pos j)
    (hi : S.inner = 255#8) (hrem : S.responseRemaining.toNat ≠ 1)
    (hbud : S.budget.toNat ≠ 0) (hS : Shaped S) (x : Byte) (hx : 128 ≤ x.toNat) :
    TlsChatResponse.step d o fast S x =
      ⟨{ S with
          positions := Pos (j + 1), value := S.value ||| VarintDecode.Spqr.payload x j,
          responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }, 0#8, 0#8, 0#8⟩ := by
  have c := contribution_pos j (by omega) x
  have w1 := weq_ne S.responseRemaining 1 hrem (by decide)
  have w0 := weq_ne S.budget 0 hbud (by decide)
  have h7 : x.getLsbD 7 = true := bit7_true x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hv hs hf hm hp hi w1 w0 h1 h2 h3 h4 h5 c
  subst hv hs hf hm hp hi
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases hmode with rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Pos, mb] at c <;>
  resp_simp [c, w1, w0, h1, h2, h3, h4, h5, h7]

/-- The last byte of the body field's length (bit 7 clear): the body starts, `skip` is its length. -/
theorem length_end_body (S : RState) (hv : S.valid = 255#8) (hs : S.seen = 255#8) (hf : S.finished = 0#8)
    (hm : S.modes = [0#8, 0#8, 255#8, 0#8]) (j : Nat) (hj : j < 9) (hp : S.positions = Pos j)
    (hk : S.kinds = [0#8, 255#8, 0#8, 0#8]) (hi : S.inner = 255#8) (hd : S.depth = 0#64)
    (hrem : S.responseRemaining.toNat ≠ 1) (hbud : S.budget.toNat ≠ 0) (hS : Shaped S) (x : Byte) (hx : x.toNat < 128)
    (hn0 : (S.value ||| VarintDecode.Spqr.payload x j).toNat ≠ 0)
    (hle : (S.value ||| VarintDecode.Spqr.payload x j).toNat ≤ (S.responseRemaining - 1).toNat) :
    TlsChatResponse.step d o fast S x =
      ⟨{ S with
          modes := [0#8, 0#8, 0#8, 255#8], positions := Pos 0, value := 0#64,
          responseRemaining := S.responseRemaining - 1, budget := S.budget - 1,
          skip := S.value ||| VarintDecode.Spqr.payload x j, bodyPresent := 255#8,
          bodyLength := S.value ||| VarintDecode.Spqr.payload x j, utf := TlsWebSocketUpgrade.initial fast 7,
          header := TlsChatResponse.headerInitial fast }, 0#8, 255#8, 0#8⟩ := by
  have c := contribution_pos j (by omega) x
  have w1 := weq_ne S.responseRemaining 1 hrem (by decide)
  have w0 := weq_ne S.budget 0 hbud (by decide)
  have wn := weq_ne _ 0 hn0 (by decide)
  have h7 : x.getLsbD 7 = false := bit7_false x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hv hs hf hm hp hk hi hd w1 w0 wn h1 h2 h3 h4 h5 c hle
  subst hv hs hf hm hp hk hi hd
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Pos, mb] at c <;>
  resp_simp [c, w1, w0, wn, h1, h2, h3, h4, h5, h7, bit7_false' x hx, hle, TlsChatResponse.headerInitial] <;>
  simpa using hle

/-- A body byte that is not the body's last: the parser only counts (any byte value). -/
theorem body_byte (S : RState) (hv : S.valid = 255#8) (hs : S.seen = 255#8) (hf : S.finished = 0#8)
    (hm : S.modes = [0#8, 0#8, 0#8, 255#8]) (hk : S.kinds = [0#8, 255#8, 0#8, 0#8]) (hi : S.inner = 255#8)
    (hskip : S.skip.toNat ≠ 1) (hrem : S.responseRemaining.toNat ≠ 1) (hbud : S.budget.toNat ≠ 0)
    (hS : Shaped S) (x : Byte) :
    TlsChatResponse.step d o fast S x =
      ⟨{ S with
          skip := S.skip - 1, responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 },
        255#8, 0#8, 0#8⟩ := by
  have w1 := weq_ne S.responseRemaining 1 hrem (by decide)
  have w0 := weq_ne S.budget 0 hbud (by decide)
  have ws := weq_ne S.skip 1 hskip (by decide)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hv hs hf hm hk hi w1 w0 ws h1 h2 h3 h4 h5
  subst hv hs hf hm hk hi
  resp_simp [w1, w0, ws, h1, h2, h3, h4, h5]

/-- The body's last byte, more of the inner response to come: back to reading a key. -/
theorem body_last (S : RState) (hv : S.valid = 255#8) (hs : S.seen = 255#8) (hf : S.finished = 0#8)
    (hm : S.modes = [0#8, 0#8, 0#8, 255#8]) (hk : S.kinds = [0#8, 255#8, 0#8, 0#8]) (hi : S.inner = 255#8)
    (hskip : S.skip = 1#64) (hrem : S.responseRemaining.toNat ≠ 1) (hbud : S.budget.toNat ≠ 0)
    (hS : Shaped S) (x : Byte) :
    TlsChatResponse.step d o fast S x =
      ⟨{ S with
          modes := [255#8, 0#8, 0#8, 0#8], skip := 0#64, responseRemaining := S.responseRemaining - 1,
          budget := S.budget - 1 }, 255#8, 0#8, 0#8⟩ := by
  have w1 := weq_ne S.responseRemaining 1 hrem (by decide)
  have w0 := weq_ne S.budget 0 hbud (by decide)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hv hs hf hm hk hi hskip w1 w0 h1 h2 h3 h4 h5
  subst hv hs hf hm hk hi hskip
  resp_simp [w1, w0, h1, h2, h3, h4, h5]

/-- The body's last byte, also the inner response's last: back to reading a key, outside it. -/
theorem body_last_close (S : RState) (hv : S.valid = 255#8) (hs : S.seen = 255#8) (hf : S.finished = 0#8)
    (hm : S.modes = [0#8, 0#8, 0#8, 255#8]) (hk : S.kinds = [0#8, 255#8, 0#8, 0#8]) (hi : S.inner = 255#8)
    (hd : S.depth = 0#64) (hskip : S.skip = 1#64) (hrem : S.responseRemaining = 1#64) (hbud : S.budget.toNat ≠ 0)
    (hS : Shaped S) (x : Byte) :
    TlsChatResponse.step d o fast S x =
      ⟨{ S with
          modes := [255#8, 0#8, 0#8, 0#8], skip := 0#64, inner := 0#8, responseRemaining := 0#64,
          budget := S.budget - 1 }, 255#8, 0#8, 0#8⟩ := by
  have w0 := weq_ne S.budget 0 hbud (by decide)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hv hs hf hm hk hi hd hskip hrem w0 h1 h2 h3 h4 h5
  subst hv hs hf hm hk hi hd hskip hrem
  resp_simp [w0, h1, h2, h3, h4, h5]

/-! ### Varints -/

/-- Protocol Buffers' varint encoding (little-endian groups of 7 bits, bit 7 set on all but the last
byte): the minimal encoding, as protobuf-java writes it. -/
def varintGo : Nat → Nat → List Byte
  | 0, n => [BitVec.ofNat 8 n]
  | fuel + 1, n => if n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: varintGo fuel (n / 128)

def varint (n : Nat) : List Byte := varintGo n n

theorem varintGo_eq : ∀ (f g n : Nat), n ≤ f → n ≤ g → varintGo f n = varintGo g n
  | 0, 0, _, _, _ => rfl
  | 0, g + 1, n, h, _ => by
      have : n = 0 := by omega
      subst this; simp [varintGo]
  | f + 1, 0, n, _, h => by
      have : n = 0 := by omega
      subst this; simp [varintGo]
  | f + 1, g + 1, n, hf, hg => by
      simp only [varintGo]
      split
      · rfl
      · rw [varintGo_eq f g (n / 128) (by omega) (by omega)]

theorem varint_lt (n : Nat) (h : n < 128) : varint n = [BitVec.ofNat 8 n] := by
  unfold varint
  cases n with
  | zero => rfl
  | succ m => simp only [varintGo, if_pos h]

theorem varint_ge (n : Nat) (h : 128 ≤ n) : varint n = BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128) := by
  unfold varint
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [varintGo, if_neg (show ¬ (m + 1 < 128) by omega)]
  rw [varintGo_eq m ((m + 1) / 128) ((m + 1) / 128) (by omega) (by omega)]

theorem varint_length_pos (n : Nat) : 1 ≤ (varint n).length := by
  by_cases h : n < 128
  · rw [varint_lt n h]; simp
  · rw [varint_ge n (by omega)]; simp

theorem payload_toNat (x : Byte) (j : Nat) (hj : 7 * j + 7 ≤ 64) :
    (VarintDecode.Spqr.payload x j).toNat = x.toNat % 128 * 2 ^ (7 * j) := by
  have hx := x.isLt
  have h128 : x.toNat % 128 < 2 ^ 7 := by omega
  have hp : x.toNat % 128 * 2 ^ (7 * j) < 2 ^ 64 := by
    calc x.toNat % 128 * 2 ^ (7 * j) < 2 ^ 7 * 2 ^ (7 * j) := Nat.mul_lt_mul_of_pos_right h128 (Nat.two_pow_pos _)
      _ = 2 ^ (7 * j + 7) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hj
  simp only [VarintDecode.Spqr.payload, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth]
  have e1 : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt (by omega)
  have e2 : (127 : BitVec 64).toNat = 2 ^ 7 - 1 := rfl
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, show (2 : Nat) ^ 7 = 128 from rfl,
    Nat.mod_eq_of_lt hp]

theorem or_payload_toNat (V : Word) (x : Byte) (j : Nat) (hj : 7 * j + 7 ≤ 64) (hV : V.toNat < 2 ^ (7 * j)) :
    (V ||| VarintDecode.Spqr.payload x j).toNat = V.toNat + x.toNat % 128 * 2 ^ (7 * j) := by
  rw [BitVec.toNat_or, payload_toNat x j hj, ← Nat.shiftLeft_eq, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt hV, Nat.add_comm]

/-! ### Runs of `step` -/

abbrev Ev := TlsChatResponse.Event Byte Word

def sEvents : RState → List Byte → List Ev
  | _, [] => []
  | S, x :: xs => TlsChatResponse.step d o fast S x :: sEvents (TlsChatResponse.step d o fast S x).state xs

def sFinal : RState → List Byte → RState
  | S, [] => S
  | S, x :: xs => sFinal (TlsChatResponse.step d o fast S x).state xs

theorem sEvents_append : ∀ (S : RState) (a b : List Byte), sEvents S (a ++ b) = sEvents S a ++ sEvents (sFinal S a) b
  | _, [], _ => rfl
  | S, x :: xs, b => by simp only [List.cons_append, sEvents, sFinal]; rw [sEvents_append _ xs b]

theorem sFinal_append : ∀ (S : RState) (a b : List Byte), sFinal S (a ++ b) = sFinal (sFinal S a) b
  | _, [], _ => rfl
  | S, x :: xs, b => by simp only [List.cons_append, sFinal]; rw [sFinal_append _ xs b]

/-- Every event valid. -/
def AllValid (es : List Ev) : Prop := ∀ e ∈ es, e.state.valid = 255#8

theorem allValid_cons {e : Ev} {es : List Ev} (h : e.state.valid = 255#8) (hs : AllValid es) : AllValid (e :: es) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hs x hx

theorem allValid_nil : AllValid [] := fun _ h => absurd h List.not_mem_nil

theorem allValid_append {a b : List Ev} (ha : AllValid a) (hb : AllValid b) : AllValid (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact ha e h
  · exact hb e h

theorem ofNat_sub_one (r : Nat) (h : 1 ≤ r) (hr : r < 2 ^ 64) : BitVec.ofNat 64 r - 1 = BitVec.ofNat 64 (r - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Word).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem toNat_ofNat64 (r : Nat) (hr : r < 2 ^ 64) : (BitVec.ofNat 64 r).toNat = r := by
  simp; omega

/-- **Body bytes.** In the body (bytes mode, kind body) with `p.length + 1` bytes left in it and more
of the inner response after it: every byte is reported as body, the parser only counts. -/
theorem body_run :
    ∀ (p : List Byte) (b : Byte) (S : RState) (rem bud : Nat), rem < 2 ^ 64 → bud < 2 ^ 64 →
    S.valid = 255#8 → S.seen = 255#8 → S.finished = 0#8 →
    S.modes = [0#8, 0#8, 0#8, 255#8] → S.kinds = [0#8, 255#8, 0#8, 0#8] → S.inner = 255#8 →
    S.skip = BitVec.ofNat 64 (p.length + 1) → S.responseRemaining = BitVec.ofNat 64 rem →
    S.budget = BitVec.ofNat 64 bud → p.length + 2 ≤ rem → p.length + 1 ≤ bud → Shaped S →
    AllValid (sEvents S (p ++ [b])) ∧ (sEvents S (p ++ [b])).map (·.bodyData) = List.replicate (p.length + 1) 255#8 ∧
    (sEvents S (p ++ [b])).map (·.bodyReset) = List.replicate (p.length + 1) 0#8 ∧
    sFinal S (p ++ [b]) = { S with
      modes := [255#8, 0#8, 0#8, 0#8], skip := 0#64,
      responseRemaining := BitVec.ofNat 64 (rem - (p.length + 1)),
      budget := BitVec.ofNat 64 (bud - (p.length + 1)) }
  | [], b, S, rem, bud, hr, hb, hv, hs, hf, hm, hk, hi, hskip, hrem, hbud, h2, h1, hS => by
      simp only [List.length_nil] at h2 h1 hskip
      have e := body_last S hv hs hf hm hk hi (by rw [hskip]) (by rw [hrem, toNat_ofNat64 rem hr]; omega)
        (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS b
      simp only [List.nil_append, sEvents, sFinal, e, List.map_cons, List.map_nil]
      refine ⟨allValid_cons hv allValid_nil, rfl, rfl, ?_⟩
      rw [hrem, hbud, ofNat_sub_one rem (by omega) hr, ofNat_sub_one bud (by omega) hb]
      rfl
  | x :: p, b, S, rem, bud, hr, hb, hv, hs, hf, hm, hk, hi, hskip, hrem, hbud, h2, h1, hS => by
      simp only [List.length_cons] at hskip h2 h1
      have e := body_byte S hv hs hf hm hk hi (by rw [hskip, toNat_ofNat64 _ (by omega)]; omega)
        (by rw [hrem, toNat_ofNat64 rem hr]; omega) (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS x
      have ih := body_run p b
        { S with skip := S.skip - 1, responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }
        (rem - 1) (bud - 1) (by omega) (by omega) hv hs hf hm hk hi
        (by simp only; rw [hskip, ofNat_sub_one _ (by omega) (by omega), Nat.add_sub_cancel])
        (by simp only; rw [hrem, ofNat_sub_one _ (by omega) hr])
        (by simp only; rw [hbud, ofNat_sub_one _ (by omega) hb]) (by omega) (by omega) hS
      simp only [List.cons_append, sEvents, sFinal, e, List.map_cons]
      refine ⟨allValid_cons hv ih.1, by rw [ih.2.1]; rfl, by rw [ih.2.2.1]; rfl, ?_⟩
      rw [ih.2.2.2]
      simp only [List.length_cons]
      congr 2 <;> omega


theorem pow_step (j : Nat) : 2 ^ (7 * (j + 1)) = 2 ^ (7 * j) * 128 := by
  rw [show 7 * (j + 1) = 7 * j + 7 by omega, Nat.pow_add]

/-- **The body field's length.** Reading the varint `varint n` (from group `j`, `V` already read) in
the length mode of the body field: nothing is body yet, the last byte resets the body (`bodyReset`)
and the parser enters the body with `skip` = the length `V + 2^(7j)·n`. -/
theorem body_len_run : ∀ (n j : Nat) (S : RState) (V rem bud : Nat),
    S.valid = 255#8 → S.seen = 255#8 → S.finished = 0#8 → S.modes = [0#8, 0#8, 255#8, 0#8] →
    S.positions = Pos j → S.kinds = [0#8, 255#8, 0#8, 0#8] → S.inner = 255#8 → S.depth = 0#64 → Shaped S →
    S.value = BitVec.ofNat 64 V → V < 2 ^ (7 * j) → j + (varint n).length ≤ 9 →
    S.responseRemaining = BitVec.ofNat 64 rem → S.budget = BitVec.ofNat 64 bud → rem < 2 ^ 64 → bud < 2 ^ 64 →
    1 ≤ V + 2 ^ (7 * j) * n → (varint n).length + (V + 2 ^ (7 * j) * n) ≤ rem → (varint n).length ≤ bud →
    AllValid (sEvents S (varint n)) ∧
    (sEvents S (varint n)).map (·.bodyData) = List.replicate (varint n).length 0#8 ∧
    (sEvents S (varint n)).map (·.bodyReset) = List.replicate ((varint n).length - 1) 0#8 ++ [255#8] ∧
    sFinal S (varint n) = { S with
      modes := [0#8, 0#8, 0#8, 255#8], positions := Pos 0, value := 0#64,
      responseRemaining := BitVec.ofNat 64 (rem - (varint n).length),
      budget := BitVec.ofNat 64 (bud - (varint n).length),
      skip := BitVec.ofNat 64 (V + 2 ^ (7 * j) * n), bodyPresent := 255#8,
      bodyLength := BitVec.ofNat 64 (V + 2 ^ (7 * j) * n), utf := TlsWebSocketUpgrade.initial fast 7,
      header := TlsChatResponse.headerInitial fast } := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro j S V rem bud hv hs hf hm hp hk hi hd hS hval hV hlen hrem hbud hr hb hN hleq hbl
  have hP := Nat.two_pow_pos (7 * j)
  have hpos : 1 ≤ (varint n).length := varint_length_pos n
  have hV64 : V < 2 ^ 64 := Nat.lt_of_lt_of_le hV (Nat.pow_le_pow_right (by decide) (by omega))
  have hvn : S.value.toNat = V := by rw [hval, toNat_ofNat64 V hV64]
  by_cases h128 : n < 128
  · rw [varint_lt n h128] at hlen hleq hbl ⊢
    simp only [List.length_singleton] at hlen hleq hbl
    have hx : (BitVec.ofNat 8 n).toNat = n := by simp; omega
    have hor : (S.value ||| VarintDecode.Spqr.payload (BitVec.ofNat 8 n) j).toNat = V + 2 ^ (7 * j) * n := by
      rw [or_payload_toNat _ _ j (by omega) (by rw [hvn]; exact hV), hvn, hx, Nat.mod_eq_of_lt h128, Nat.mul_comm]
    have e := length_end_body S hv hs hf hm j (by omega) hp hk hi hd
      (by rw [hrem, toNat_ofNat64 rem hr]; omega) (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS
      (BitVec.ofNat 8 n) (by omega) (by rw [hor]; omega)
      (by rw [hor, hrem, ofNat_sub_one rem (by omega) hr, toNat_ofNat64 _ (by omega)]; omega)
    have hw : S.value ||| VarintDecode.Spqr.payload (BitVec.ofNat 8 n) j = BitVec.ofNat 64 (V + 2 ^ (7 * j) * n) := by
      apply BitVec.eq_of_toNat_eq; rw [hor, toNat_ofNat64 _ (by omega)]
    simp only [sEvents, sFinal, e, List.map_cons, List.map_nil, hw]
    refine ⟨allValid_cons hv allValid_nil, rfl, rfl, ?_⟩
    rw [hrem, hbud, ofNat_sub_one rem (by omega) hr, ofNat_sub_one bud (by omega) hb]
    rfl
  · have hge : 128 ≤ n := by omega
    rw [varint_ge n hge] at hlen hleq hbl ⊢
    simp only [List.length_cons] at hlen hleq hbl
    have hpos' : 1 ≤ (varint (n / 128)).length := varint_length_pos _
    have hx : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 := by simp; omega
    have hor : (S.value ||| VarintDecode.Spqr.payload (BitVec.ofNat 8 (n % 128 + 128)) j).toNat =
        V + n % 128 * 2 ^ (7 * j) := by
      rw [or_payload_toNat _ _ j (by omega) (by rw [hvn]; exact hV), hvn, hx]; congr 2; omega
    have hP7 := pow_step j
    have hm127 : n % 128 * 2 ^ (7 * j) ≤ 127 * 2 ^ (7 * j) := Nat.mul_le_mul_right _ (by omega)
    have hV' : V + n % 128 * 2 ^ (7 * j) < 2 ^ (7 * (j + 1)) := by rw [hP7]; omega
    have hNeq : V + n % 128 * 2 ^ (7 * j) + 2 ^ (7 * (j + 1)) * (n / 128) = V + 2 ^ (7 * j) * n := by
      rw [hP7, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm (n % 128), ← Nat.mul_add, Nat.mod_add_div]
    have e := varint_more S [0#8, 0#8, 255#8, 0#8] (Or.inr rfl) hv hs hf hm j (by omega) hp hi
      (by rw [hrem, toNat_ofNat64 rem hr]; omega) (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS
      (BitVec.ofNat 8 (n % 128 + 128)) (by omega)
    have hw : S.value ||| VarintDecode.Spqr.payload (BitVec.ofNat 8 (n % 128 + 128)) j =
        BitVec.ofNat 64 (V + n % 128 * 2 ^ (7 * j)) := by
      apply BitVec.eq_of_toNat_eq; rw [hor, toNat_ofNat64 _ (by omega)]
    have ih' := ih (n / 128) (by omega) (j + 1)
      { S with positions := Pos (j + 1), value := BitVec.ofNat 64 (V + n % 128 * 2 ^ (7 * j)),
               responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }
      (V + n % 128 * 2 ^ (7 * j)) (rem - 1) (bud - 1) hv hs hf hm rfl hk hi hd
      ⟨hS.1, rfl, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2⟩ rfl hV' (by omega)
      (by simp only; rw [hrem, ofNat_sub_one rem (by omega) hr])
      (by simp only; rw [hbud, ofNat_sub_one bud (by omega) hb]) (by omega) (by omega)
      (by rw [hNeq]; exact hN) (by rw [hNeq]; omega) (by omega)
    rw [hNeq] at ih'
    simp only [sEvents, sFinal, e, List.map_cons, hw]
    refine ⟨allValid_cons hv ih'.1, by rw [ih'.2.1]; rfl, ?_, ?_⟩
    · rw [ih'.2.2.1]
      obtain ⟨k, hk'⟩ : ∃ k, (varint (n / 128)).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos').symm⟩
      simp only [List.length_cons, hk', Nat.add_sub_cancel, List.replicate_succ, List.cons_append]
    · rw [ih'.2.2.2]
      simp only [List.length_cons]
      congr 2 <;> omega

/-- Body bytes ending exactly where the inner response ends. -/
theorem body_run_close :
    ∀ (p : List Byte) (b : Byte) (S : RState) (rem bud : Nat), rem < 2 ^ 64 → bud < 2 ^ 64 →
    S.valid = 255#8 → S.seen = 255#8 → S.finished = 0#8 →
    S.modes = [0#8, 0#8, 0#8, 255#8] → S.kinds = [0#8, 255#8, 0#8, 0#8] → S.inner = 255#8 → S.depth = 0#64 →
    S.skip = BitVec.ofNat 64 (p.length + 1) → S.responseRemaining = BitVec.ofNat 64 rem →
    S.budget = BitVec.ofNat 64 bud → p.length + 1 = rem → p.length + 1 ≤ bud → Shaped S →
    AllValid (sEvents S (p ++ [b])) ∧ (sEvents S (p ++ [b])).map (·.bodyData) = List.replicate (p.length + 1) 255#8 ∧
    (sEvents S (p ++ [b])).map (·.bodyReset) = List.replicate (p.length + 1) 0#8 ∧
    sFinal S (p ++ [b]) = { S with
      modes := [255#8, 0#8, 0#8, 0#8], skip := 0#64, inner := 0#8, responseRemaining := 0#64,
      budget := BitVec.ofNat 64 (bud - (p.length + 1)) }
  | [], b, S, rem, bud, hr, hb, hv, hs, hf, hm, hk, hi, hd, hskip, hrem, hbud, h2, h1, hS => by
      simp only [List.length_nil] at h2 h1 hskip
      have e := body_last_close S hv hs hf hm hk hi hd (by rw [hskip]) (by rw [hrem, ← h2])
        (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS b
      simp only [List.nil_append, sEvents, sFinal, e, List.map_cons, List.map_nil]
      refine ⟨allValid_cons hv allValid_nil, rfl, rfl, ?_⟩
      rw [hbud, ofNat_sub_one bud (by omega) hb]
      rfl
  | x :: p, b, S, rem, bud, hr, hb, hv, hs, hf, hm, hk, hi, hd, hskip, hrem, hbud, h2, h1, hS => by
      simp only [List.length_cons] at hskip h2 h1
      have e := body_byte S hv hs hf hm hk hi (by rw [hskip, toNat_ofNat64 _ (by omega)]; omega)
        (by rw [hrem, toNat_ofNat64 rem hr]; omega) (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS x
      have ih := body_run_close p b
        { S with skip := S.skip - 1, responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }
        (rem - 1) (bud - 1) (by omega) (by omega) hv hs hf hm hk hi hd
        (by simp only; rw [hskip, ofNat_sub_one _ (by omega) (by omega), Nat.add_sub_cancel])
        (by simp only; rw [hrem, ofNat_sub_one _ (by omega) hr])
        (by simp only; rw [hbud, ofNat_sub_one _ (by omega) hb]) (by omega) (by omega) hS
      simp only [List.cons_append, sEvents, sFinal, e, List.map_cons]
      refine ⟨allValid_cons hv ih.1, by rw [ih.2.1]; rfl, by rw [ih.2.2.1]; rfl, ?_⟩
      rw [ih.2.2.2]
      simp only [List.length_cons]
      congr 2; omega

/-- The inner response at a field key: valid, started, not finished, key mode, varint group 0, no
partial value, inside the inner response, no group open. -/
def KeyIn (S : RState) : Prop :=
  S.valid = 255#8 ∧ S.seen = 255#8 ∧ S.finished = 0#8 ∧ S.modes = [255#8, 0#8, 0#8, 0#8] ∧ S.positions = Pos 0 ∧
    S.value = 0#64 ∧ S.inner = 255#8 ∧ S.depth = 0#64 ∧ Shaped S

/-- The bytes of the body field (field 4, `bytes body`) as protobuf-java writes them: key `22`, the
length as a varint, the body. -/
def bodyField (body : List Byte) : List Byte := 0x22#8 :: varint body.length ++ body

/-- **`body_field`.** From a field key inside the inner response, with `rem` bytes of the inner
response and `bud` of the budget left, the body field with a non-empty body followed by more of the
inner response: every event valid; `bodyData` exactly on the body's bytes (none on the key and the
length); `bodyReset` exactly on the length's last byte; afterwards at a field key again, the counts
lowered by the field's size, the body's length recorded. -/
theorem body_field (S : RState) (hK : KeyIn S) (rem bud : Nat) (hr : rem < 2 ^ 64) (hb : bud < 2 ^ 64)
    (hrem : S.responseRemaining = BitVec.ofNat 64 rem) (hbud : S.budget = BitVec.ofNat 64 bud)
    (body : List Byte) (hne : body ≠ []) (hv9 : (varint body.length).length ≤ 9)
    (hfit : (bodyField body).length < rem) (hbfit : (bodyField body).length ≤ bud) :
    AllValid (sEvents S (bodyField body)) ∧
    (sEvents S (bodyField body)).map (·.bodyData) =
      List.replicate (1 + (varint body.length).length) 0#8 ++ List.replicate body.length 255#8 ∧
    (sEvents S (bodyField body)).map (·.bodyReset) =
      List.replicate (varint body.length).length 0#8 ++ [255#8] ++ List.replicate body.length 0#8 ∧
    sFinal S (bodyField body) = { S with
      modes := [255#8, 0#8, 0#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
      responseRemaining := BitVec.ofNat 64 (rem - (bodyField body).length),
      budget := BitVec.ofNat 64 (bud - (bodyField body).length), skip := 0#64, bodyPresent := 255#8,
      bodyLength := BitVec.ofNat 64 body.length, utf := TlsWebSocketUpgrade.initial fast 7,
      header := TlsChatResponse.headerInitial fast } := by
  obtain ⟨hv, hs, hf, hm, hp, hval, hi, hd, hS⟩ := hK
  obtain ⟨p, b, rfl⟩ : ∃ p b, body = p ++ [b] := by
    rcases List.eq_nil_or_concat body with h | ⟨p, b, h⟩
    · exact absurd h hne
    · exact ⟨p, b, by rw [h, List.concat_eq_append]⟩
  have hL : (bodyField (p ++ [b])).length = 1 + (varint (p.length + 1)).length + (p.length + 1) := by
    simp [bodyField]; omega
  simp only [List.length_append, List.length_singleton] at hv9 hL ⊢
  rw [hL] at hfit hbfit ⊢
  have hpos : 1 ≤ (varint (p.length + 1)).length := varint_length_pos _
  -- the key
  have e1 := key_body S hv hs hf hm hp hval hi hd (by rw [hrem, toNat_ofNat64 rem hr]; omega)
    (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS
  -- the length
  have r1 := body_len_run (p.length + 1) 0
    { S with modes := [0#8, 0#8, 255#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
             responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }
    0 (rem - 1) (bud - 1) hv hs hf rfl hp rfl hi hd ⟨rfl, hS.2.1, rfl, hS.2.2.2.1, hS.2.2.2.2⟩ hval (by decide)
    (by omega) (by simp only; rw [hrem, ofNat_sub_one rem (by omega) hr])
    (by simp only; rw [hbud, ofNat_sub_one bud (by omega) hb]) (by omega) (by omega)
    (by simp) (by simp; omega) (by omega)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at r1
  -- the body
  have r2 := body_run p b (sFinal
    { S with modes := [0#8, 0#8, 255#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
             responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 } (varint (p.length + 1)))
    (rem - 1 - (varint (p.length + 1)).length) (bud - 1 - (varint (p.length + 1)).length)
    (by omega) (by omega) (by rw [r1.2.2.2]; exact hv) (by rw [r1.2.2.2]; exact hs) (by rw [r1.2.2.2]; exact hf)
    (by rw [r1.2.2.2]) (by rw [r1.2.2.2]) (by rw [r1.2.2.2]; exact hi) (by rw [r1.2.2.2])
    (by rw [r1.2.2.2]) (by rw [r1.2.2.2]) (by omega) (by omega)
    (by rw [r1.2.2.2]; exact ⟨rfl, rfl, rfl, hS.2.2.2.1, rfl⟩)
  have hsplit : bodyField (p ++ [b]) = 0x22#8 :: (varint (p.length + 1) ++ (p ++ [b])) := by
    simp [bodyField]
  rw [hsplit]
  simp only [sEvents, sFinal]
  rw [e1]
  dsimp only
  rw [sEvents_append _ (varint _) (p ++ [b]), sFinal_append _ (varint _) (p ++ [b])]
  obtain ⟨k, hk⟩ : ∃ k, (varint (p.length + 1)).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  refine ⟨allValid_append (allValid_cons hv r1.1) r2.1, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, r1.2.1, r2.2.1, hk]
    rw [show 1 + (k + 1) = k + 1 + 1 by omega]
    simp only [List.replicate_succ, List.cons_append]
  · simp only [List.map_append, List.map_cons, r1.2.2.1, r2.2.2.1, hk]
    simp [List.replicate_succ]
  · rw [r2.2.2.2, r1.2.2.2]
    simp only [hp, hval]
    congr 2 <;> omega

/-- **`body_field_close`.** As `body_field`, the body being the inner response's last field: the
parser leaves the inner response (`inner` 0, `responseRemaining` 0) at the body's last byte. -/
theorem body_field_close (S : RState) (hK : KeyIn S) (rem bud : Nat) (hr : rem < 2 ^ 64) (hb : bud < 2 ^ 64)
    (hrem : S.responseRemaining = BitVec.ofNat 64 rem) (hbud : S.budget = BitVec.ofNat 64 bud)
    (body : List Byte) (hne : body ≠ []) (hv9 : (varint body.length).length ≤ 9)
    (hfit : (bodyField body).length = rem) (hbfit : (bodyField body).length ≤ bud) :
    AllValid (sEvents S (bodyField body)) ∧
    (sEvents S (bodyField body)).map (·.bodyData) =
      List.replicate (1 + (varint body.length).length) 0#8 ++ List.replicate body.length 255#8 ∧
    (sEvents S (bodyField body)).map (·.bodyReset) =
      List.replicate (varint body.length).length 0#8 ++ [255#8] ++ List.replicate body.length 0#8 ∧
    sFinal S (bodyField body) = { S with
      modes := [255#8, 0#8, 0#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
      inner := 0#8, responseRemaining := 0#64,
      budget := BitVec.ofNat 64 (bud - (bodyField body).length), skip := 0#64, bodyPresent := 255#8,
      bodyLength := BitVec.ofNat 64 body.length, utf := TlsWebSocketUpgrade.initial fast 7,
      header := TlsChatResponse.headerInitial fast } := by
  obtain ⟨hv, hs, hf, hm, hp, hval, hi, hd, hS⟩ := hK
  obtain ⟨p, b, rfl⟩ : ∃ p b, body = p ++ [b] := by
    rcases List.eq_nil_or_concat body with h | ⟨p, b, h⟩
    · exact absurd h hne
    · exact ⟨p, b, by rw [h, List.concat_eq_append]⟩
  have hL : (bodyField (p ++ [b])).length = 1 + (varint (p.length + 1)).length + (p.length + 1) := by
    simp [bodyField]; omega
  simp only [List.length_append, List.length_singleton] at hv9 hL ⊢
  rw [hL] at hfit hbfit ⊢
  have hpos : 1 ≤ (varint (p.length + 1)).length := varint_length_pos _
  have e1 := key_body S hv hs hf hm hp hval hi hd (by rw [hrem, toNat_ofNat64 rem hr]; omega)
    (by rw [hbud, toNat_ofNat64 bud hb]; omega) hS
  have r1 := body_len_run (p.length + 1) 0
    { S with modes := [0#8, 0#8, 255#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
             responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 }
    0 (rem - 1) (bud - 1) hv hs hf rfl hp rfl hi hd ⟨rfl, hS.2.1, rfl, hS.2.2.2.1, hS.2.2.2.2⟩ hval (by decide)
    (by omega) (by simp only; rw [hrem, ofNat_sub_one rem (by omega) hr])
    (by simp only; rw [hbud, ofNat_sub_one bud (by omega) hb]) (by omega) (by omega)
    (by simp) (by simp; omega) (by omega)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at r1
  have r2 := body_run_close p b (sFinal
    { S with modes := [0#8, 0#8, 255#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
             responseRemaining := S.responseRemaining - 1, budget := S.budget - 1 } (varint (p.length + 1)))
    (rem - 1 - (varint (p.length + 1)).length) (bud - 1 - (varint (p.length + 1)).length)
    (by omega) (by omega) (by rw [r1.2.2.2]; exact hv) (by rw [r1.2.2.2]; exact hs) (by rw [r1.2.2.2]; exact hf)
    (by rw [r1.2.2.2]) (by rw [r1.2.2.2]) (by rw [r1.2.2.2]; exact hi) (by rw [r1.2.2.2]; exact hd)
    (by rw [r1.2.2.2]) (by rw [r1.2.2.2]) (by rw [r1.2.2.2]) (by omega) (by omega)
    (by rw [r1.2.2.2]; exact ⟨rfl, rfl, rfl, hS.2.2.2.1, rfl⟩)
  have hsplit : bodyField (p ++ [b]) = 0x22#8 :: (varint (p.length + 1) ++ (p ++ [b])) := by
    simp [bodyField]
  rw [hsplit]
  simp only [sEvents, sFinal]
  rw [e1]
  dsimp only
  rw [sEvents_append _ (varint _) (p ++ [b]), sFinal_append _ (varint _) (p ++ [b])]
  obtain ⟨k, hk⟩ : ∃ k, (varint (p.length + 1)).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  refine ⟨allValid_append (allValid_cons hv r1.1) r2.1, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, r1.2.1, r2.2.1, hk]
    rw [show 1 + (k + 1) = k + 1 + 1 by omega]
    simp only [List.replicate_succ, List.cons_append]
  · simp only [List.map_append, List.map_cons, r1.2.2.1, r2.2.2.1, hk]
    simp [List.replicate_succ]
  · rw [r2.2.2.2, r1.2.2.2]
    simp only [hp, hval]
    congr 2; omega

/-! ### Malformed: the validity byte drops (fail closed) -/

/-- The body's declared length is more than what is left of the inner response: the step at the
length's last byte is invalid, before any byte is reported as body. -/
theorem reject_body_length (S : RState) (hm : S.modes = [0#8, 0#8, 255#8, 0#8]) (j : Nat) (hj : j < 9)
    (hp : S.positions = Pos j) (hi : S.inner = 255#8) (hS : Shaped S) (x : Byte) (hx : x.toNat < 128)
    (hgt : (S.responseRemaining - 1).toNat < (S.value ||| VarintDecode.Spqr.payload x j).toNat) :
    (TlsChatResponse.step d o fast S x).state.valid = 0#8 := by
  have c := contribution_pos j (by omega) x
  have h7 : x.getLsbD 7 = false := bit7_false x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hm hp hi h1 h2 h3 h4 h5 c hgt
  subst hm hp hi
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  have hng : ¬ ((value ||| VarintDecode.Spqr.payload x j).toNat ≤ (responseRemaining - 1).toNat) := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Pos, mb] at c <;>
  resp_simp [c, h1, h2, h3, h4, h5, h7, bit7_false' x hx] <;>
  (have hg := hgt; simp at hg; rw [if_neg (Nat.not_le.mpr hg)]; simp)

/-- The message ends (its frame's last byte) while the parser is still inside a field (here: the
body): `finish` finds no field boundary and the validity byte drops. -/
theorem reject_end_in_field (S : RState) (hm : S.modes = [0#8, 0#8, 0#8, 255#8]) :
    (TlsChatResponse.finish o fast S).valid = 0#8 := by
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  simp only at hm
  subst hm
  simp [TlsChatResponse.finish, TlsWebSocketUpgrade.get, fast_and, fast_not, fast_const]

/-! ### `runByte`, as the controller calls it -/

/-- The six output bytes `runByte` puts before the next state. -/
def outBytes (e : Ev) : List Byte := [e.state.valid, e.state.finished, e.state.successful, e.bodyData, e.bodyReset,
  e.headerData]

theorem runByte_process (cap : Nat) (S : RState) (hS : Shaped S) (a b e x : Byte) :
    TlsChatResponse.runByte d o fast cap (TlsChatResponse.stateBytes o S ++ [a, b, e] ++ [x]) =
      outBytes (TlsChatResponse.process d o fast cap S a b e x) ++
        TlsChatResponse.stateBytes o (TlsChatResponse.process d o fast cap S a b e x).state := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  have hlen : (TlsChatResponse.stateBytes o S).length = 932 := stateBytes_length S h1 h2 h3 h4 h5
  unfold TlsChatResponse.runByte
  have ht : (TlsChatResponse.stateBytes o S ++ [a, b, e] ++ [x]).take TlsChatResponse.stateSize =
      TlsChatResponse.stateBytes o S := by
    rw [List.append_assoc]; exact List.take_left' hlen
  have g : ∀ i, TlsWebSocketUpgrade.get fast (TlsChatResponse.stateBytes o S ++ [a, b, e] ++ [x])
      (TlsChatResponse.stateSize + i) = [a, b, e, x].getD i (fast.const 0) := by
    intro i
    simp only [TlsWebSocketUpgrade.get, TlsChatResponse.stateSize, List.append_assoc, List.cons_append,
      List.nil_append, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  have g0 := g 0
  rw [Nat.add_zero] at g0
  rw [ht, g0, g 1, g 2, g 3, readState_stateBytes S h1 h2 h3 h4 h5]
  rfl

/-- The controller's loop over the response parser: feed `state ++ flags ++ [byte]`, keep the first 6
output bytes, the rest is the next state. -/
def respRun (cap : Nat) : List Byte → List (List Byte × Byte) → List (List Byte) × List Byte
  | raw, [] => ([], raw)
  | raw, (flags, x) :: rest =>
    let out := TlsChatResponse.runByte d o fast cap (raw ++ flags ++ [x])
    let r := respRun cap (out.drop 6) rest
    (out.take 6 :: r.1, r.2)

theorem sFinal_shaped : ∀ (S : RState) (xs : List Byte), Shaped S → Shaped (sFinal S xs)
  | _, [], h => h
  | S, x :: xs, h => sFinal_shaped _ xs (step_shaped S h x)

/-- **`respRun_active`.** Payload bytes that neither start nor end the message (flags `255 0 0`, what
the controller feeds for them), from the serialised state: `runByte` iterated is `step` iterated. -/
theorem respRun_active (cap : Nat) : ∀ (xs : List Byte) (S : RState), Shaped S →
    respRun cap (TlsChatResponse.stateBytes o S) (xs.map (fun x => ([255#8, 0#8, 0#8], x))) =
      ((sEvents S xs).map outBytes, TlsChatResponse.stateBytes o (sFinal S xs))
  | [], _, _ => rfl
  | x :: xs, S, hS => by
      simp only [List.map_cons, respRun]
      rw [runByte_process cap S hS 255#8 0#8 0#8 x, process_active cap S hS x]
      have hl : (outBytes ⟨(TlsChatResponse.step d o fast S x).state, (TlsChatResponse.step d o fast S x).bodyData,
          (TlsChatResponse.step d o fast S x).bodyReset, (TlsChatResponse.step d o fast S x).headerData⟩).length = 6 := rfl
      rw [List.drop_left' hl, List.take_left' hl, respRun_active cap xs _ (step_shaped S hS x)]
      rfl

theorem sEvents_length : ∀ (S : RState) (xs : List Byte), (sEvents S xs).length = xs.length
  | _, [] => rfl
  | S, x :: xs => by simp only [sEvents, List.length_cons, sEvents_length _ xs]

theorem allValid_map : ∀ (es : List Ev), AllValid es →
    es.map ((fun out : List Byte => out.getD 0 0) ∘ outBytes) = List.replicate es.length 255#8
  | [], _ => rfl
  | e :: es, h => by
      simp only [List.map_cons, List.length_cons, List.replicate_succ, Function.comp, outBytes]
      rw [allValid_map es (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      simp [h e (List.mem_cons_self ..)]

theorem sEvents_finished : ∀ (S : RState) (xs : List Byte), S.finished = 0#8 →
    (sEvents S xs).map ((fun out : List Byte => out.getD 1 0) ∘ outBytes) = List.replicate (sEvents S xs).length 0#8
  | _, [], _ => rfl
  | S, x :: xs, h => by
      simp only [sEvents, List.map_cons, List.length_cons, List.replicate_succ, Function.comp, outBytes]
      have hf : (TlsChatResponse.step d o fast S x).state.finished = 0#8 := h
      rw [← sEvents_finished _ xs hf]
      simp [hf]

/-- **`body_field_runByte`.** `body_field` through the deployed `runByte`, as the controller runs it: over
the body field's bytes (each fed with flags `255 0 0`), output byte 0 (validity) is 255 throughout,
output byte 3 (`bodyData`) is 255 exactly on the body's bytes, output byte 4 (`bodyReset`) exactly on
the length's last byte, output byte 1 (`finished`) 0. -/
theorem body_field_runByte (cap : Nat) (S : RState) (hK : KeyIn S) (rem bud : Nat) (hr : rem < 2 ^ 64)
    (hb : bud < 2 ^ 64) (hrem : S.responseRemaining = BitVec.ofNat 64 rem) (hbud : S.budget = BitVec.ofNat 64 bud)
    (body : List Byte) (hne : body ≠ []) (hv9 : (varint body.length).length ≤ 9)
    (hfit : (bodyField body).length < rem) (hbfit : (bodyField body).length ≤ bud) :
    let outs := (respRun cap (TlsChatResponse.stateBytes o S)
      ((bodyField body).map (fun x => ([255#8, 0#8, 0#8], x)))).1
    outs.map (fun out : List Byte => out.getD 0 0) = List.replicate (bodyField body).length 255#8 ∧
    outs.map (fun out : List Byte => out.getD 1 0) = List.replicate (bodyField body).length 0#8 ∧
    outs.map (fun out : List Byte => out.getD 3 0) =
      List.replicate (1 + (varint body.length).length) 0#8 ++ List.replicate body.length 255#8 ∧
    outs.map (fun out : List Byte => out.getD 4 0) =
      List.replicate (varint body.length).length 0#8 ++ [255#8] ++ List.replicate body.length 0#8 := by
  obtain ⟨hall, hbd, hbr, hfin⟩ := body_field S hK rem bud hr hb hrem hbud body hne hv9 hfit hbfit
  have hS : Shaped S := hK.2.2.2.2.2.2.2.2
  intro outs
  have ho : outs = (sEvents S (bodyField body)).map outBytes := by
    show (respRun cap _ _).1 = _
    rw [respRun_active cap (bodyField body) S hS]
  rw [ho]
  simp only [List.map_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sEvents_length S (bodyField body)]; exact allValid_map _ hall
  · rw [← sEvents_length S (bodyField body)]; exact sEvents_finished S _ hK.2.2.1
  · rw [← hbd]; rfl
  · rw [← hbr]; rfl

/-- The reference reads a body field the way `body_field` says the parser does: in a response whose
inner message is `bodyField body` alone, the body's extent is the bytes after the key and the
length. (Example, kernel-evaluated; the vectors check whole messages.) -/
theorem wsMessage_body_example :
    wsMessage ([0x08, 0x02, 0x1a, 0x05] ++ bodyField [0xaa, 0xbb, 0xcc]) =
      some ⟨some 2, false, none, none, none, some (6, 3), []⟩ := by
  decide +kernel

end TlsMpc.KernelSpecs.ParseChatResponse
