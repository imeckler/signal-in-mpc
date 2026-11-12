import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsChatResponse
import TlsMpc.Signal.Word64Fast

/-!
# Passing over an unrevealed body in bulk

The controller (`handshake_backend/EmpHybridWork/PublicServiceController.lean`) passes over the
unrevealed body of a server response (`stepPassed`) or server request (`stepSkipped`) one byte at a
time: for each byte it runs, in the clear, the circuit-shaped frame parser
(`TlsWebSocketFrame.runByte`, fed the active byte `[255, 0]`: the byte is not revealed, so a zero
stands in for it), the control queue (`TlsWebSocketControl.run`, fed the frame parser's control
outputs and a zero byte) and, for a response awaited, the response parser
(`TlsChatResponse.runByte`, fed the frame flags and a zero byte). About a millisecond per byte.

What those parsers do inside a body, read off their definitions and proved here for exactly the
inputs the controller feeds them:

* frame parser (`frame_step_room`): inside the payload of a valid data frame, with more than one
  payload byte left and room left in the message, it reports a valid data byte that ends nothing,
  and only its two 16-bit counts (payload left, message capacity left) go down by one;
* control queue (`control_idle`): given no control data, no frame end and no opcode, its step is
  the identity on its state when its counts are in range;
* response parser (`response_step_room`): inside the body field of the inner response, with more
  than one body byte and inner-response byte left and budget left, it stays valid, does not finish,
  reports a body byte, and only three 64-bit counts (`skip`, `budget`, `responseRemaining`) go down
  by one.

So `k` such bytes are `frameBulk k` / the identity / `responseBulk k`, computed in one step, as long
as `k` is within `frameRoom` / `controlIdle` / `responseRoom` (decidable conditions on the states;
0 or false when the state has any other shape). The controller's `passRun_bulk` combines these into
the theorem that its bulk step equals its byte-by-byte loop. None of the parser modules is changed:
the circuits are compiled from them, and no emitter imports this module.

`fast` (the controller's byte operations, equal to `ByteAuth.concrete`) moved here from the
controller unchanged, so that these theorems can be stated about it. Pure: no I/O.
-/

open TlsMpc TlsMpc.Signal

namespace PublicReceive

/-! The byte operations the controller's parsers run on, for values in the clear (moved here
unchanged from the controller, which imports this module, so that the pass-over theorems below can
be stated about them). Equal to `ByteAuth.concrete` (`fast_eq`); the differences are in how three
operations are computed at run time. `ByteAuth.concrete` builds the mask of one bit with
`BitVec.replicate`, and its constants and complements go through `2 ^ 8` as an arbitrary-precision
power each time; together that made every parsed byte cost milliseconds. -/

def fastConst (n : Nat) : BitVec 8 := BitVec.ofFin ⟨n % 256, Nat.mod_lt n (by decide)⟩
theorem fastConst_eq (n : Nat) : fastConst n = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp [fastConst]

def fastNot (x : BitVec 8) : BitVec 8 := x ^^^ 255#8
theorem fastNot_eq : ∀ x : BitVec 8, fastNot x = ~~~x := by decide

def fastMask (x : BitVec 8) (i : Nat) : BitVec 8 := if x.getLsbD i then 255#8 else 0#8

theorem fastMask_eq (x : BitVec 8) (i : Nat) : fastMask x i = BitVec.replicate 8 (x.extractLsb' i 1) := by
  have h : x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hz : j = 0 := by omega
    subst hz
    simp
  rw [h]
  unfold fastMask
  cases x.getLsbD i <;> decide

def fast : ByteAuth.Ops (BitVec 8) where
  const := fastConst
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := fastNot
  maskBit := fastMask

theorem fast_eq : fast = ByteAuth.concrete := by
  have hc : fastConst = BitVec.ofNat 8 := funext fastConst_eq
  have hn : fastNot = (fun x : BitVec 8 => ~~~x) := funext fastNot_eq
  have hm : fastMask = (fun (x : BitVec 8) (i : Nat) => BitVec.replicate 8 (x.extractLsb' i 1)) :=
    funext fun x => funext fun i => fastMask_eq x i
  unfold fast ByteAuth.concrete
  rw [hc, hn, hm]

end PublicReceive

namespace PublicReceive.PassOver
open TlsWebSocketUpgrade (get eq either any member choose initial)

abbrev Byte := BitVec 8

theorem fast_and (x y : Byte) : fast.and x y = x &&& y := rfl
theorem fast_not (x : Byte) : fast.not x = x ^^^ 255#8 := rfl
theorem fast_const (n : Nat) : fast.const n = BitVec.ofNat 8 n := fastConst_eq n
theorem fast_maskBit (x : Byte) (i : Nat) : fast.maskBit x i = if x.getLsbD i then 255#8 else 0#8 := rfl

theorem select_zero (y n : Byte) : TlsInner.select fast 0 y n = n := by
  rw [fast_eq]; exact TlsInner.select_reject y n
theorem select_ones (y n : Byte) : TlsInner.select fast 255 y n = y := by
  rw [fast_eq]; exact TlsInner.select_accept y n
theorem select_zero' (y n : Byte) : TlsInner.select fast 0#8 y n = n := select_zero y n
theorem select_ones' (y n : Byte) : TlsInner.select fast 255#8 y n = y := select_ones y n

theorem eq_fast (x : Byte) (n : Nat) : eq fast x n = if x = BitVec.ofNat 8 n then 255 else 0 := by
  unfold eq
  rw [fast_eq]
  exact ByteAuth.eqMask_value x _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The frame parser on one active zero byte, its state in the payload phase of a valid, unclosed
data frame (opcode 0 or 2) past its first two payload bytes, more than one payload byte left
(`one` is 0) and message capacity left (`zero` is 0): valid, a data byte, nothing ends; the payload
and message counts are decremented, every other state byte is kept. -/
theorem frame_step (cap : Nat) (op fin frag hi lo mh ml cc cv u0 u1 u2 u3 u4 u5 u6 u7 : Byte)
    (hop : op = 0 ∨ op = 2) (hone : TlsWebSocketFrame.one fast hi lo = 0)
    (hzero : TlsWebSocketFrame.zero fast mh ml = 0) :
    TlsWebSocketFrame.runByte fast cap
      ([0,0,0,0,255,255,0,op,fin,frag,hi,lo,mh,ml,0,0,cc,cv,u0,u1,u2,u3,u4,u5,u6,u7] ++ [255, 0]) =
      [255,255,0,0,0,0,0,0] ++ [0,0,0,0,255,255,0,op,fin,frag,(TlsWebSocketFrame.dec fast hi lo).1,
        (TlsWebSocketFrame.dec fast hi lo).2,(TlsWebSocketFrame.dec fast mh ml).1,
        (TlsWebSocketFrame.dec fast mh ml).2,0,0,cc,cv,u0,u1,u2,u3,u4,u5,u6,u7] := by
  rcases hop with rfl | rfl <;>
  · unfold TlsWebSocketFrame.runByte
    simp [TlsWebSocketFrame.readState, TlsWebSocketFrame.step, TlsWebSocketFrame.stateSelect,
      TlsWebSocketFrame.stateBytes, TlsWebSocketFrame.stateSize, TlsWebSocketFrame.control,
      TlsWebSocketFrame.dataKind, TlsWebSocketFrame.utfStep, TlsWebSocketUpgrade.get, either, any, member, choose, initial,
      ByteAuth.release, fast_and, fast_not, fast_const, fast_maskBit, select_zero', select_ones',
      eq_fast, hone, hzero]

open TlsWebSocketFrame (wordValue) in
theorem one_fast (hi lo : Byte) (h : 2 ≤ wordValue hi lo) : TlsWebSocketFrame.one fast hi lo = 0 := by
  unfold TlsWebSocketFrame.one
  rw [fast_and, eq_fast, eq_fast]
  by_cases a : hi = BitVec.ofNat 8 0
  · by_cases b : lo = BitVec.ofNat 8 1
    · subst a; subst b; exact absurd h (by decide)
    · rw [if_neg b]; simp
  · rw [if_neg a]; simp

open TlsWebSocketFrame (wordValue) in
theorem zero_fast (hi lo : Byte) (h : 1 ≤ wordValue hi lo) : TlsWebSocketFrame.zero fast hi lo = 0 := by
  unfold TlsWebSocketFrame.zero
  rw [fast_and, eq_fast, eq_fast]
  by_cases a : hi = BitVec.ofNat 8 0
  · by_cases b : lo = BitVec.ofNat 8 0
    · subst a; subst b; exact absurd h (by decide)
    · rw [if_neg b]; simp
  · rw [if_neg a]; simp

/-- The high and low byte of a 16-bit count. -/
def hiOf (v : Nat) : Byte := BitVec.ofNat 8 (v / 256)
def loOf (v : Nat) : Byte := BitVec.ofNat 8 (v % 256)

open TlsWebSocketFrame (wordValue) in
theorem wordValue_of (v : Nat) (h : v < 65536) : wordValue (hiOf v) (loOf v) = v := by
  unfold wordValue hiOf loOf
  simp only [BitVec.toNat_ofNat]
  omega

open TlsWebSocketFrame (wordValue) in
theorem wordValue_lt (hi lo : Byte) : wordValue hi lo < 65536 := by
  have := hi.isLt; have := lo.isLt
  unfold wordValue; omega

open TlsWebSocketFrame (wordValue) in
theorem dec_fast (hi lo : Byte) (h : 1 ≤ wordValue hi lo) :
    TlsWebSocketFrame.dec fast hi lo = (hiOf (wordValue hi lo - 1), loOf (wordValue hi lo - 1)) := by
  have hv := TlsWebSocketFrame.dec_value hi lo h
  rw [← fast_eq] at hv
  have h1 := (TlsWebSocketFrame.dec fast hi lo).1.isLt
  have h2 := (TlsWebSocketFrame.dec fast hi lo).2.isLt
  unfold wordValue at hv h ⊢
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq <;> simp only [hiOf, loOf, BitVec.toNat_ofNat] <;> omega

open TlsWebSocketFrame (wordValue)

/-- How many payload bytes the frame parser (its 26-byte state `f`) can be advanced over in one go:
it is in the payload phase of a valid, unclosed data frame (opcode 0 or 2) whose first two payload
bytes are behind it; at most all but the last payload byte of the frame (that one ends the frame)
and at most what is left of the message's capacity. 0 when the state has any other shape. -/
def frameRoom (f : List Byte) : Nat :=
  match f with
  | [p0, p1, p2, p3, p4, v, c, op, _, _, hi, lo, mh, ml, pf, ps, _, _, _, _, _, _, _, _, _, _] =>
    if p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 ∧ p4 = 255 ∧ v = 255 ∧ c = 0 ∧ (op = 0 ∨ op = 2) ∧ pf = 0 ∧ ps = 0
    then min (wordValue hi lo - 1) (wordValue mh ml) else 0
  | _ => 0

/-- The frame parser's state after `k` such payload bytes: both counts lowered by `k`. -/
def frameBulk (k : Nat) (f : List Byte) : List Byte :=
  match f with
  | [p0, p1, p2, p3, p4, v, c, op, fin, frag, hi, lo, mh, ml, pf, ps, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7] =>
    [p0, p1, p2, p3, p4, v, c, op, fin, frag, hiOf (wordValue hi lo - k), loOf (wordValue hi lo - k),
     hiOf (wordValue mh ml - k), loOf (wordValue mh ml - k), pf, ps, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7]
  | _ => f

theorem frame_shape {f : List Byte} (h : 1 ≤ frameRoom f) :
    ∃ op fin frag hi lo mh ml cc cv u0 u1 u2 u3 u4 u5 u6 u7,
      f = [0, 0, 0, 0, 255, 255, 0, op, fin, frag, hi, lo, mh, ml, 0, 0, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7] ∧
      (op = 0 ∨ op = 2) ∧ 2 ≤ wordValue hi lo ∧ 1 ≤ wordValue mh ml := by
  unfold frameRoom at h
  split at h
  · next p0 p1 p2 p3 p4 v c op fin frag hi lo mh ml pf ps cc cv u0 u1 u2 u3 u4 u5 u6 u7 =>
    split at h
    · next hc =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hop, rfl, rfl⟩ := hc
      exact ⟨op, fin, frag, hi, lo, mh, ml, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7, rfl, hop, by omega, by omega⟩
    · omega
  · omega

/-- **One passed-over payload byte, frame parser.** Fed an active zero byte, the frame parser
reports a valid data byte that ends nothing, and its new state is `frameBulk 1`. -/
theorem frame_step_room (cap : Nat) (f : List Byte) (h : 1 ≤ frameRoom f) :
    TlsWebSocketFrame.runByte fast cap (f ++ [255, 0]) = [255, 255, 0, 0, 0, 0, 0, 0] ++ frameBulk 1 f := by
  obtain ⟨op, fin, frag, hi, lo, mh, ml, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7, rfl, hop, h1, h2⟩ := frame_shape h
  rw [frame_step cap op fin frag hi lo mh ml cc cv u0 u1 u2 u3 u4 u5 u6 u7 hop (one_fast _ _ h1) (zero_fast _ _ h2),
    dec_fast _ _ (by omega), dec_fast _ _ h2]
  rfl

theorem frameRoom_one (f : List Byte) (h : 1 ≤ frameRoom f) : frameRoom (frameBulk 1 f) = frameRoom f - 1 := by
  obtain ⟨op, fin, frag, hi, lo, mh, ml, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7, rfl, hop, h1, h2⟩ := frame_shape h
  have w1 := wordValue_lt hi lo
  have w2 := wordValue_lt mh ml
  simp only [frameBulk, frameRoom, wordValue_of _ (show wordValue hi lo - 1 < 65536 by omega),
    wordValue_of _ (show wordValue mh ml - 1 < 65536 by omega)]
  rcases hop with rfl | rfl <;> simp <;> omega

theorem frameBulk_succ (f : List Byte) (k : Nat) (h : k + 1 ≤ frameRoom f) :
    frameBulk k (frameBulk 1 f) = frameBulk (k + 1) f := by
  obtain ⟨op, fin, frag, hi, lo, mh, ml, cc, cv, u0, u1, u2, u3, u4, u5, u6, u7, rfl, hop, h1, h2⟩ :=
    frame_shape (show 1 ≤ frameRoom f by omega)
  have w1 := wordValue_lt hi lo
  have w2 := wordValue_lt mh ml
  simp only [frameBulk, wordValue_of _ (show wordValue hi lo - 1 < 65536 by omega),
    wordValue_of _ (show wordValue mh ml - 1 < 65536 by omega), Nat.sub_sub, Nat.add_comm 1 k]

/-! ### The response parser -/

abbrev Word := BitVec 64
abbrev RState := TlsChatResponse.State Byte Word

theorem bytes_fast (w : Word) : Word64.bytes Word64.fast w =
    [Word64.fastUnpack w 0, Word64.fastUnpack w 1, Word64.fastUnpack w 2, Word64.fastUnpack w 3,
     Word64.fastUnpack w 4, Word64.fastUnpack w 5, Word64.fastUnpack w 6, Word64.fastUnpack w 7] := rfl

theorem pack_bytes (w : Word) : Word64.fast.pack (Word64.bytes Word64.fast w) = w := by
  rw [bytes_fast]
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  change (Word64.fastPack _).toNat = _
  simp only [Word64.fastPack, Word64.fastUnpack, BitVec.toNat_ofFin, Nat.shiftRight_eq_div_pow]
  omega

theorem pack_unpacks (w : Word) : Word64.fast.pack
    [Word64.fastUnpack w 0, Word64.fastUnpack w 1, Word64.fastUnpack w 2, Word64.fastUnpack w 3,
     Word64.fastUnpack w 4, Word64.fastUnpack w 5, Word64.fastUnpack w 6, Word64.fastUnpack w 7] = w :=
  pack_bytes w

theorem bytes_inj {x y : Word} (h : Word64.bytes Word64.fast x = Word64.bytes Word64.fast y) : x = y := by
  rw [← pack_bytes x, ← pack_bytes y, h]

theorem weq_fast (x : Word) (n : Nat) :
    TlsChatResponse.weq Word64.fast fast x n = if x = BitVec.ofNat 64 n then 255 else 0 := by
  unfold TlsChatResponse.weq Word64.eq
  rw [fast_eq, ByteAuth.equalMask_value]
  have hc : Word64.fast.const n = BitVec.ofNat 64 n := Word64.fastConst_eq n
  rw [hc]
  by_cases h : x = BitVec.ofNat 64 n
  · rw [if_pos (congrArg _ h), if_pos h]
  · rw [if_neg (fun e => h (bytes_inj e)), if_neg h]

theorem w_select : Word64.fast.select = Word64.fastSelect := rfl
theorem w_sub (x y : Word) : Word64.fast.sub x y = x - y := rfl
theorem w_const (n : Nat) : Word64.fast.const n = BitVec.ofNat 64 n := Word64.fastConst_eq n
theorem fastSelect_zero (x y : Word) : Word64.fastSelect 0#8 x y = y := by
  unfold Word64.fastSelect; simp
theorem fastSelect_ones (x y : Word) : Word64.fastSelect 255#8 x y = x := by
  unfold Word64.fastSelect; simp

theorem choose_zero : ∀ (yes no : List Byte), no.length ≤ yes.length → choose fast 0#8 yes no = no
  | _, [], _ => by simp [choose]
  | [], _ :: _, h => by simp at h
  | y :: ys, n :: ns, h => by
      have := choose_zero ys ns (by simp at h; omega)
      simp only [choose, List.zipWith_cons_cons] at this ⊢
      rw [select_zero', this]

theorem choose_ones : ∀ (yes no : List Byte), yes.length ≤ no.length → choose fast 255#8 yes no = yes
  | [], _, _ => by simp [choose]
  | _ :: _, [], h => by simp at h
  | y :: ys, n :: ns, h => by
      have := choose_ones ys ns (by simp at h; omega)
      simp only [choose, List.zipWith_cons_cons] at this ⊢
      rw [select_ones', this]

theorem zipWith_zero : ∀ (yes no : List Word), no.length ≤ yes.length →
    List.zipWith (Word64.fastSelect 0#8) yes no = no
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | y :: ys, n :: ns, h => by
      rw [List.zipWith_cons_cons, fastSelect_zero, zipWith_zero ys ns (by simp at h; omega)]

theorem writeStack_zero (index tag : Word) (stack : List Word) :
    TlsChatResponse.writeStack Word64.fast fast 0#8 index tag stack = stack := by
  unfold TlsChatResponse.writeStack
  simp [w_select, fastSelect_zero, fast_and]

theorem and_ones : ∀ x : Byte, x &&& 255#8 = x := by decide
theorem xor_ones_ones : ∀ x : Byte, x ^^^ 255#8 ^^^ 255#8 = x := by decide

theorem utfStep_length (s : List Byte) (x : Byte) : (TlsWebSocketFrame.utfStep fast s x).length = 8 := rfl

theorem len4 {α : Type} : ∀ (l : List α), l.length = 4 → ∃ a b c d, l = [a, b, c, d]
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem len8 {α : Type} : ∀ (l : List α), l.length = 8 → ∃ a b c d e f g i, l = [a, b, c, d, e, f, g, i]
  | [a, b, c, d, e, f, g, i], _ => ⟨a, b, c, d, e, f, g, i, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem len10 {α : Type} : ∀ (l : List α), l.length = 10 →
    ∃ a b c d e f g i j k, l = [a, b, c, d, e, f, g, i, j, k]
  | [a, b, c, d, e, f, g, i, j, k], _ => ⟨a, b, c, d, e, f, g, i, j, k, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h | [_, _, _, _, _, _, _, _], h
  | [_, _, _, _, _, _, _, _, _], h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem flat_length : ∀ (l : List Word), (l.flatMap (Word64.bytes Word64.fast)).length = 8 * l.length
  | [] => rfl
  | x :: xs => by
      rw [List.flatMap_cons, List.length_append, flat_length xs, Word64.bytes_length]
      simp only [List.length_cons]; omega

theorem flat_drop (R : List Byte) : ∀ (l : List Word) (i : Nat), i ≤ l.length →
    (l.flatMap (Word64.bytes Word64.fast) ++ R).drop (8 * i) = (l.drop i).flatMap (Word64.bytes Word64.fast) ++ R
  | _, 0, _ => rfl
  | [], _ + 1, h => by simp at h
  | x :: xs, i + 1, h => by
      have e : 8 * (i + 1) = 8 + 8 * i := by omega
      rw [e, List.flatMap_cons, List.append_assoc, ← List.drop_drop,
        List.drop_left' (Word64.bytes_length _ _), flat_drop R xs i (by simp at h; omega)]
      rfl

theorem stack_read (P Q : List Byte) (stack : List Word) (hP : P.length = 72) (hs : stack.length = 100) :
    (List.range 100).map (fun i => Word64.fast.pack
      (((P ++ (stack.flatMap (Word64.bytes Word64.fast) ++ Q)).drop (72 + 8 * i)).take 8)) = stack := by
  apply List.ext_getElem
  · simp [hs]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < stack.length := by omega
    rw [← hP, ← List.drop_drop, List.drop_left, flat_drop Q stack i (by omega),
      List.drop_eq_getElem_cons hi, List.flatMap_cons, List.append_assoc,
      List.take_left' (Word64.bytes_length _ _), pack_bytes]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The response parser's state survives its serialisation: `readState` undoes `stateBytes`. -/
theorem readState_stateBytes (S : RState) (hm : S.modes.length = 4) (hp : S.positions.length = 10)
    (hk : S.kinds.length = 4) (hst : S.stack.length = 100) (hu : S.utf.length = 8) :
    TlsChatResponse.readState Word64.fast fast (TlsChatResponse.stateBytes Word64.fast S) = S := by
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := header
  simp only at hm hp hk hst hu
  obtain ⟨m0, m1, m2, m3, rfl⟩ := len4 modes hm
  obtain ⟨k0, k1, k2, k3, rfl⟩ := len4 kinds hk
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, rfl⟩ := len10 positions hp
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, rfl⟩ := len8 utf hu
  have split : TlsChatResponse.stateBytes Word64.fast ⟨valid, seen, finished, successful, [m0, m1, m2, m3],
      [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9], value, tag, scalarKnown, [k0, k1, k2, k3], inner,
      responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
      id, expected, status, bodyPresent, bodyLength, messagePresent, [u0, u1, u2, u3, u4, u5, u6, u7],
      ⟨h0, h1, h2, h3, h4, h5, h6⟩⟩ =
      ([valid, seen, finished, successful, m0, m1, m2, m3, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] ++
        Word64.bytes Word64.fast value ++ Word64.bytes Word64.fast tag ++ [scalarKnown, k0, k1, k2, k3, inner] ++
        Word64.bytes Word64.fast responseRemaining ++ Word64.bytes Word64.fast budget ++
        Word64.bytes Word64.fast skip ++ Word64.bytes Word64.fast depth) ++
      (stack.flatMap (Word64.bytes Word64.fast) ++
        (Word64.bytes Word64.fast typeValue ++ [requestPresent, responsePresent, idPresent] ++
          Word64.bytes Word64.fast id ++ Word64.bytes Word64.fast expected ++ Word64.bytes Word64.fast status ++
          [bodyPresent] ++ Word64.bytes Word64.fast bodyLength ++ [messagePresent, u0, u1, u2, u3, u4, u5, u6, u7,
          h0, h1, h2, h3, h4, h5, h6])) := by
    simp [TlsChatResponse.stateBytes, TlsChatResponse.headerBytes]
  rw [split]
  unfold TlsChatResponse.readState
  rw [stack_read _ _ stack (by simp [bytes_fast]) hst]
  have hF : (stack.flatMap (Word64.bytes Word64.fast)).length = 800 := by rw [flat_length, hst]
  simp only [bytes_fast, List.cons_append, List.nil_append, TlsWebSocketUpgrade.get,
    TlsChatResponse.readHeader, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
  simp only [List.drop_append, hF, List.drop_eq_nil_of_le, List.nil_append, List.drop_succ_cons, List.drop_zero,
    pack_unpacks, Nat.le_refl]
  simp only [Nat.sub_self, List.drop_zero, List.take_succ_cons, List.take_zero, pack_unpacks]
  have hD : ∀ n, 800 ≤ n → (stack.flatMap (Word64.bytes Word64.fast)).drop n = [] :=
    fun n h => List.drop_eq_nil_of_le (by rw [hF]; exact h)
  simp [hF, hD, pack_unpacks]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- One byte of an unrevealed response body, at the parser's state level: the parser is inside a
length-delimited field of the inner response (`modes` = bytes, `kinds` = body), so it only counts. -/
theorem response_process (cap : Nat) (S : RState)
    (hv : S.valid = 255) (hs : S.seen = 255) (hf : S.finished = 0) (hm : S.modes = [0,0,0,255])
    (hk : S.kinds = [0,255,0,0]) (hi : S.inner = 255)
    (hskip : TlsChatResponse.weq Word64.fast fast S.skip 1 = 0)
    (hbudget : TlsChatResponse.weq Word64.fast fast S.budget 0 = 0)
    (hrem : TlsChatResponse.weq Word64.fast fast S.responseRemaining 1 = 0)
    (hp : S.positions.length = 10) (hst : S.stack.length = 100) (hu : S.utf.length = 8) :
    TlsChatResponse.process VarintDecode.Spqr.concrete Word64.fast fast cap S 255 0 0 0 =
      ⟨{S with skip := S.skip - 1, budget := S.budget - 1, responseRemaining := S.responseRemaining - 1},
        255, 0, 0⟩ := by
  obtain ⟨valid, seen, finished, successful, modes, positions, value, tag, scalarKnown, kinds, inner,
    responseRemaining, budget, skip, depth, stack, typeValue, requestPresent, responsePresent, idPresent,
    id, expected, status, bodyPresent, bodyLength, messagePresent, utf, header⟩ := S
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := header
  simp only at hv hs hf hm hk hi hskip hbudget hrem hp hst hu
  subst hv hs hf hm hk hi
  simp [TlsChatResponse.process, TlsChatResponse.step, TlsChatResponse.stateSelect,
    TlsChatResponse.initial, TlsChatResponse.headerSelect, TlsChatResponse.headerInitial,
    TlsChatResponse.finish, TlsWebSocketUpgrade.get, either, any, choose_zero, choose_ones, initial,
    fast_and, fast_not, fast_const, fast_maskBit, select_zero', select_ones', eq_fast,
    w_select, w_sub, w_const, fastSelect_zero, fastSelect_ones, zipWith_zero,
    writeStack_zero, utfStep_length, and_ones, xor_ones_ones, hskip, hbudget, hrem, hp, hst, hu]

theorem stateBytes_length (S : RState) (hm : S.modes.length = 4) (hp : S.positions.length = 10)
    (hk : S.kinds.length = 4) (hst : S.stack.length = 100) (hu : S.utf.length = 8) :
    (TlsChatResponse.stateBytes Word64.fast S).length = 932 := by
  simp only [TlsChatResponse.stateBytes, TlsChatResponse.headerBytes, List.length_append, List.length_cons,
    List.length_nil, flat_length, Word64.bytes_length, hm, hp, hk, hst, hu]

/-- The response parser's state is inside the body of the inner response: valid, started, not
finished, reading the bytes of a length-delimited field (`modes`) that is the body (`kinds`), with
lists of their usual lengths. -/
def responseFits (S : RState) : Prop :=
  S.valid = 255 ∧ S.seen = 255 ∧ S.finished = 0 ∧ S.modes = [0, 0, 0, 255] ∧ S.kinds = [0, 255, 0, 0] ∧
    S.inner = 255 ∧ S.positions.length = 10 ∧ S.stack.length = 100 ∧ S.utf.length = 8

instance : DecidablePred responseFits := fun S => by unfold responseFits; infer_instance

/-- How many body bytes the response parser (its 932-byte state `r`) can be advanced over in one go:
`r` is the serialisation of a state that `responseFits`; at most all but the last byte of the body
field, all but the last byte of the inner response, and what is left of the parser's budget. -/
def responseRoom (r : List Byte) : Nat :=
  let S := TlsChatResponse.readState Word64.fast fast r
  if r.length = 932 ∧ TlsChatResponse.stateBytes Word64.fast S = r ∧ responseFits S then
    min (S.skip.toNat - 1) (min S.budget.toNat (S.responseRemaining.toNat - 1))
  else 0

/-- The response parser's state after `k` body bytes: three counts lowered by `k`. -/
def responseAdvance (k : Nat) (S : RState) : RState :=
  { S with skip := BitVec.ofNat 64 (S.skip.toNat - k), budget := BitVec.ofNat 64 (S.budget.toNat - k),
           responseRemaining := BitVec.ofNat 64 (S.responseRemaining.toNat - k) }

def responseBulk (k : Nat) (r : List Byte) : List Byte :=
  TlsChatResponse.stateBytes Word64.fast (responseAdvance k (TlsChatResponse.readState Word64.fast fast r))

theorem response_shape {r : List Byte} (h : 1 ≤ responseRoom r) :
    r.length = 932 ∧ TlsChatResponse.stateBytes Word64.fast (TlsChatResponse.readState Word64.fast fast r) = r ∧
      responseFits (TlsChatResponse.readState Word64.fast fast r) ∧
      responseRoom r = min ((TlsChatResponse.readState Word64.fast fast r).skip.toNat - 1)
        (min (TlsChatResponse.readState Word64.fast fast r).budget.toNat
          ((TlsChatResponse.readState Word64.fast fast r).responseRemaining.toNat - 1)) := by
  unfold responseRoom at h ⊢
  dsimp only at h ⊢
  split at h
  · next hc => exact ⟨hc.1, hc.2.1, hc.2.2, if_pos hc⟩
  · omega

theorem sub_one_word (x : Word) (h : 1 ≤ x.toNat) : x - 1 = BitVec.ofNat 64 (x.toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  have h1 : (1 : Word).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem weq_ne (x : Word) (n : Nat) (h : x.toNat ≠ n) (hn : n < 2 ^ 64) :
    TlsChatResponse.weq Word64.fast fast x n = 0 := by
  rw [weq_fast, if_neg]
  intro e
  apply h
  rw [e, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hn

/-- **One passed-over body byte, response parser.** Fed an active zero byte that neither starts nor
ends a message, the parser stays valid, does not finish, reports a body byte, and its new state is
`responseBulk 1`. -/
theorem response_step_room (cap : Nat) (r : List Byte) (h : 1 ≤ responseRoom r) :
    TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast cap (r ++ [255, 0, 0] ++ [0]) =
      [255, 0, (TlsChatResponse.readState Word64.fast fast r).successful, 255, 0, 0] ++ responseBulk 1 r := by
  obtain ⟨hlen, _, ⟨hv, hs, hf, hm, hk, hi, hp, hst, hu⟩, hroom⟩ := response_shape h
  have hskip : (TlsChatResponse.readState Word64.fast fast r).skip.toNat ≠ 1 := by omega
  have hbudget : (TlsChatResponse.readState Word64.fast fast r).budget.toNat ≠ 0 := by omega
  have hrem : (TlsChatResponse.readState Word64.fast fast r).responseRemaining.toNat ≠ 1 := by omega
  unfold TlsChatResponse.runByte
  have ht : (r ++ [255, 0, 0] ++ [0]).take TlsChatResponse.stateSize = r := by
    rw [List.append_assoc]; exact List.take_left' hlen
  have g : ∀ i, TlsWebSocketUpgrade.get fast (r ++ [255, 0, 0] ++ [0]) (TlsChatResponse.stateSize + i) =
      [255, 0, 0, 0].getD i (fast.const 0) := by
    intro i
    simp only [TlsWebSocketUpgrade.get, TlsChatResponse.stateSize, List.append_assoc, List.cons_append,
      List.nil_append, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  have g0 := g 0
  rw [Nat.add_zero] at g0
  rw [ht, g0, g 1, g 2, g 3]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [response_process cap _ hv hs hf hm hk hi (weq_ne _ _ hskip (by decide)) (weq_ne _ _ hbudget (by decide))
    (weq_ne _ _ hrem (by decide)) hp hst hu]
  have e : { TlsChatResponse.readState Word64.fast fast r with
      skip := (TlsChatResponse.readState Word64.fast fast r).skip - 1,
      budget := (TlsChatResponse.readState Word64.fast fast r).budget - 1,
      responseRemaining := (TlsChatResponse.readState Word64.fast fast r).responseRemaining - 1 } =
      responseAdvance 1 (TlsChatResponse.readState Word64.fast fast r) := by
    rw [sub_one_word _ (by omega), sub_one_word _ (by omega), sub_one_word _ (by omega)]
    rfl
  rw [e]
  dsimp only
  rw [responseBulk]
  simp only [responseAdvance, hv, hf]

theorem ofNat_toNat_sub (x : Word) (k : Nat) : (BitVec.ofNat 64 (x.toNat - k)).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- After advancing, the state still has the right shape: reading back its bytes gives it. -/
theorem response_advance_shape {r : List Byte} (h : 1 ≤ responseRoom r) (k : Nat) :
    TlsChatResponse.readState Word64.fast fast (responseBulk k r) =
        responseAdvance k (TlsChatResponse.readState Word64.fast fast r) ∧
      (responseBulk k r).length = 932 ∧
      responseFits (responseAdvance k (TlsChatResponse.readState Word64.fast fast r)) := by
  obtain ⟨_, _, ⟨hv, hs, hf, hm, hk, hi, hp, hst, hu⟩, _⟩ := response_shape h
  have hm4 : (responseAdvance k (TlsChatResponse.readState Word64.fast fast r)).modes.length = 4 := by
    simp [responseAdvance, hm]
  have hk4 : (responseAdvance k (TlsChatResponse.readState Word64.fast fast r)).kinds.length = 4 := by
    simp [responseAdvance, hk]
  exact ⟨readState_stateBytes _ hm4 hp hk4 hst hu, stateBytes_length _ hm4 hp hk4 hst hu,
    hv, hs, hf, hm, hk, hi, hp, hst, hu⟩

theorem responseRoom_one (r : List Byte) (h : 1 ≤ responseRoom r) :
    responseRoom (responseBulk 1 r) = responseRoom r - 1 := by
  obtain ⟨rt, len, fits⟩ := response_advance_shape h 1
  have hroom := (response_shape h).2.2.2
  have hc : (responseBulk 1 r).length = 932 ∧
      TlsChatResponse.stateBytes Word64.fast (TlsChatResponse.readState Word64.fast fast (responseBulk 1 r)) =
        responseBulk 1 r ∧ responseFits (TlsChatResponse.readState Word64.fast fast (responseBulk 1 r)) := by
    rw [rt]; exact ⟨len, rfl, fits⟩
  rw [hroom]
  unfold responseRoom
  dsimp only
  rw [if_pos hc, rt]
  simp only [responseAdvance, ofNat_toNat_sub]
  omega

theorem responseBulk_succ (r : List Byte) (k : Nat) (h : k + 1 ≤ responseRoom r) :
    responseBulk k (responseBulk 1 r) = responseBulk (k + 1) r := by
  have h1 : 1 ≤ responseRoom r := by omega
  obtain ⟨rt, _, _⟩ := response_advance_shape h1 1
  rw [responseBulk, rt, responseBulk]
  simp only [responseAdvance, ofNat_toNat_sub, Nat.sub_sub, Nat.add_comm 1 k]

/-! ### The control queue -/

theorem member_range (x : Byte) : ∀ n, n ≤ 256 → member fast x (List.range n) = if x.toNat < n then 255 else 0
  | 0, _ => by simp [member, any, fast_const]
  | n + 1, h => by
      have ih := member_range x n (by omega)
      unfold member any at ih ⊢
      rw [List.range_succ, List.map_append, List.foldl_append, ih]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, either, fast_not, fast_and, eq_fast]
      have hx := x.isLt
      by_cases a : x.toNat < n
      · have a' : x.toNat < n + 1 := by omega
        by_cases b : x = BitVec.ofNat 8 n
        · simp only [if_pos a, if_pos a', if_pos b]; decide
        · simp only [if_pos a, if_pos a', if_neg b]; decide
      · by_cases b : x = BitVec.ofNat 8 n
        · have a' : x.toNat < n + 1 := by rw [b, BitVec.toNat_ofNat]; omega
          simp only [if_neg a, if_pos a', if_pos b]; decide
        · have a' : ¬ x.toNat < n + 1 := by
            intro c
            apply b
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat]
            omega
          simp only [if_neg a, if_neg a', if_neg b]; decide

theorem map_range_get (l : List Byte) (n : Nat) (h : l.length = n) :
    (List.range n).map (fun i => get fast l i) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [TlsWebSocketUpgrade.get, List.getElem?_eq_getElem h2]

/-- The control queue's step with no control data, no frame end, no opcode (and a zero byte) leaves
its state as it is, when the payload count is below 126 and the queue length below 5. -/
theorem control_step_idle (S : TlsWebSocketControl.State Byte) (hd : S.data.length = 125)
    (hk : S.kinds.length = 4) (hl : S.lengths.length = 4) (hp : S.payloads.length = 500)
    (hc : S.count.toNat < 126) (hq : S.queued.toNat < 5) :
    TlsWebSocketControl.step fast S 0 0 0 0 = S := by
  obtain ⟨valid, count, data, queued, kinds, lengths, payloads⟩ := S
  simp only at hd hk hl hp hc hq
  have mc : member fast count (List.range 126) = 255 := by rw [member_range _ _ (by decide), if_pos hc]
  have mq : member fast queued (List.range 5) = 255 := by rw [member_range _ _ (by decide), if_pos hq]
  have m0 : member fast 0#8 [0, 255] = 255 := by decide
  simp [TlsWebSocketControl.step, mc, mq, m0, fast_and, fast_not, fast_const, eq_fast, select_zero',
    choose_zero, map_range_get, hd, hk, hl, hp, and_ones]

theorem take_merge (c : List Byte) (k m n k2 t : Nat) (h1 : k + m = k2) (h2 : m + n = t) :
    (c.drop k).take m ++ (c.drop k2).take n = (c.drop k).take t := by
  subst h1 h2
  rw [List.take_add, List.drop_drop]

theorem singleton_get (c : List Byte) (i : Nat) (h : i < c.length) : [get fast c i] = (c.drop i).take 1 := by
  rw [List.drop_eq_getElem_cons h]
  simp only [TlsWebSocketUpgrade.get, List.getElem?_eq_getElem h, Option.getD_some, List.take_succ_cons,
    List.take_zero]

/-- The control queue's state survives its serialisation. -/
theorem control_reassemble (c : List Byte) (hlen : c.length = 636) :
    TlsWebSocketControl.stateBytes (TlsWebSocketControl.readState fast c) = c := by
  have e : TlsWebSocketControl.stateBytes (TlsWebSocketControl.readState fast c) =
      [get fast c 0] ++ [get fast c 1] ++ (c.drop 2).take 125 ++ [get fast c 127] ++ (c.drop 128).take 4 ++
        (c.drop 132).take 4 ++ (c.drop 136).take 500 := by
    simp [TlsWebSocketControl.stateBytes, TlsWebSocketControl.readState]
  rw [e, singleton_get c 0 (by omega), singleton_get c 1 (by omega), singleton_get c 127 (by omega),
    take_merge c 0 1 1 1 2 rfl rfl, take_merge c 0 2 125 2 127 rfl rfl, take_merge c 0 127 1 127 128 rfl rfl,
    take_merge c 0 128 4 128 132 rfl rfl, take_merge c 0 132 4 132 136 rfl rfl,
    take_merge c 0 136 500 136 636 rfl rfl, List.drop_zero, List.take_of_length_le (by omega)]

/-- The control queue's 636-byte state has its payload count below 126 and its queue length below 5:
then a byte with no control data, no frame end and no opcode leaves it unchanged (`control_idle`). -/
def controlIdle (c : List Byte) : Prop :=
  c.length = 636 ∧ (get fast c 1).toNat < 126 ∧ (get fast c 127).toNat < 5

instance : DecidablePred controlIdle := fun c => by unfold controlIdle; infer_instance

/-- **One passed-over payload byte, control queue.** With no control data, no frame end and no
opcode (what the frame parser reports for a data payload byte), the queue's step is the identity on
its 636-byte state, provided its counts are in range (payload count below 126, queue length below 5;
otherwise the step would mark the state invalid). -/
theorem control_idle (c : List Byte) (h : controlIdle c) :
    TlsWebSocketControl.run fast (c ++ [0, 0, 0, 0]) = c := by
  obtain ⟨hlen, hcount, hqueued⟩ := h
  unfold TlsWebSocketControl.run
  rw [List.take_left' hlen]
  have g : ∀ i, i < 4 → get fast (c ++ [0, 0, 0, 0]) (636 + i) = [0, 0, 0, 0][i]?.getD 0 := by
    intro i hi
    simp only [TlsWebSocketUpgrade.get]
    rw [List.getElem?_append_right (by omega), show 636 + i - c.length = i by omega, fast_const]
    rfl
  have g0 := g 0 (by decide)
  have g1 := g 1 (by decide)
  have g2 := g 2 (by decide)
  have g3 := g 3 (by decide)
  simp only [Nat.add_zero] at g0
  simp only [Nat.reduceAdd] at g1 g2 g3
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at g0 g1 g2 g3
  rw [g0, g1, g2, g3, control_step_idle _ (by simp [TlsWebSocketControl.readState, hlen])
    (by simp [TlsWebSocketControl.readState, hlen]) (by simp [TlsWebSocketControl.readState, hlen])
    (by simp [TlsWebSocketControl.readState, hlen]) hcount hqueued]
  exact control_reassemble c hlen

end PublicReceive.PassOver
