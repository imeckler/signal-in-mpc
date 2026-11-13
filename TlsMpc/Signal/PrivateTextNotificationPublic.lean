import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.Signal.PrivateTextNotificationSizedSemantics

/-! # The public text's built message, computed directly (the notify path)

`PrivateTextNotification.buildPublic` / `buildPublicOfficial` evaluate the circuit's own
definition (`buildPadded`) on the concrete byte operations: every private-length append is a
masked shift of the whole buffer, every UTF-8 step compares the byte with up to 128 constants
through `ByteAuth.eqMask` (eight `BitVec.replicate` each), and every class tried rebuilds the
message. On the notify path the text is public, so the controllers can compute the same bytes
directly: the Content's protobuf bytes (`contentBytesSized`), the 0x80 terminator and zeros, and the
UTF-8 automaton with its range tests on the byte's value.

`buildPublicFast` / `buildPublicOfficialFast` are PROVED equal to the definitions
(`buildPublicFast_eq`, `buildPublicOfficialFast_eq`), which stay the specification and are what the
private path compiles; the controllers call the fast functions by name (no `csimp`). Each step is
one of the semantics theorems already proved about the circuit (`fromWire_decoded`,
`contentSized_contents`, `iso7816_sized_contents`), plus the overflow case of the padding (the
class is too small: the padded buffer is the zero buffer, `join_terminator_overflow`) and the UTF-8
loop on the values of its masks (`utfLoop_public`, `utfStep_fast`). Inputs outside the proved
shape (a text longer than its capacity, a timestamp not of eight bytes, a padded size of zero or
at least 65536, no canonical varint width) take the definition itself, so the equality holds for
every input. Not in any emitter's import closure (only `Session/Send` imports it). -/

namespace TlsMpc.Signal.PrivateTextNotification
open PrivateBuffer PrivateProtobuf

/-! ### The padding when the Content does not fit the class -/

theorem resize_contents_overflow (capacity sourceCapacity : Nat) (hc : capacity < 65536)
    (raw : List (BitVec 8)) (over : capacity < raw.length) (bounded : raw.length < 65536) :
    resize ByteAuth.concrete capacity (ofContents sourceCapacity raw) = zero ByteAuth.concrete capacity := by
  have made : make ByteAuth.concrete capacity (ofContents sourceCapacity raw).lengthBits
      ((List.range capacity).map (OpenResult.get ByteAuth.concrete (ofContents sourceCapacity raw).data)) =
      zero ByteAuth.concrete capacity := by
    have h := make_decoded capacity hc (BitVec.ofNat 8 (raw.length / 256)) (BitVec.ofNat 8 raw.length)
      ((List.range capacity).map (OpenResult.get ByteAuth.concrete (ofContents sourceCapacity raw).data))
      (by simp)
    rw [public_length_value raw.length bounded, if_neg (by omega)] at h
    exact h
  unfold resize
  rw [made]
  change finish ByteAuth.concrete ((0 : BitVec 8) &&& _) _ _ = _
  rw [zero_and_literal]
  exact finish_reject capacity _ _ (zero_bits_length capacity) (zero_data_length capacity)

theorem append_resize_reject_right (capacity : Nat) (left right : Buffer (BitVec 8))
    (hr : resize ByteAuth.concrete capacity right = zero ByteAuth.concrete capacity) :
    append ByteAuth.concrete capacity left right = zero ByteAuth.concrete capacity := by
  unfold append
  rw [hr]
  change finish ByteAuth.concrete (_ &&& ((0 : BitVec 8) &&& _)) _ _ = _
  rw [zero_and_literal, and_zero_literal]
  apply finish_reject
  · simpa only [List.length_range] using addLoop_length ByteAuth.concrete _ _ (List.range 16) (ByteAuth.concrete.const 0)
  · simp only [List.length_map, List.length_range]

theorem append_contents_overflow (capacity leftCapacity rightCapacity : Nat) (hc : capacity < 65536)
    (left right : List (BitVec 8)) (hl : left.length ≤ capacity) (hr : right.length ≤ capacity)
    (over : capacity < left.length + right.length) :
    append ByteAuth.concrete capacity (ofContents leftCapacity left) (ofContents rightCapacity right) =
      zero ByteAuth.concrete capacity := by
  have resized : append ByteAuth.concrete capacity (ofContents leftCapacity left) (ofContents rightCapacity right) =
      append ByteAuth.concrete capacity (ofContents capacity left) (ofContents capacity right) := by
    unfold append
    rw [resize_contents capacity leftCapacity hc left hl, resize_contents capacity rightCapacity hc right hr,
      resize_contents capacity capacity hc left hl, resize_contents capacity capacity hc right hr]
  rw [resized]
  have leftEq : ofContents capacity left =
      ⟨255, publicLength ByteAuth.concrete left.length, prefixData ByteAuth.concrete capacity left.length left⟩ := by
    unfold ofContents
    rw [prefix_contents capacity left hl]
  have rightEq : ofContents capacity right =
      ⟨255, publicLength ByteAuth.concrete right.length, prefixData ByteAuth.concrete capacity right.length right⟩ := by
    unfold ofContents
    rw [prefix_contents capacity right hr]
  rw [leftEq, rightEq]
  have result := append_decoded capacity hc
    (BitVec.ofNat 8 (left.length / 256)) (BitVec.ofNat 8 left.length)
    (BitVec.ofNat 8 (right.length / 256)) (BitVec.ofNat 8 right.length) left right
    (by rw [public_length_value left.length (by omega)]; exact hl)
    (by rw [public_length_value right.length (by omega)]; exact hr)
  rw [public_length_value left.length (by omega), public_length_value right.length (by omega),
    if_neg (by omega)] at result
  exact result

/-- The padding of a Content that does not leave room for its terminator: the zero buffer. -/
theorem join_terminator_overflow (size sourceCapacity : Nat) (hc : size < 65536) (positive : 0 < size)
    (content : List (BitVec 8)) (over : size ≤ content.length) (bounded : content.length < 65536) :
    PrivateSend.join ByteAuth.concrete size [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete size [128]] = zero ByteAuth.concrete size := by
  unfold PrivateSend.join PrivateSend.literal
  simp only [List.foldl_cons, List.foldl_nil]
  rw [fromPublic_contents size hc [] (by simp)]
  by_cases same : content.length = size
  · rw [append_contents size size sourceCapacity hc [] content (by simp only [List.length_nil]; omega)]
    simp only [List.nil_append]
    rw [fromPublic_contents size hc [128] (by simp only [List.length_cons, List.length_nil]; omega)]
    exact append_contents_overflow size size size hc content [128] (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega) (by simp only [List.length_cons, List.length_nil]; omega)
  · rw [append_resize_reject_right size _ _
      (resize_contents_overflow size sourceCapacity hc content (by omega) bounded)]
    exact append_zero_left size _

/-! ### The UTF-8 automaton on the values of its masks -/

theorem either_full (acc : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete acc 255 = 255 := by
  show ~~~(~~~acc &&& ~~~(255 : BitVec 8)) = 255
  rw [show ~~~(255 : BitVec 8) = 0 from by decide, and_zero_literal]
  decide

theorem either_empty (acc : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete acc 0 = acc := by
  show ~~~(~~~acc &&& ~~~(0 : BitVec 8)) = acc
  rw [show ~~~(0 : BitVec 8) = BitVec.allOnes 8 from by decide, BitVec.and_allOnes, BitVec.not_not]

theorem eq_value (x : BitVec 8) (n : Nat) :
    TlsWebSocketUpgrade.eq ByteAuth.concrete x n = if x = BitVec.ofNat 8 n then 255 else 0 :=
  ByteAuth.eqMask_value x (BitVec.ofNat 8 n)

theorem any_masks (x : BitVec 8) (ns : List Nat) (acc : BitVec 8) :
    (ns.map (TlsWebSocketUpgrade.eq ByteAuth.concrete x)).foldl (TlsWebSocketUpgrade.either ByteAuth.concrete) acc =
      if ∃ n ∈ ns, x = BitVec.ofNat 8 n then 255 else acc := by
  induction ns generalizing acc with
  | nil => simp
  | cons n ns ih =>
    rw [List.map_cons, List.foldl_cons, ih, eq_value]
    by_cases h : x = BitVec.ofNat 8 n
    · rw [if_pos h, either_full, ite_self, if_pos ⟨n, by simp, h⟩]
    · rw [if_neg h, either_empty]
      have same : (∃ m ∈ n :: ns, x = BitVec.ofNat 8 m) ↔ (∃ m ∈ ns, x = BitVec.ofNat 8 m) := by
        constructor
        · rintro ⟨m, hm, hx⟩
          rcases List.mem_cons.mp hm with hm | hm
          · exact absurd (hm ▸ hx) h
          · exact ⟨m, hm, hx⟩
        · rintro ⟨m, hm, hx⟩
          exact ⟨m, List.mem_cons_of_mem n hm, hx⟩
      by_cases e : ∃ m ∈ ns, x = BitVec.ofNat 8 m
      · rw [if_pos e, if_pos (same.mpr e)]
      · rw [if_neg e, if_neg (fun h' => e (same.mp h'))]

theorem member_value (x : BitVec 8) (ns : List Nat) :
    TlsWebSocketUpgrade.member ByteAuth.concrete x ns = if ∃ n ∈ ns, x = BitVec.ofNat 8 n then 255 else 0 :=
  any_masks x ns (ByteAuth.concrete.const 0)

/-- A range test on the byte's value: 255 if `low ≤ x < low + count`, else 0. -/
def rangeMask (x : BitVec 8) (low count : Nat) : BitVec 8 :=
  if low ≤ x.toNat ∧ x.toNat < low + count then 255 else 0

theorem member_range (x : BitVec 8) (low count : Nat) (bound : low + count ≤ 256) :
    TlsWebSocketUpgrade.member ByteAuth.concrete x ((List.range count).map (· + low)) = rangeMask x low count := by
  rw [member_value]
  unfold rangeMask
  have iff : (∃ n ∈ (List.range count).map (· + low), x = BitVec.ofNat 8 n) ↔
      (low ≤ x.toNat ∧ x.toNat < low + count) := by
    constructor
    · rintro ⟨n, hn, hx⟩
      simp only [List.mem_map, List.mem_range] at hn
      obtain ⟨m, hm, hmn⟩ := hn
      have hv : x.toNat = n := by
        rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨x.toNat, ?_, ?_⟩
      · simp only [List.mem_map, List.mem_range]
        exact ⟨x.toNat - low, by omega, by omega⟩
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  by_cases h : low ≤ x.toNat ∧ x.toNat < low + count
  · rw [if_pos (iff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (iff.mp h')), if_neg h]

/-- `TlsWebSocketFrame.utfStep` on the concrete operations, its range and equality tests computed
from the byte's value (`utfStep_fast`). -/
def utfStepFast (state : List (BitVec 8)) (x : BitVec 8) : List (BitVec 8) :=
  let a := ByteAuth.concrete
  let p := fun i => TlsWebSocketUpgrade.get a state i
  let range := fun low count => rangeMask x low count
  let eq := fun n => if x = BitVec.ofNat 8 n then (255 : BitVec 8) else 0
  let either := TlsWebSocketUpgrade.either a
  let continuation := range 128 64
  [either (a.and (p 0) (range 0 128)) (a.and (p 1) continuation),
   either (a.and (p 0) (range 194 30))
     (either (a.and (p 2) continuation)
       (either (a.and (p 4) (range 160 32)) (a.and (p 5) (range 128 32)))),
   either (a.and (p 0) (either (range 225 12) (range 238 2)))
     (either (a.and (p 3) continuation)
       (either (a.and (p 6) (range 144 48)) (a.and (p 7) (range 128 16)))),
   a.and (p 0) (range 241 3), a.and (p 0) (eq 224), a.and (p 0) (eq 237),
   a.and (p 0) (eq 240), a.and (p 0) (eq 244)]

theorem utfStep_fast (state : List (BitVec 8)) (x : BitVec 8) :
    TlsWebSocketFrame.utfStep ByteAuth.concrete state x = utfStepFast state x := by
  simp only [TlsWebSocketFrame.utfStep, utfStepFast, eq_value,
    member_range x 0 128 (by decide), member_range x 128 64 (by decide),
    member_range x 194 30 (by decide), member_range x 160 32 (by decide),
    member_range x 128 32 (by decide), member_range x 225 12 (by decide),
    member_range x 238 2 (by decide), member_range x 144 48 (by decide),
    member_range x 128 16 (by decide), member_range x 241 3 (by decide)]

theorem utfStepFast_length (state : List (BitVec 8)) (x : BitVec 8) : (utfStepFast state x).length = 8 := rfl

/-- `utfLoop` with the public length `n`: the bytes below `n` step the automaton, the others
leave it unchanged (`utfLoop_public`). -/
def utfLoopFast (data : List (BitVec 8)) (n : Nat) : List Nat → List (BitVec 8) → List (BitVec 8)
  | [], state => state
  | i :: rest, state =>
    utfLoopFast data n rest (if i < n then utfStepFast state (OpenResult.get ByteAuth.concrete data i) else state)

theorem select_full (yes no : BitVec 8) : TlsInner.select ByteAuth.concrete 255 yes no = yes := by
  show ((255 : BitVec 8) &&& (yes ^^^ no)) ^^^ no = yes
  rw [and_full_literal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem select_empty (yes no : BitVec 8) : TlsInner.select ByteAuth.concrete 0 yes no = no := by
  show ((0 : BitVec 8) &&& (yes ^^^ no)) ^^^ no = no
  rw [zero_and_literal]
  exact BitVec.zero_xor

theorem choose_full (yes no : List (BitVec 8)) (h : yes.length = no.length) :
    TlsWebSocketUpgrade.choose ByteAuth.concrete 255 yes no = yes := by
  induction yes generalizing no with
  | nil => rfl
  | cons y ys ih =>
    cases no with
    | nil => simp at h
    | cons n ns =>
      have rest := ih ns (by simpa using h)
      simp only [TlsWebSocketUpgrade.choose, List.zipWith_cons_cons] at rest ⊢
      rw [rest, select_full]

theorem choose_empty (yes no : List (BitVec 8)) (h : yes.length = no.length) :
    TlsWebSocketUpgrade.choose ByteAuth.concrete 0 yes no = no := by
  induction yes generalizing no with
  | nil =>
    cases no with
    | nil => rfl
    | cons n ns => simp at h
  | cons y ys ih =>
    cases no with
    | nil => simp at h
    | cons n ns =>
      have rest := ih ns (by simpa using h)
      simp only [TlsWebSocketUpgrade.choose, List.zipWith_cons_cons] at rest ⊢
      rw [rest, select_empty]

theorem utfLoop_public (data : List (BitVec 8)) (n : Nat) (hn : n < 65536) (indices : List Nat)
    (bounded : ∀ i ∈ indices, i < 65536) (state : List (BitVec 8)) (hs : state.length = 8) :
    utfLoop ByteAuth.concrete data (publicLength ByteAuth.concrete n) indices state =
      utfLoopFast data n indices state := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    have hi : i < 65536 := bounded i (List.mem_cons_self ..)
    have tail : ∀ j ∈ rest, j < 65536 := fun j hj => bounded j (List.mem_cons_of_mem i hj)
    have active : less ByteAuth.concrete (publicLength ByteAuth.concrete i) (publicLength ByteAuth.concrete n) =
        if i < n then 255 else 0 := by
      have h := public_less_decoded i hi (BitVec.ofNat 8 (n / 256)) (BitVec.ofNat 8 n)
      rw [public_length_value n hn] at h
      exact h
    simp only [utfLoop, utfLoopFast]
    rw [active, utfStep_fast]
    by_cases h : i < n
    · rw [if_pos h, if_pos h, choose_full _ _ (by rw [utfStepFast_length, hs])]
      exact ih tail _ (utfStepFast_length _ _)
    · rw [if_neg h, if_neg h, choose_empty _ _ (by rw [utfStepFast_length, hs])]
      exact ih tail _ hs

/-! ### The public input -/

theorem publicCapacity_le (length : Nat) : publicCapacity length ≤ 256 := by
  unfold publicCapacity
  split <;> omega

theorem publicInput_split (text timestamp : List (BitVec 8)) :
    publicInput text timestamp =
      (255 :: BitVec.ofNat 8 (text.length / 256) :: BitVec.ofNat 8 text.length ::
        (text ++ List.replicate (publicCapacity text.length - text.length) 0)) ++ timestamp := by
  simp only [publicInput, List.cons_append, List.nil_append, List.append_assoc]

theorem publicInput_length (text timestamp : List (BitVec 8)) (fits : text.length ≤ publicCapacity text.length)
    (eight : timestamp.length = 8) :
    (publicInput text timestamp).length = inputBytes (publicCapacity text.length) := by
  rw [publicInput_split]
  simp only [List.length_append, List.length_cons, List.length_replicate, eight, inputBytes]
  omega

theorem publicInput_take (text timestamp : List (BitVec 8)) (fits : text.length ≤ publicCapacity text.length) :
    (publicInput text timestamp).take (publicCapacity text.length + 3) =
      255 :: BitVec.ofNat 8 (text.length / 256) :: BitVec.ofNat 8 text.length ::
        (text ++ List.replicate (publicCapacity text.length - text.length) 0) := by
  rw [publicInput_split]
  apply List.take_left'
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

theorem publicInput_timestamp (text timestamp : List (BitVec 8)) (fits : text.length ≤ publicCapacity text.length)
    (eight : timestamp.length = 8) :
    ((publicInput text timestamp).drop (publicCapacity text.length + 3)).take 8 = timestamp := by
  rw [publicInput_split, List.drop_left' (by simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
  exact List.take_of_length_le (by omega)

theorem fromWire_public (text : List (BitVec 8)) (capacity : Nat) (fits : text.length ≤ capacity)
    (hc : capacity < 65536) :
    fromWire ByteAuth.concrete capacity (255 :: BitVec.ofNat 8 (text.length / 256) :: BitVec.ofNat 8 text.length ::
      (text ++ List.replicate (capacity - text.length) 0)) = ofContents capacity text := by
  rw [fromWire_decoded capacity hc 255 _ _ _
      (by simp only [List.length_append, List.length_replicate]; omega),
    public_length_value text.length (by omega), if_pos ⟨rfl, fits⟩, prefix_append_tail,
    prefix_contents capacity text fits]
  rfl

/-! ### The fast builder -/

/-- The smallest canonical varint width (1..10) of a word, if any. -/
def widthOf (word : BitVec 64) : Option Nat :=
  ((List.range 10).map (· + 1)).find? (fun w => decide (Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) w))

theorem widthOf_spec (word : BitVec 64) (width : Nat) (h : widthOf word = some width) :
    0 < width ∧ width ≤ 10 ∧ Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width := by
  unfold widthOf at h
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [List.mem_map, List.mem_range] at hm
  obtain ⟨m, hm, hmw⟩ := hm
  exact ⟨by omega, by omega, of_decide_eq_true hp⟩

theorem contentBytesSized_length_lt (body : List (BitVec 8)) (word : BitVec 64) (width : Nat)
    (bounded : body.length ≤ 300) (hl : width ≤ 10) :
    (contentBytesSized body word width).length < 65536 := by
  have h1 := dataMessageBytesSized_length body word width
  have h2 := lengthPrefix_length (dataMessageBytesSized body word width).length
  have h3 := lengthPrefix_length body.length
  simp only [contentBytesSized, List.length_append, List.length_cons, List.length_nil] at h1 ⊢
  omega

/-- `buildPadded` on the concrete operations for a public text (`publicInput`, capacity
`publicCapacity`), computed directly: `buildPaddedPublic_eq`. -/
def buildPaddedPublic (padded : Nat) (text timestamp : List (BitVec 8)) : List (BitVec 8) :=
  if text.length ≤ publicCapacity text.length ∧ timestamp.length = 8 ∧ 0 < padded ∧ padded < 65536 then
    match widthOf (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) with
    | none => buildPadded Sha256.concrete Varint64.concrete ByteAuth.concrete (publicCapacity text.length) padded
        (publicInput text timestamp)
    | some width =>
      let utf := utfLoopFast (text ++ List.replicate (publicCapacity text.length - text.length) 0) text.length
        (List.range (publicCapacity text.length)) (TlsWebSocketUpgrade.initial ByteAuth.concrete 7)
      let content := contentBytesSized text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width
      let out := if content.length < padded then ofContents padded (content ++ [128]) else zero ByteAuth.concrete padded
      let valid := ByteAuth.concrete.and out.valid
        (ByteAuth.eqMask ByteAuth.concrete (OpenResult.get ByteAuth.concrete utf 0) (ByteAuth.concrete.const 255))
      valid :: ByteAuth.release ByteAuth.concrete valid (ByteAuth.concrete.const 0 :: out.data ++ timestamp)
  else buildPadded Sha256.concrete Varint64.concrete ByteAuth.concrete (publicCapacity text.length) padded
    (publicInput text timestamp)

theorem buildPaddedPublic_eq (padded : Nat) (text timestamp : List (BitVec 8)) :
    buildPaddedPublic padded text timestamp =
      buildPadded Sha256.concrete Varint64.concrete ByteAuth.concrete (publicCapacity text.length) padded
        (publicInput text timestamp) := by
  unfold buildPaddedPublic
  split
  · rename_i cond
    obtain ⟨fits, eight, positive, hp⟩ := cond
    split
    · rfl
    · rename_i width hwidth
      obtain ⟨hw, hl, canonical⟩ := widthOf_spec _ _ hwidth
      have hcap := publicCapacity_le text.length
      have hlen := publicInput_length text timestamp fits eight
      have htake := publicInput_take text timestamp fits
      have hstamp := publicInput_timestamp text timestamp fits eight
      have hbody := fromWire_public text (publicCapacity text.length) fits (by omega)
      have hutf : utfLoop ByteAuth.concrete (ofContents (publicCapacity text.length) text).data
          (ofContents (publicCapacity text.length) text).lengthBits (List.range (publicCapacity text.length))
          (TlsWebSocketUpgrade.initial ByteAuth.concrete 7) =
          utfLoopFast (text ++ List.replicate (publicCapacity text.length - text.length) 0) text.length
            (List.range (publicCapacity text.length)) (TlsWebSocketUpgrade.initial ByteAuth.concrete 7) :=
        utfLoop_public _ text.length (by omega) _ (fun i hi => by simp only [List.mem_range] at hi; omega) _ (by simp [TlsWebSocketUpgrade.initial])
      have hcontent : PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
          (PrivateSend.join ByteAuth.concrete (publicCapacity text.length + 15)
            [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10 (ofContents (publicCapacity text.length) text),
             PrivateSend.join ByteAuth.concrete 11 [PrivateSend.literal ByteAuth.concrete 11 [ByteAuth.concrete.const 56],
               PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete
                 (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp)]]) =
          ofContents (publicCapacity text.length + 15 + 4)
            (contentBytesSized text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width) :=
        contentSized_contents (publicCapacity text.length) (by omega) text fits (by omega) _ width hw hl canonical
      have hclen := contentBytesSized_length_lt text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width
        (by omega) hl
      unfold buildPadded
      simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, htake, hstamp, hbody, hutf, hcontent]
      by_cases room : (contentBytesSized text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width).length < padded
      · have hpad : PrivateSend.join ByteAuth.concrete padded
            [ofContents (publicCapacity text.length + 15 + 4)
              (contentBytesSized text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width),
             PrivateSend.literal ByteAuth.concrete padded [ByteAuth.concrete.const 128]] =
            ofContents padded (contentBytesSized text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width ++ [128]) :=
          iso7816_sized_contents padded _ hp _ room
        rw [hpad, if_pos room]
      · have hpad : PrivateSend.join ByteAuth.concrete padded
            [ofContents (publicCapacity text.length + 15 + 4)
              (contentBytesSized text (Varint64.pack Varint64.concrete ByteAuth.concrete timestamp) width),
             PrivateSend.literal ByteAuth.concrete padded [ByteAuth.concrete.const 128]] =
            zero ByteAuth.concrete padded :=
          join_terminator_overflow padded _ hp positive _ (by omega) hclen
        rw [hpad, if_neg room]
  · rfl

/-- `firstFit` / `firstFitOfficial` on `buildPaddedPublic`, the padded size of a class given by
`paddedOf`. -/
def firstFitPublic (paddedOf : Nat → Nat) (text timestamp : List (BitVec 8)) :
    Nat → Nat → Option (Nat × List (BitVec 8))
  | 0, _ => none
  | fuel + 1, classes =>
    let built := buildPaddedPublic (paddedOf classes) text timestamp
    if built.head? = some 255 then some (classes, built)
    else firstFitPublic paddedOf text timestamp fuel (classes + 1)

theorem firstFitPublic_sized (text timestamp : List (BitVec 8)) (fuel classes : Nat) :
    firstFitPublic paddedBytes text timestamp fuel classes =
      firstFit (publicCapacity text.length) (publicInput text timestamp) fuel classes := by
  induction fuel generalizing classes with
  | zero => rfl
  | succ fuel ih =>
    simp only [firstFitPublic, firstFit, buildPaddedPublic_eq, buildSized_eq_buildPadded, ih]

theorem firstFitPublic_official (text timestamp : List (BitVec 8)) (fuel classes : Nat) :
    firstFitPublic officialPaddedBytes text timestamp fuel classes =
      firstFitOfficial (publicCapacity text.length) (publicInput text timestamp) fuel classes := by
  induction fuel generalizing classes with
  | zero => rfl
  | succ fuel ih =>
    simp only [firstFitPublic, firstFitOfficial, buildPaddedPublic_eq, buildOfficial, ih]

/-- `buildPublic`, computed directly (`buildPublicFast_eq`). -/
def buildPublicFast (limit : Nat) (text timestamp : List (BitVec 8)) : Option (Nat × List (BitVec 8)) :=
  firstFitPublic paddedBytes text timestamp limit 1

/-- `buildPublicOfficial`, computed directly (`buildPublicOfficialFast_eq`). -/
def buildPublicOfficialFast (limit : Nat) (text timestamp : List (BitVec 8)) : Option (Nat × List (BitVec 8)) :=
  firstFitPublic officialPaddedBytes text timestamp limit 1

theorem buildPublicFast_eq (limit : Nat) (text timestamp : List (BitVec 8)) :
    buildPublicFast limit text timestamp = buildPublic limit text timestamp :=
  firstFitPublic_sized text timestamp limit 1

theorem buildPublicOfficialFast_eq (limit : Nat) (text timestamp : List (BitVec 8)) :
    buildPublicOfficialFast limit text timestamp = buildPublicOfficial limit text timestamp :=
  firstFitPublic_official text timestamp limit 1

end TlsMpc.Signal.PrivateTextNotification
