import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.Varint64
import TlsMpc.TlsWebSocketFrame

/-! Bounded valid-UTF8 text notification. Private input: validity8, BE16 text
length, 48 text bytes, timestampBE8. Output: validity8, kind0, 80-byte ISO7816
application plaintext, identical timestampBE8. Public bucket80 matches the
relay notification profile. Invalid UTF8/bounds/status gives canonical zeros.
This is the text-only Content/DataMessage subset, not the full app schema. -/
namespace TlsMpc.Signal.PrivateTextNotification
open Std.Tactic.BVDecide

def utfLoop (a : ByteAuth.Ops B) (data lengthBits : List B) :
    List Nat → List B → List B
  | [],state => state
  | i::rest,state =>
    let active := PrivateBuffer.less a (PrivateBuffer.publicLength a i) lengthBits
    utfLoop a data lengthBits rest (TlsWebSocketUpgrade.choose a active
      (TlsWebSocketFrame.utfStep a state (OpenResult.get a data i)) state)

def build (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (input : List B) : List B :=
  if input.length != 59 then List.replicate 90 (a.const 0) else
  let body := PrivateBuffer.fromWire a 48 (input.take 51)
  let timestamp := (input.drop 51).take 8
  let utf := utfLoop a body.data body.lengthBits (List.range 48) (TlsWebSocketUpgrade.initial a 7)
  let bodyField := PrivateProtobuf.bytesField s a 10 body
  let timeField := PrivateSend.join a 11 [PrivateSend.literal a 11 [a.const 56],
    PrivateVarint.uint64 v a (Varint64.pack v a timestamp)]
  let dm := PrivateSend.join a 63 [bodyField,timeField]
  let content := PrivateProtobuf.bytesField s a 10 dm
  let padded := PrivateSend.join a 80 [content,PrivateSend.literal a 80 [a.const 128]]
  let valid := a.and padded.valid (ByteAuth.eqMask a (OpenResult.get a utf 0) (a.const 255))
  valid :: ByteAuth.release a valid (a.const 0 :: padded.data ++ timestamp)

theorem build_length (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (input : List B) : (build s v a input).length = 90 := by
  unfold build
  split
  · simp only [List.length_replicate]
  · rename_i h
    have hi : input.length = 59 := by simpa using h
    simp only [List.length_cons,ByteAuth.release,List.length_map,List.length_append,
      PrivateProtobuf.join_data_length,List.length_take,List.length_drop,hi]
    decide

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fv : V → V'}
  (hs : Sha256.Hom s s' f fw) (hv : Varint64.Hom v v' f fv) (ha : ByteAuth.Hom a a' f)
include ha

theorem utfLoop_map (data lengthBits : List B) (indices : List Nat) (state : List B) :
    (utfLoop a data lengthBits indices state).map f =
    utfLoop a' (data.map f) (lengthBits.map f) indices (state.map f) := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [utfLoop,ih,TlsWebSocketUpgrade.choose_map ha,TlsWebSocketFrame.utfStep_map ha,
      PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha,OpenResult.get_map ha]

theorem fromWire_data_map (cap : Nat) (input : List B) :
    (PrivateBuffer.fromWire a cap input).data.map f =
    (PrivateBuffer.fromWire a' cap (input.map f)).data :=
  congrArg PrivateBuffer.Buffer.data (PrivateBuffer.fromWire_map ha cap input)
theorem fromWire_bits_map (cap : Nat) (input : List B) :
    (PrivateBuffer.fromWire a cap input).lengthBits.map f =
    (PrivateBuffer.fromWire a' cap (input.map f)).lengthBits :=
  congrArg PrivateBuffer.Buffer.lengthBits (PrivateBuffer.fromWire_map ha cap input)
theorem join_valid_map (cap : Nat) (chunks : List (PrivateBuffer.Buffer B)) :
    f (PrivateSend.join a cap chunks).valid =
    (PrivateSend.join a' cap (chunks.map (PrivateBuffer.Buffer.map f))).valid :=
  congrArg PrivateBuffer.Buffer.valid (PrivateSend.join_map ha cap chunks)
theorem join_data_map (cap : Nat) (chunks : List (PrivateBuffer.Buffer B)) :
    (PrivateSend.join a cap chunks).data.map f =
    (PrivateSend.join a' cap (chunks.map (PrivateBuffer.Buffer.map f))).data :=
  congrArg PrivateBuffer.Buffer.data (PrivateSend.join_map ha cap chunks)

include hs hv

theorem build_map (input : List B) :
    (build s v a input).map f = build s' v' a' (input.map f) := by
  simp only [build,List.length_map]
  split
  · simp only [List.map_replicate,ha.const]
  · simp only [List.map_cons,List.map_append,ByteAuth.release_map ha,ha.and,ha.const,
      ByteAuth.eqMask_map ha,OpenResult.get_map ha,utfLoop_map ha,TlsWebSocketUpgrade.initial_map ha,
      PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,
      PrivateProtobuf.bytesField_map hs ha,PrivateVarint.uint64_map hv ha,Varint64.pack_map hv ha,
      PrivateBuffer.fromWire_map ha,List.map_take,List.map_drop,fromWire_data_map ha,fromWire_bits_map ha,join_valid_map ha,join_data_map ha]
end Refinement

theorem compiled_build_correct (input : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement (build Sha256.symbolic Varint64.symbolic ByteAuth.symbolic input)
      (build Sha256.concrete Varint64.concrete ByteAuth.concrete (input.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,build_map (Sha256.evaluationHom assign)
    (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

/-! ### Size classes

Signal pads the serialized Content with a 0x80 terminator and zeros up to a
whole number of 80-byte blocks. `buildSized` is `build` with the text capacity
and the number of blocks (the size class) as public parameters; `build` is its
instance with 48 bytes of text and one block (`buildSized_base`).

Layout, all public: the text input is `inputBytes capacity` bytes (validity8,
BE16 text length, `capacity` text bytes, timestampBE8); the built message is
`builtBytes classes` bytes (validity8, kind0, `paddedBytes classes` padded
content bytes, timestampBE8). A text whose Content and terminator do not fit
`paddedBytes classes` is rejected (canonical zeros), like invalid UTF-8.

What a size class reveals: the padded plaintext, and with it the session
ciphertext and the sealed-sender envelope, has a length fixed by the class, so
an observer of the envelope size learns the class and nothing finer: the
length of Content plus terminator rounded up to a multiple of 80. With today's
six-byte timestamp varints that is the text length in one of the ranges 1..68,
69..146, 147..226, 227..306 (classes 1..4; the public path below takes at most
256 bytes of text). -/

/-- Padded content bytes of a size class. -/
def paddedBytes (classes : Nat) : Nat := 80 * classes
/-- Bytes of a built message: validity, kind, padded content, timestamp. -/
def builtBytes (classes : Nat) : Nat := paddedBytes classes + 10
/-- Bytes of the text input: validity, BE16 length, `capacity` text bytes, timestamp. -/
def inputBytes (capacity : Nat) : Nat := capacity + 11

def buildSized (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (capacity classes : Nat) (input : List B) : List B :=
  if input.length != inputBytes capacity then List.replicate (builtBytes classes) (a.const 0) else
  let body := PrivateBuffer.fromWire a capacity (input.take (capacity + 3))
  let timestamp := (input.drop (capacity + 3)).take 8
  let utf := utfLoop a body.data body.lengthBits (List.range capacity) (TlsWebSocketUpgrade.initial a 7)
  let bodyField := PrivateProtobuf.bytesField s a 10 body
  let timeField := PrivateSend.join a 11 [PrivateSend.literal a 11 [a.const 56],
    PrivateVarint.uint64 v a (Varint64.pack v a timestamp)]
  let dm := PrivateSend.join a (capacity + 15) [bodyField,timeField]
  let content := PrivateProtobuf.bytesField s a 10 dm
  let padded := PrivateSend.join a (paddedBytes classes)
    [content,PrivateSend.literal a (paddedBytes classes) [a.const 128]]
  let valid := a.and padded.valid (ByteAuth.eqMask a (OpenResult.get a utf 0) (a.const 255))
  valid :: ByteAuth.release a valid (a.const 0 :: padded.data ++ timestamp)

/-- The 48-byte, one-block instance is `build` itself, so everything stated
about `build` is a statement about `buildSized 48 1`. -/
theorem buildSized_base (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (input : List B) : buildSized s v a 48 1 input = build s v a input := rfl

theorem buildSized_length (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (capacity classes : Nat) (input : List B) :
    (buildSized s v a capacity classes input).length = builtBytes classes := by
  unfold buildSized
  split
  · simp only [List.length_replicate]
  · rename_i h
    have hi : input.length = capacity + 11 := by simpa [inputBytes] using h
    simp only [List.length_cons,ByteAuth.release,List.length_map,List.length_append,
      PrivateProtobuf.join_data_length,List.length_take,List.length_drop,hi,builtBytes]
    omega

section SizedRefinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fv : V → V'}
  (hs : Sha256.Hom s s' f fw) (hv : Varint64.Hom v v' f fv) (ha : ByteAuth.Hom a a' f)
include hs hv ha

theorem buildSized_map (capacity classes : Nat) (input : List B) :
    (buildSized s v a capacity classes input).map f =
      buildSized s' v' a' capacity classes (input.map f) := by
  simp only [buildSized,List.length_map]
  split
  · simp only [List.map_replicate,ha.const]
  · simp only [List.map_cons,List.map_append,ByteAuth.release_map ha,ha.and,ha.const,
      ByteAuth.eqMask_map ha,OpenResult.get_map ha,utfLoop_map ha,TlsWebSocketUpgrade.initial_map ha,
      PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,
      PrivateProtobuf.bytesField_map hs ha,PrivateVarint.uint64_map hv ha,Varint64.pack_map hv ha,
      PrivateBuffer.fromWire_map ha,List.map_take,List.map_drop,fromWire_data_map ha,fromWire_bits_map ha,join_valid_map ha,join_data_map ha]
end SizedRefinement

theorem compiled_buildSized_correct (capacity classes : Nat) (input : List (BVExpr 8))
    (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (buildSized Sha256.symbolic Varint64.symbolic ByteAuth.symbolic capacity classes input)
      (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity classes
        (input.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,buildSized_map (Sha256.evaluationHom assign)
    (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

/-! ### Public text (the notify path)

The text is public there, so the controllers evaluate `buildSized` in the
clear and hand the built message to the send kernel of its size class. The
class is the smallest one whose padded content holds the Content and its
terminator: exactly the block count a Signal client's padding gives (in 80-byte
blocks), so it depends on nothing but the lengths of the text and of the
timestamp's varint. -/

/-- The first class from `first`, trying `fuel` classes, that accepts the input,
with the message built for it. -/
def firstFit (capacity : Nat) (input : List (BitVec 8)) : Nat → Nat → Option (Nat × List (BitVec 8))
  | 0, _ => none
  | fuel + 1, classes =>
    if (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity classes input).head? = some 255 then
      some (classes, buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity classes input)
    else firstFit capacity input fuel (classes + 1)

/-- Text capacity of the public input: 48 (the input of `build`) for texts that
fit it, 256 otherwise. -/
def publicCapacity (length : Nat) : Nat := if length ≤ 48 then 48 else 256

/-- The text input for a public text and an 8-byte big-endian timestamp. -/
def publicInput (text timestamp : List (BitVec 8)) : List (BitVec 8) :=
  [255, BitVec.ofNat 8 (text.length / 256), BitVec.ofNat 8 text.length] ++ text ++
    List.replicate (publicCapacity text.length - text.length) 0 ++ timestamp

/-- Size class (1..`limit`) and built message for a public text; `none` if the
text is rejected (not UTF-8, empty input shape, or too long for `limit` blocks). -/
def buildPublic (limit : Nat) (text timestamp : List (BitVec 8)) : Option (Nat × List (BitVec 8)) :=
  firstFit (publicCapacity text.length) (publicInput text timestamp) limit 1

/-- What `firstFit` returns is the accepted message of the chosen class, of
that class's length, and every smaller class tried rejects the input. -/
theorem firstFit_spec (capacity : Nat) (input : List (BitVec 8)) (fuel first chosen : Nat)
    (built : List (BitVec 8)) (h : firstFit capacity input fuel first = some (chosen, built)) :
    first ≤ chosen ∧ chosen < first + fuel ∧
    built = buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity chosen input ∧
    built.head? = some 255 ∧ built.length = builtBytes chosen ∧
    ∀ smaller, first ≤ smaller → smaller < chosen →
      (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity smaller input).head? ≠ some 255 := by
  induction fuel generalizing first with
  | zero => simp [firstFit] at h
  | succ fuel ih =>
    by_cases hc : (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity first input).head? = some 255
    · rw [firstFit, if_pos hc] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, rfl, hc, buildSized_length _ _ _ _ _ _, fun _ _ _ => by omega⟩
    · rw [firstFit, if_neg hc] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (first + 1) h
      refine ⟨by omega, by omega, h3, h4, h5, fun smaller low high => ?_⟩
      by_cases same : smaller = first
      · rw [same]; exact hc
      · exact h6 smaller (by omega) high

theorem buildPublic_spec (limit : Nat) (text timestamp : List (BitVec 8)) (chosen : Nat)
    (built : List (BitVec 8)) (h : buildPublic limit text timestamp = some (chosen, built)) :
    1 ≤ chosen ∧ chosen ≤ limit ∧
    built = buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete
      (publicCapacity text.length) chosen (publicInput text timestamp) ∧
    built.head? = some 255 ∧ built.length = builtBytes chosen ∧
    ∀ smaller, 1 ≤ smaller → smaller < chosen →
      (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete
        (publicCapacity text.length) smaller (publicInput text timestamp)).head? ≠ some 255 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := firstFit_spec _ _ _ _ _ _ h
  exact ⟨h1, by omega, h3, h4, h5, h6⟩

/-- Texts of at most 48 bytes that `build` accepts get class 1 and exactly the
message `build` gives: the 48-byte path is unchanged. -/
theorem buildPublic_short (limit : Nat) (text timestamp : List (BitVec 8)) (short : text.length ≤ 48)
    (valid : (build Sha256.concrete Varint64.concrete ByteAuth.concrete
      (publicInput text timestamp)).head? = some 255) :
    buildPublic (limit + 1) text timestamp =
      some (1, build Sha256.concrete Varint64.concrete ByteAuth.concrete (publicInput text timestamp)) := by
  have capacity : publicCapacity text.length = 48 := by simp [publicCapacity, short]
  unfold buildPublic
  rw [capacity, firstFit, buildSized_base, if_pos valid]
end TlsMpc.Signal.PrivateTextNotification
