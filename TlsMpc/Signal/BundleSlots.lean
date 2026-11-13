import TlsMpc.Signal.BundleResponse

/-!
One device of a prekey-bundle response with its five numbers in FIXED-WIDTH slots, so that one
circuit serves every digit count (`handshake_backend/EmpHybridWork/CIRCUIT_SHAPES.md`, "Not done"
3, now done this way; `TlsMpc/BundleSlotKernels.lean` is the kernel).

`BundleResponse.device` reads an item laid out for its digit counts `w`, so `bundle-item` is one
circuit per `(D, R, S, P, K)`: thousands for realistic ranges (registration ids of 1–5 digits,
key ids of 1–8). Here the runtime first SPLICES the item: before each number it inserts as many
public `filler` bytes (0, NUL; `0` characters before the emitter batch) as the number is shorter
than its slot (device id 3, registration id 5, key ids 10: the bounds `Widths.ok` allows), and
copies everything else unchanged (`splice` says how, from the public widths). The result has the
layout of `item (slots oneTime)` whatever the digit counts. The circuit also receives the five
digit counts (`widths`, one byte each, public: they are the ones `layout?` read off the opened
punctuation flags) and checks each slot against its count: the padding is the filler, the number
itself is a decimal as JSON writes it (no leading zero unless it is the only digit), and its value
is below the same bound as in `device`. The filler's low four bits are 0, so the decoded fields
are those of `device` on the original item (`BundleSlotWhole.deviceSlots_splice`).

`deviceSlots` is `BundleResponse.device` at the slot widths with `numberValid` replaced by
`slotValid`: the same template checks, separators, base64 decoding, key types and outputs.
It is written out here rather than by changing `device`, so that the existing kernels (and
`flat_kernel_emitter`, whose hash keys the circuit cache) stay as they are.
-/
namespace TlsMpc.Signal.BundleSlots
open Establish (part)
open ReceiveFirst (expect all either any)
open RelayEncoding (literal)
open BundleResponse (Widths Piece fieldOf literals decode decodeValid numberBits numberBytes digitValid item size
  header firstItem optional)

/-- The slot sizes: the largest digit counts `Widths.ok` allows. -/
def slots (oneTime : Bool) : Widths := ⟨3, 5, 10, if oneTime then 10 else 0, 10⟩

/-- The byte the runtime puts in front of a number to fill its slot: 0 (NUL), not `0` (48). It is
not a digit, so a slot's padding cannot be mistaken for digits of the number (with `0` padding,
`05` spliced with two digits and `5` spliced with one were the same slot, so a `widths` input that
disagreed with the splice could make the kernel accept the non-canonical `05`; NEEDS_REVIEW.md
3f, defect 2). Its low four bits are 0, so `numberBits` reads it as a leading zero. -/
def filler : Nat := 0

/-- 255 exactly when `width` (a byte) is between 1 and the slot's size `chars.length`, the
slot's first `chars.length − width` bytes are the `filler` byte, the remaining `width` bytes are a
decimal as JSON writes it (digits only, no leading zero unless it is the only digit), and the
slot's value is below `2^limit`. Since the filler is not a digit, the width that passes is the
number of bytes after the filler: a slot is accepted exactly when it is the filler-padding of a
canonical decimal, whatever the width byte says. -/
def slotValid (a : ByteAuth.Ops B) (limit : Nat) (width : B) (chars : List B) : B :=
  let n := chars.length
  let is := fun k => ByteAuth.eqMask a width (a.const k)
  let zero := fun j => ByteAuth.eqMask a (OpenResult.get a chars j) (a.const 48)
  all a ([any a ((List.range n).map (fun k => is (k + 1)))] ++
    -- position j is padding when the width is below n − j: then it must be the filler, else a digit
    (List.range n).map (fun j =>
      either a (a.and (any a ((List.range (n - j)).map is)) (ByteAuth.eqMask a (OpenResult.get a chars j) (a.const filler)))
        (a.and (a.not (any a ((List.range (n - j)).map is))) (digitValid a (OpenResult.get a chars j)))) ++
    -- position j is the number's first digit when the width is n − j: then not `0`, unless n − j = 1
    (List.range (n - 1)).map (fun j => a.not (a.and (is (n - j)) (zero j))) ++
    ((numberBits a chars).drop limit).map a.not)

/-- `BundleResponse.device` for an item spliced into the slot layout `item (slots oneTime)`,
with the digit counts as the bytes `widths` (device, registration, signed, one-time, Kyber;
the fourth is not read when `oneTime` is false). Outputs exactly as `device`. -/
def deviceSlots (a : ByteAuth.Ops B) (total start : Nat) (oneTime : Bool) (widths body : List B) : List (List B) :=
  let w := slots oneTime
  let pieces := item w
  let field := fieldOf body start pieces
  let width := fun i => OpenResult.get a widths i
  let shift := if w.oneTime = 0 then 0 else 2
  let stop := start + size pieces
  let identity := decode a (fieldOf body 0 header 0)
  let signedKey := decode a (field 3)
  let oneTimeKey := decode a (field 6)
  let kyberKey := decode a (field (6 + shift))
  let ok := all a ([literals a body 0 header, literals a body start pieces,
      expect a body (start - 1) (literal a (if start = firstItem then "[" else ",")),
      expect a body stop (literal a (if stop + 2 = total then "]}" else ",")),
      expect a body (total - 2) (literal a "]}"),
      decodeValid a (fieldOf body 0 header 0), ByteAuth.eqMask a (OpenResult.get a identity 0) (a.const 5),
      slotValid a 7 (width 0) (field 0), slotValid a 32 (width 1) (field 1), slotValid a 32 (width 2) (field 2),
      decodeValid a (field 3), ByteAuth.eqMask a (OpenResult.get a signedKey 0) (a.const 5), decodeValid a (field 4),
      slotValid a 32 (width 4) (field (5 + shift)), decodeValid a (field (6 + shift)),
      ByteAuth.eqMask a (OpenResult.get a kyberKey 0) (a.const 8), decodeValid a (field (7 + shift))] ++
    optional (w.oneTime != 0) [slotValid a 32 (width 3) (field 5), decodeValid a (field 6),
      ByteAuth.eqMask a (OpenResult.get a oneTimeKey 0) (a.const 5)])
  [ok] :: ([identity.drop 1, numberBytes a 1 (field 0), numberBytes a 4 (field 1), numberBytes a 4 (field 2),
      signedKey.drop 1, decode a (field 4), numberBytes a 4 (field (5 + shift)), kyberKey.drop 1,
      decode a (field (7 + shift))] ++
    optional (w.oneTime != 0) [numberBytes a 4 (field 5), oneTimeKey.drop 1]).map (ByteAuth.release a ok)

/-! ### The splice (public arithmetic, for the controllers) -/

/-- Piece by piece: `(zeros, copy)` turns a piece of the item for `w` into the same piece of the
slot item `to`: a number field of `n` digits whose slot has `m` bytes becomes `m − n` zeros and
the `n` digits; text and base64 fields are copied. -/
def runs : List Piece → List Piece → List (Nat × Nat)
  | .field n :: rest, .field m :: rest' => (m - n, n) :: runs rest rest'
  | p :: rest, _ :: rest' => (0, p.size) :: runs rest rest'
  | _, _ => []

/-- Adjacent runs merged: a run without zeros continues the copy before it. -/
def merge : List (Nat × Nat) → List (Nat × Nat)
  | (z, c) :: (0, c') :: rest => merge ((z, c + c') :: rest)
  | r :: rest => r :: merge rest
  | [] => []
termination_by xs => xs.length

/-- How the runtime builds the `item` input of `bundle-slot` from the item as it is in the body
(digit counts `w`): for each `(zeros, copy)`, `zeros` bytes `filler` (0), then the next `copy`
bytes of the item. Copies add up to `size (item w)`; zeros and copies to `size (item (slots _))`. -/
def splice (w : Widths) : List (Nat × Nat) := merge (runs (item w) (item (slots (w.oneTime != 0))))

/-- The splice applied to concrete bytes (what the runtime does; for the checks). -/
def spliced (w : Widths) (itemBytes : List α) (zero : α) : List α :=
  ((splice w).foldl (fun (acc : List α × Nat) (r : Nat × Nat) =>
    (acc.1 ++ List.replicate r.1 zero ++ (itemBytes.drop acc.2).take r.2, acc.2 + r.2)) ([], 0)).1

/-! ### From circuit to values -/

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}

theorem slotValid_map (ha : ByteAuth.Hom a a' f) (limit : Nat) (width : B) (chars : List B) :
    f (slotValid a limit width chars) = slotValid a' limit (f width) (chars.map f) := by
  have tail : (List.drop limit (numberBits a chars)).map (fun x => a'.not (f x)) =
      ((numberBits a' (chars.map f)).drop limit).map a'.not := by
    simp only [← BundleResponse.numberBits_map ha, List.map_drop, List.map_map, Function.comp_def]
  simp only [slotValid, ReceiveFirst.all_map ha, ReceiveFirst.any_map ha, ReceiveFirst.either_map ha, List.map_append,
    List.map_cons, List.map_nil, List.map_map, Function.comp_def, BundleResponse.digitValid_map ha, ha.not, ha.and,
    ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const, tail, List.length_map]

theorem deviceSlots_map (ha : ByteAuth.Hom a a' f) (total start : Nat) (oneTime : Bool) (widths body : List B) :
    (deviceSlots a total start oneTime widths body).map (List.map f) =
      deviceSlots a' total start oneTime (widths.map f) (body.map f) := by
  simp only [deviceSlots, List.map_cons, List.map_nil, List.map_append, List.map_map, Function.comp_def,
    ByteAuth.release_map ha, ReceiveFirst.all_map ha, BundleResponse.optional_map, BundleResponse.literals_map ha,
    ReceiveFirst.expect_map ha, RelayEncoding.literal_map ha, BundleResponse.decodeValid_map ha,
    BundleResponse.decode_map ha, slotValid_map ha, BundleResponse.numberBytes_map ha,
    ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const, BundleResponse.fieldOf_map, List.map_drop]

end Refinement

#print axioms slotValid_map
#print axioms deviceSlots_map

end TlsMpc.Signal.BundleSlots
