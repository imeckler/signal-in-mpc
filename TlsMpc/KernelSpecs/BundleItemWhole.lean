import TlsMpc.KernelSpecs.PointsAndItem
import TlsMpc.BundleSlotProofs

/-!
# `bundle-item` against the whole response body (locality of `BundleResponse.device`)

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `device_local` (the locality lemma): `BundleResponse.device` gives the same outputs on two bodies
  whenever they read the same on its windows (`Windows`): the header (`firstItem` bytes), the item
  (at `start'` in one, `start` in the other), the separator before it (`[` or `,`), what follows it
  (`]}` when it is the last item, else `,`) and the last two bytes. `deviceSlots_local`: the same
  for `BundleSlots.deviceSlots`.
* `cut_windows`, `device_cut`: the reassembled response `cut X first last start n` (what
  `bundle-item` takes as `head ‖ before ‖ item ‖ after ‖ end`) has those windows, whenever the item
  is placed as `layout?` places it (`Placed`: after the header, at least two bytes before the end,
  `first` exactly at `firstItem`, `last` exactly when followed by the closing `]}`).
* `bundleItem_whole`: `bundle-item`'s outputs are `BundleResponse.device` on the WHOLE response body
  at the item's real offset, for every assignment whose inputs are that cut.
* `bundleSlot_whole`: `bundle-slot`'s outputs are `BundleSlots.deviceSlots` on the whole body in
  which the item has been spliced into the slot layout.

Here `bundle-slot` is linked to the whole spliced body; `TlsMpc/KernelSpecs/BundleSlotWhole.lean`
links it to `device` on the body the server sent (`bundleSlot_device`: `deviceSlots` on a spliced
item equals `device` on the original, and the splice produces the slot layout). Trusted: that the
C++ worker binds the five inputs as `cut` describes.
-/
namespace TlsMpc.KernelSpecs.BundleItemWhole
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open Establish (part)
open BundleResponse (Widths Piece literals fieldOf item header firstItem size)

/-! ### Reading through windows -/

theorem size_cons (p : Piece) (ps : List Piece) : size (p :: ps) = p.size + size ps := by
  have gen : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih => intro a; simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega
  simp only [size, List.map_cons, List.foldl_cons]
  rw [gen _ (0 + p.size)]
  omega

theorem literal_length {B : Type} (a : ByteAuth.Ops B) (s : String) :
    (RelayEncoding.literal a s).length = s.toUTF8.size := by
  simp only [RelayEncoding.literal, List.length_map, Array.length_toList]
  rfl

/-- Two bodies agree on a stretch of `m` bytes, at `p` in the first and `q` in the second. -/
def Agree {B : Type} (X Y : List B) (p q m : Nat) : Prop := ∀ x c, x + c ≤ m → part X (p + x) c = part Y (q + x) c

theorem literals_agree {B : Type} (a : ByteAuth.Ops B) (X Y : List B) (p q m : Nat) (h : Agree X Y p q m) :
    ∀ (ps : List Piece) (x : Nat), x + size ps ≤ m → literals a X (p + x) ps = literals a Y (q + x) ps
  | [], _, _ => rfl
  | .text s :: rest, x, hx => by
      rw [size_cons] at hx
      simp only [Piece.size] at hx
      simp only [literals]
      have e : ReceiveFirst.expect a X (p + x) (RelayEncoding.literal a s) =
          ReceiveFirst.expect a Y (q + x) (RelayEncoding.literal a s) := by
        simp only [ReceiveFirst.expect]
        rw [h x _ (by rw [literal_length]; omega)]
      rw [e, show p + x + s.toUTF8.size = p + (x + s.toUTF8.size) by omega,
        show q + x + s.toUTF8.size = q + (x + s.toUTF8.size) by omega,
        literals_agree a X Y p q m h rest (x + s.toUTF8.size) (by omega)]
  | .field n :: rest, x, hx => by
      rw [size_cons] at hx
      simp only [Piece.size] at hx
      simp only [literals]
      rw [show p + x + n = p + (x + n) by omega, show q + x + n = q + (x + n) by omega,
        literals_agree a X Y p q m h rest (x + n) (by omega)]

theorem fieldOf_agree {B : Type} (X Y : List B) (p q m : Nat) (h : Agree X Y p q m) :
    ∀ (ps : List Piece) (x k : Nat), x + size ps ≤ m → fieldOf X (p + x) ps k = fieldOf Y (q + x) ps k
  | [], _, _, _ => rfl
  | .text s :: rest, x, k, hx => by
      rw [size_cons] at hx
      simp only [Piece.size] at hx
      simp only [fieldOf]
      rw [show p + x + s.toUTF8.size = p + (x + s.toUTF8.size) by omega,
        show q + x + s.toUTF8.size = q + (x + s.toUTF8.size) by omega,
        fieldOf_agree X Y p q m h rest (x + s.toUTF8.size) k (by omega)]
  | .field n :: rest, x, 0, hx => by
      rw [size_cons] at hx
      simp only [Piece.size] at hx
      simp only [fieldOf]
      exact h x n (by omega)
  | .field n :: rest, x, k + 1, hx => by
      rw [size_cons] at hx
      simp only [Piece.size] at hx
      simp only [fieldOf]
      rw [show p + x + n = p + (x + n) by omega, show q + x + n = q + (x + n) by omega,
        fieldOf_agree X Y p q m h rest (x + n) k (by omega)]

theorem part_append_left {B : Type} (X Y : List B) (o c : Nat) (h : o + c ≤ X.length) :
    part (X ++ Y) o c = part X o c := by
  simp only [part, List.drop_append]
  rw [List.take_append, show c - (List.drop o X).length = 0 by simp; omega]
  simp

theorem part_append_right {B : Type} (X Y : List B) (o c : Nat) : part (X ++ Y) (X.length + o) c = part Y o c := by
  simp only [part, List.drop_append]
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append, show X.length + o - X.length = o by omega]

theorem part_part {B : Type} (X : List B) (s n o c : Nat) (h : o + c ≤ n) : part (part X s n) o c = part X (s + o) c := by
  simp only [part, List.drop_take, List.take_take, List.drop_drop]
  congr 1
  omega

theorem header_size : size header = firstItem := by decide

/-! ### The reassembled response -/

/-- The kernel's five inputs, cut from the whole body `body` for an item of `n` bytes at `start`:
`head` (the first `firstItem` bytes), `before` (unless first: the byte before the item), `item`,
`after` (unless last: the byte after it), `end` (the last two bytes). -/
def cut {B : Type} (body : List B) (first last : Bool) (start n : Nat) : List B :=
  part body 0 firstItem ++ (if first then [] else part body (start - 1) 1) ++ part body start n ++
    (if last then [] else part body (start + n) 1) ++ part body (body.length - 2) 2

/-- The item's start in the reassembled response. -/
def cutStart (first : Bool) : Nat := firstItem + (if first then 0 else 1)

/-- The hypotheses that tie the cut to the whole body: the item lies after the header and ends at
least two bytes before the end; `first` holds exactly for the item at `firstItem`; `last` exactly
when the item is followed by the closing two bytes. -/
structure Placed (bodyLength : Nat) (first last : Bool) (start n : Nat) : Prop where
  after_header : firstItem ≤ start
  fits : start + n + 2 ≤ bodyLength
  first_iff : first = true ↔ start = firstItem
  last_iff : last = true ↔ start + n + 2 = bodyLength

theorem part_append_at {B : Type} (X Y : List B) (o c : Nat) (h : o = X.length) : part (X ++ Y) o c = part Y 0 c := by
  subst h
  have := part_append_right X Y 0 c
  simpa using this

theorem part_length {B : Type} (X : List B) (o c : Nat) (h : o + c ≤ X.length) : (part X o c).length = c := by
  simp only [part, List.length_take, List.length_drop]
  omega

theorem litOpen {B : Type} (a : ByteAuth.Ops B) : (RelayEncoding.literal a "[").length = 1 := by
  rw [literal_length]; rfl
theorem litComma {B : Type} (a : ByteAuth.Ops B) : (RelayEncoding.literal a ",").length = 1 := by
  rw [literal_length]; rfl
theorem litClose {B : Type} (a : ByteAuth.Ops B) : (RelayEncoding.literal a "]}").length = 2 := by
  rw [literal_length]; rfl

/-- The windows `device` reads, in the cut and in the whole body. -/
structure Windows {B : Type} (a : ByteAuth.Ops B) (R X : List B) (start' start n : Nat) : Prop where
  header : Agree X R 0 0 firstItem
  item : Agree X R start start' n
  before : ReceiveFirst.expect a R (start' - 1) (RelayEncoding.literal a (if start' = firstItem then "[" else ",")) =
    ReceiveFirst.expect a X (start - 1) (RelayEncoding.literal a (if start = firstItem then "[" else ","))
  after : ReceiveFirst.expect a R (start' + n) (RelayEncoding.literal a (if start' + n + 2 = R.length then "]}" else ",")) =
    ReceiveFirst.expect a X (start + n) (RelayEncoding.literal a (if start + n + 2 = X.length then "]}" else ","))
  ending : ReceiveFirst.expect a R (R.length - 2) (RelayEncoding.literal a "]}") =
    ReceiveFirst.expect a X (X.length - 2) (RelayEncoding.literal a "]}")

theorem cut_windows {B : Type} (a : ByteAuth.Ops B) (X : List B) (first last : Bool) (start n : Nat)
    (placed : Placed X.length first last start n) :
    Windows a (cut X first last start n) X (cutStart first) start n := by
  obtain ⟨hh, hfit, hfirst, hlast⟩ := placed
  have fi : firstItem = 73 := rfl
  obtain ⟨h, hd⟩ : ∃ h, h = part X 0 firstItem := ⟨_, rfl⟩
  obtain ⟨b, bd⟩ : ∃ b : List B, b = (if first then [] else part X (start - 1) 1) := ⟨_, rfl⟩
  obtain ⟨i, id'⟩ : ∃ i, i = part X start n := ⟨_, rfl⟩
  obtain ⟨af, ad⟩ : ∃ af : List B, af = (if last then [] else part X (start + n) 1) := ⟨_, rfl⟩
  obtain ⟨e, ed⟩ : ∃ e, e = part X (X.length - 2) 2 := ⟨_, rfl⟩
  have hR : cut X first last start n = h ++ (b ++ (i ++ (af ++ e))) := by
    rw [hd, bd, id', ad, ed]; simp [cut, List.append_assoc]
  have hLen : h.length = firstItem := by rw [hd]; exact part_length X 0 firstItem (by omega)
  have bLen : b.length = (if first then 0 else 1) := by
    rw [bd]; cases first
    · simp only [Bool.false_eq_true, if_false]; exact part_length X _ 1 (by omega)
    · rfl
  have iLen : i.length = n := by rw [id']; exact part_length X start n (by omega)
  have afLen : af.length = (if last then 0 else 1) := by
    rw [ad]; cases last
    · simp only [Bool.false_eq_true, if_false]; exact part_length X _ 1 (by omega)
    · rfl
  have eLen : e.length = 2 := by rw [ed]; exact part_length X _ 2 (by omega)
  have prefixLen : (h ++ b).length = cutStart first := by rw [List.length_append, hLen, bLen]; rfl
  have rLen : (h ++ (b ++ (i ++ (af ++ e)))).length = cutStart first + n + (if last then 0 else 1) + 2 := by
    simp only [List.length_append, hLen, bLen, iLen, afLen, eLen, cutStart]; omega
  rw [hR]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x c hxc
    rw [Nat.zero_add, part_append_left _ _ _ _ (by rw [hLen]; omega), hd, part_part X 0 firstItem x c hxc,
      Nat.zero_add]
  · intro x c hxc
    rw [← List.append_assoc h b, ← prefixLen, part_append_right, part_append_left _ _ _ _ (by rw [iLen]; omega), id',
      part_part X start n x c hxc]
  · simp only [ReceiveFirst.expect]
    by_cases hf : first = true
    · have es : start = firstItem := hfirst.mp hf
      have ec : cutStart first = firstItem := by simp [cutStart, hf]
      rw [ec, es, if_pos rfl, litOpen, part_append_left _ _ _ _ (by rw [hLen, fi]; decide),
        hd, part_part X 0 firstItem _ _ (by rw [fi]; decide), Nat.zero_add]
    · have ns : start ≠ firstItem := fun eq => hf (hfirst.mpr eq)
      have ec : cutStart first = firstItem + 1 := by simp [cutStart, hf]
      rw [ec, if_neg (by rw [fi]; decide), if_neg ns, litComma, show firstItem + 1 - 1 = h.length + 0 by rw [hLen]; omega,
        part_append_right, part_append_left _ _ _ _ (by rw [bLen, if_neg hf]; decide), bd, if_neg hf,
        part_part X (start - 1) 1 0 1 (Nat.le_refl _), Nat.add_zero]
  · simp only [ReceiveFirst.expect]
    rw [rLen]
    by_cases hl : last = true
    · have ex : start + n + 2 = X.length := hlast.mp hl
      rw [if_pos (by simp [hl]), if_pos ex, litClose, ← List.append_assoc h b, ← prefixLen, part_append_right,
        part_append_at i _ n _ iLen.symm, ad, if_pos hl, List.nil_append, ed, show X.length - 2 = start + n by omega,
        part_part X (start + n) 2 0 2 (Nat.le_refl _), Nat.add_zero]
    · have nx : ¬ start + n + 2 = X.length := fun eq => hl (hlast.mpr eq)
      rw [if_neg (by simp [hl]), if_neg nx, litComma, ← List.append_assoc h b, ← prefixLen, part_append_right,
        part_append_at i _ n _ iLen.symm, part_append_left _ _ _ _ (by rw [afLen, if_neg hl]; decide), ad, if_neg hl,
        part_part X (start + n) 1 0 1 (Nat.le_refl _), Nat.add_zero]
  · simp only [ReceiveFirst.expect]
    have : (h ++ (b ++ (i ++ (af ++ e)))).length - 2 = (h ++ b ++ i ++ af).length := by
      rw [rLen]; simp only [List.length_append, hLen, bLen, iLen, afLen, cutStart]; omega
    rw [this, show h ++ (b ++ (i ++ (af ++ e))) = (h ++ b ++ i ++ af) ++ e by simp [List.append_assoc],
      part_append_at _ _ _ _ rfl, litClose, ed, part_part X (X.length - 2) 2 0 2 (Nat.le_refl _), Nat.add_zero]

/-! ### `device` reads only those windows (the locality lemma) -/

theorem header_agree {B : Type} (a : ByteAuth.Ops B) (R X : List B) (h : Agree X R 0 0 firstItem) :
    literals a R 0 header = literals a X 0 header ∧ fieldOf R 0 header 0 = fieldOf X 0 header 0 := by
  have l := literals_agree a X R 0 0 firstItem h header 0 (by rw [header_size]; omega)
  have f := fieldOf_agree X R 0 0 firstItem h header 0 0 (by rw [header_size]; omega)
  exact ⟨l.symm, f.symm⟩

theorem item_agree {B : Type} (a : ByteAuth.Ops B) (R X : List B) (start' start : Nat) (w : Widths)
    (h : Agree X R start start' (size (item w))) :
    literals a R start' (item w) = literals a X start (item w) ∧
      ∀ k, fieldOf R start' (item w) k = fieldOf X start (item w) k := by
  have l := literals_agree a X R start start' _ h (item w) 0 (by omega)
  refine ⟨l.symm, fun k => ?_⟩
  have f := fieldOf_agree X R start start' _ h (item w) 0 k (by omega)
  exact f.symm

/-- **Locality of `BundleResponse.device`.** Two bodies on which the header, the item (at `start'`
in one and `start` in the other), the separator before it, what follows it and the last two bytes
read the same give the same outputs. -/
theorem device_local {B : Type} (a : ByteAuth.Ops B) (R X : List B) (start' start : Nat) (w : Widths)
    (hw : Windows a R X start' start (size (item w))) :
    BundleResponse.device a R.length start' w R = BundleResponse.device a X.length start w X := by
  obtain ⟨h1, h2⟩ := header_agree a R X hw.header
  obtain ⟨h3, h4⟩ := item_agree a R X start' start w hw.item
  simp only [BundleResponse.device, h1, h2, h3, h4, hw.before, hw.after, hw.ending]

/-- The same for `BundleSlots.deviceSlots` (the `bundle-slot` kernels), at the slot widths. -/
theorem deviceSlots_local {B : Type} (a : ByteAuth.Ops B) (R X : List B) (start' start : Nat) (oneTime : Bool)
    (widths : List B) (hw : Windows a R X start' start (size (item (BundleSlots.slots oneTime)))) :
    BundleSlots.deviceSlots a R.length start' oneTime widths R =
      BundleSlots.deviceSlots a X.length start oneTime widths X := by
  obtain ⟨h1, h2⟩ := header_agree a R X hw.header
  obtain ⟨h3, h4⟩ := item_agree a R X start' start (BundleSlots.slots oneTime) hw.item
  simp only [BundleSlots.deviceSlots, h1, h2, h3, h4, hw.before, hw.after, hw.ending]

/-- `device` on the cut equals `device` on the whole body. -/
theorem device_cut {B : Type} (a : ByteAuth.Ops B) (X : List B) (first last : Bool) (start : Nat) (w : Widths)
    (placed : Placed X.length first last start (size (item w))) :
    BundleResponse.device a (cut X first last start (size (item w))).length (cutStart first) w
        (cut X first last start (size (item w))) = BundleResponse.device a X.length start w X :=
  device_local a _ X _ start w (cut_windows a X first last start _ placed)

/-! ### The kernels against the whole body -/

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-item` computes `BundleResponse.device` on the whole response body.** For every
input assignment whose five inputs are the cut of a body `X` around an item of the kernel's widths
at `start` (`head` = the first `firstItem` bytes, `before` = the byte before the item unless first,
`item`, `after` = the byte after it unless last, `end` = the last two bytes), with `first` and
`last` saying whether the item is at `firstItem` and whether it is followed by the closing `]}`,
the kernel's outputs are those of `device` on `X` at `start`. -/
theorem bundleItem_whole (first last : Bool) (w : Widths) (assign : BVExpr.Assignment) (X : List (BitVec 8))
    (start : Nat) (placed : Placed X.length first last start (size (item w)))
    (inputs : let get := fun name => (lookup (BundleItemKernel.itemInputs first last w) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" = cut X first last start (size (item w))) :
    let out := BundleResponse.device ByteAuth.concrete X.length start w X
    values (BundleItemKernel.bundleItem first last w) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) := by
  intro out
  rw [PointsAndItem.bundleItem_spec]
  dsimp only at inputs ⊢
  rw [inputs, show BundleResponse.firstItem + (if first then 0 else 1) = cutStart first from rfl,
    device_cut ByteAuth.concrete X first last start w placed]

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` computes `BundleSlots.deviceSlots` on the whole (spliced) response body**, in the
same sense: its outputs are those of `deviceSlots` on any body `X` whose cut around the slot item
at `start` is the kernel's five inputs. (`X` is the response with this item replaced by its splice;
that `deviceSlots` on the spliced item equals `device` on the original is
`BundleSlotWhole.deviceSlots_splice`, and the kernel on the original body `bundleSlot_device`.) -/
theorem bundleSlot_whole (first last oneTime : Bool) (assign : BVExpr.Assignment) (X : List (BitVec 8))
    (start : Nat) (placed : Placed X.length first last start (size (item (BundleSlots.slots oneTime))))
    (inputs : let get := fun name => (lookup (BundleSlotKernel.slotInputs first last oneTime) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        cut X first last start (size (item (BundleSlots.slots oneTime)))) :
    let get := fun name => (lookup (BundleSlotKernel.slotInputs first last oneTime) name).map (BVExpr.eval assign)
    let out := BundleSlots.deviceSlots ByteAuth.concrete X.length start oneTime (get "widths") X
    values (BundleSlotKernel.bundleSlot first last oneTime) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if oneTime then [out.getD 10 [], out.getD 11 []] else []) := by
  intro get out
  rw [BundleSlotKernel.bundleSlot_spec]
  dsimp only at inputs ⊢
  rw [inputs, show BundleResponse.firstItem + (if first then 0 else 1) = cutStart first from rfl,
    deviceSlots_local ByteAuth.concrete _ X _ start oneTime _ (cut_windows ByteAuth.concrete X first last start _ placed)]

#print axioms cut_windows
#print axioms device_local
#print axioms deviceSlots_local
#print axioms bundleItem_whole
#print axioms bundleSlot_whole

end TlsMpc.KernelSpecs.BundleItemWhole
