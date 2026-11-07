import TlsMpc.FieldDag

/-! RFC 7748 X25519 over the exact base field 2^255-19. Scalar bits are
LSB-indexed and clamped inside the circuit; the public ladder visits bits254..0.
The input u encoding is decoded with bit255 masked and reduced modulo p.
The fixed inverse exponent also maps zero to zero; TLS MUST reject that result.
No scalar, ladder intermediate or shared ECDH result is revealed here.
-/
namespace TlsMpc.X25519
open FieldDag

structure Ops (B : Type) where
  const : Nat → B
  add : B → B → B
  sub : B → B → B
  mul : B → B → B

def concrete : Ops F := ⟨ofNat, (· + ·), (· - ·), (· * ·)⟩
def symbolic : Ops Expr := ⟨Expr.const, Expr.bin .add, Expr.bin .sub, Expr.bin .mul⟩

def bitValue (b : Bool) : F := if b then 1 else 0
def select (o : Ops B) (bit yes no : B) : B := o.add no (o.mul bit (o.sub yes no))
def xorBit (o : Ops B) (a b : B) : B := o.sub (o.add a b) (o.mul (o.const 2) (o.mul a b))

structure Coordinates (B : Type) where
  x2 : B
  z2 : B
  x3 : B
  z3 : B

def Coordinates.map (f : B → C) (s : Coordinates B) : Coordinates C :=
  ⟨f s.x2, f s.z2, f s.x3, f s.z3⟩

def swap (o : Ops B) (bit : B) (s : Coordinates B) : Coordinates B :=
  ⟨select o bit s.x3 s.x2, select o bit s.z3 s.z2,
    select o bit s.x2 s.x3, select o bit s.z2 s.z3⟩

def advance (o : Ops B) (u : B) (s : Coordinates B) : Coordinates B :=
  let a := o.add s.x2 s.z2
  let aa := o.mul a a
  let b := o.sub s.x2 s.z2
  let bb := o.mul b b
  let e := o.sub aa bb
  let c := o.add s.x3 s.z3
  let d := o.sub s.x3 s.z3
  let da := o.mul d a
  let cb := o.mul c b
  let sum := o.add da cb
  let diff := o.sub da cb
  ⟨o.mul aa bb, o.mul e (o.add aa (o.mul (o.const 121665) e)),
    o.mul sum sum, o.mul u (o.mul diff diff)⟩

def ladder (o : Ops B) (u previous : B) (s : Coordinates B) : List B → Coordinates B
  | [] => swap o previous s
  | bit :: rest => ladder o u bit (advance o u (swap o (xorBit o previous bit) s)) rest

def powBits (o : Ops B) (x acc : B) : List Bool → B
  | [] => acc
  | bit :: rest =>
      let squared := o.mul acc acc
      powBits o x (if bit then o.mul squared x else squared) rest

def inverseBits : List Bool := (List.range 255).reverse.map (fun i => (modulus - 2).testBit i)
def inverse (o : Ops B) (x : B) : B := powBits o x (o.const 1) inverseBits

def scalarBit (o : Ops B) (input : Nat → B) (i : Nat) : B :=
  if i < 3 ∨ i = 255 then o.const 0 else if i = 254 then o.const 1 else input i

def scalarBits (o : Ops B) (input : Nat → B) : List B :=
  (List.range 255).reverse.map (scalarBit o input)

def compute (o : Ops B) (input : Nat → B) (u : B) : B :=
  let s := ladder o u (o.const 0) ⟨o.const 1, o.const 0, u, o.const 1⟩ (scalarBits o input)
  o.mul s.x2 (inverse o s.z2)

def expr : Expr := compute symbolic Expr.input (.input 256)

def decodeU (bytes : List UInt8) : F := ofNat
  ((bytes.take 32).zipIdx.foldl (fun n (b, i) =>
    n + (if i = 31 then b.toNat % 128 else b.toNat) * 256 ^ i) 0)

def decodeScalar (bytes : List UInt8) (i : Nat) : Bool :=
  ((bytes[i / 8]?).getD 0).toNat.testBit (i % 8)

def encode (x : F) : List UInt8 := (List.range 32).map (fun i => UInt8.ofNat (x.val / 256 ^ i))

def scalarSpec (input : Nat → Bool) (i : Nat) : Bool :=
  if i < 3 ∨ i = 255 then false else if i = 254 then true else input i

def swapSpec (bit : Bool) (s : Coordinates F) : Coordinates F :=
  if bit then ⟨s.x3, s.z3, s.x2, s.z2⟩ else s

/-- Direct RFC branch semantics; this is a functional specification, not the
constant-time execution path. Conditional swaps in the circuit are arithmetic. -/
def ladderSpec (u : F) (previous : Bool) (s : Coordinates F) : List Bool → Coordinates F
  | [] => swapSpec previous s
  | bit :: rest => ladderSpec u bit (advance concrete u (swapSpec (previous ^^ bit) s)) rest

def spec (input : Nat → Bool) (u : F) : F :=
  let s := ladderSpec u false ⟨1, 0, u, 1⟩ ((List.range 255).reverse.map (scalarSpec input))
  s.x2 * inverse concrete s.z2

structure Hom (a : Ops B) (b : Ops C) (f : B → C) : Prop where
  const : ∀ n, f (a.const n) = b.const n
  add : ∀ x y, f (a.add x y) = b.add (f x) (f y)
  sub : ∀ x y, f (a.sub x y) = b.sub (f x) (f y)
  mul : ∀ x y, f (a.mul x y) = b.mul (f x) (f y)

def evaluationHom (input : Nat → F) : Hom symbolic concrete (Expr.eval input) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

section Refinement
variable {a : Ops B} {b : Ops C} {f : B → C} (h : Hom a b f)
include h

theorem select_map (bit yes no : B) : f (select a bit yes no) = select b (f bit) (f yes) (f no) := by
  simp only [select, h.add, h.mul, h.sub]
theorem xorBit_map (x y : B) : f (xorBit a x y) = xorBit b (f x) (f y) := by
  simp only [xorBit, h.add, h.sub, h.mul, h.const]
theorem swap_map (bit : B) (s : Coordinates B) :
    (swap a bit s).map f = swap b (f bit) (s.map f) := by
  simp only [swap, Coordinates.map, select_map h]
theorem advance_map (u : B) (s : Coordinates B) :
    (advance a u s).map f = advance b (f u) (s.map f) := by
  simp only [advance, Coordinates.map, h.add, h.sub, h.mul, h.const]
theorem ladder_map (u previous : B) (s : Coordinates B) (bits : List B) :
    (ladder a u previous s bits).map f = ladder b (f u) (f previous) (s.map f) (bits.map f) := by
  induction bits generalizing previous s with
  | nil => exact swap_map h previous s
  | cons bit rest ih => simp only [ladder, List.map_cons, ih, advance_map h, swap_map h, xorBit_map h]
theorem powBits_map (x acc : B) (bits : List Bool) :
    f (powBits a x acc bits) = powBits b (f x) (f acc) bits := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [powBits, Bool.false_eq_true, ↓reduceIte, ih, h.mul]
theorem inverse_map (x : B) : f (inverse a x) = inverse b (f x) := by
  simp only [inverse, powBits_map h, h.const]
theorem scalarBit_map (input : Nat → B) (i : Nat) :
    f (scalarBit a input i) = scalarBit b (f ∘ input) i := by
  unfold scalarBit; split <;> first | simp only [h.const] | (split <;> simp [h.const])
theorem scalarBits_map (input : Nat → B) :
    (scalarBits a input).map f = scalarBits b (f ∘ input) := by
  simp only [scalarBits, List.map_map, Function.comp_def, scalarBit_map h]
theorem compute_map (input : Nat → B) (u : B) :
    f (compute a input u) = compute b (f ∘ input) (f u) := by
  have hm := ladder_map h u (a.const 0) ⟨a.const 1, a.const 0, u, a.const 1⟩ (scalarBits a input)
  have hx := congrArg Coordinates.x2 hm
  have hz := congrArg Coordinates.z2 hm
  simp only [Coordinates.map, h.const, scalarBits_map h] at hx hz
  simp only [compute, h.mul, inverse_map h, hx, hz, h.const]
end Refinement

private theorem add_sub_cancel (x y : F) : y + (x - y) = x := by
  apply Fin.eq_of_val_eq
  simp only [Fin.val_add, Fin.val_sub]
  rw [Nat.add_mod_mod]
  have hy := y.isLt
  have he : y.val + (modulus - y.val + x.val) = modulus + x.val := by omega
  rw [he, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt x.isLt]
  exact Nat.mod_eq_of_lt x.isLt

theorem select_value (bit : Bool) (yes no : F) :
    select concrete (bitValue bit) yes no = if bit then yes else no := by
  cases bit
  · change no + (0 : F) * (yes - no) = no
    rw [Fin.zero_mul, Fin.add_zero]
  · change no + (1 : F) * (yes - no) = yes
    rw [Fin.one_mul, add_sub_cancel]

theorem xorBit_value (a b : Bool) : xorBit concrete (bitValue a) (bitValue b) = bitValue (a ^^ b) := by
  cases a <;> cases b <;> decide

theorem swap_correct (bit : Bool) (s : Coordinates F) : swap concrete (bitValue bit) s = swapSpec bit s := by
  cases bit <;> simp only [swap, select_value, swapSpec, Bool.false_eq_true, ↓reduceIte]

theorem ladder_correct (u : F) (previous : Bool) (s : Coordinates F) (bits : List Bool) :
    ladder concrete u (bitValue previous) s (bits.map bitValue) = ladderSpec u previous s bits := by
  induction bits generalizing previous s with
  | nil => exact swap_correct previous s
  | cons bit rest ih => simp only [List.map_cons, ladder, xorBit_value, swap_correct, ladderSpec, ih]

theorem scalarBit_correct (input : Nat → Bool) (i : Nat) :
    scalarBit concrete (bitValue ∘ input) i = bitValue (scalarSpec input i) := by
  unfold scalarBit scalarSpec
  split <;> first | rfl | (split <;> rfl)

theorem compute_correct (input : Nat → Bool) (u : F) :
    compute concrete (bitValue ∘ input) u = spec input u := by
  have hb : scalarBits concrete (bitValue ∘ input) =
      ((List.range 255).reverse.map (scalarSpec input)).map bitValue := by
    simp only [scalarBits, List.map_map]
    apply List.map_congr_left
    intro i _
    exact scalarBit_correct input i
  simp only [compute, hb]
  change _ * inverse concrete _ = _
  rw [show concrete.const 0 = bitValue false from rfl, ladder_correct]
  rfl

def assignment (bits : Nat → Bool) (u : F) (i : Nat) : F :=
  if i = 256 then u else bitValue (bits i)

theorem compiled_compute_correct (bits : Nat → Bool) (u : F) (artifact : FieldDag.Artifact)
    (compiled : FieldDag.compile expr = some artifact) :
    FieldDag.result (FieldDag.concrete (assignment bits u)) artifact.nodes artifact.output = spec bits u := by
  rw [FieldDag.compile_correct _ _ compiled, expr, compute_map (evaluationHom (assignment bits u))]
  have hb : scalarBits concrete
      (Expr.eval (assignment bits u) ∘ Expr.input) =
      scalarBits concrete (bitValue ∘ bits) := by
    unfold scalarBits
    apply List.map_congr_left
    intro i hi
    have hi : i < 255 := List.mem_range.mp (List.mem_reverse.mp hi)
    simp only [Function.comp_def, scalarBit, concrete]
    split
    · rfl
    · split
      · rfl
      · simp [show i ≠ 256 by omega, Expr.eval, assignment]
  simp only [compute, hb, Expr.eval, assignment, ↓reduceIte]
  exact compute_correct bits u

end TlsMpc.X25519
