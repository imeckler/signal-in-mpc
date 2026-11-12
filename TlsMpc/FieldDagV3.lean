import TlsMpc.FieldDag
import TlsMpc.FieldDagMulti

/-!
# Field programs, format V3: rows with explicit masks, output marks, a parser, the semantics

REORGANIZATION_PLAN.md 5.5 (stage S9). A V3 program is what `node_worker/src/program.rs`
evaluates for the engine instruction `program` (`TlsMpc/Node/Engine.lean`, opcode 22). The V2
format (`EmitWordMask.renderFieldAll`) is unchanged and its files stay beside the V3 ones for the
legacy library (`field_program.h`) until S11.

WHAT CHANGED FROM V2.
  * A division names its mask. `D a b m` is `a / b` with the program's mask input `m` (masks are a
    second input vector, beside the data inputs): the evaluator opens `o = b·m` (one checked
    opening), aborts when `o = 0`, and otherwise computes `(a·m)·o⁻¹`. In V2 the mask came from
    `RAND_bytes` inside the evaluator; in V3 the script supplies it (from `Channels.random`).
  * `Z a b m` is new: the same, but zero-tolerant: when `o = 0` its value is 0 instead of an abort
    (the X25519 and hinted-quotient behaviour, `x25519_fast.h:49-50`, `hinted_points.h:172`).
    `F k` is the public zero flag of the `Z` row `k` (1 when its opening was 0, else 0).
  * Every output carries a mark: `O node mark`, mark 0 never (stays in the engine) or 1 public
    (a declared check value or flag, which both parties may open).

THE TEXT (one canonical form; ASCII; every line ends in `\n`; single spaces; decimal numbers
without leading zeros):
    EMP_HYBRID_FIELD_DAG_V3
    INPUTS MASKS ROWS OUTPUTS
    57896044618658097711785492504343953926634992332820282019728792003956564819949
    one row per line:  I i | C n | A a b | S a b | M a b | D a b m | Z a b m | F k
    one output per line:  O node mark
Row `j` refers only to rows below `j`; `I i` has `i < INPUTS`, `C n` has `n < p`, `D`/`Z` name a
mask `m < MASKS`, `F k` names a `Z` row. The masks named by the `D`/`Z` rows, in row order, are
exactly `0, 1, …, MASKS − 1` (P-INV (d): every mask feeds exactly one `D`/`Z` row, and no other
row can read a mask). `Program.valid` is this list of conditions; `parse` accepts a text iff it is
`render p` for a valid `p` (`parse_render`, `parse_valid`, `render_parse`).

THE SEMANTICS (`eval`): from the data inputs and the masks, the output values and the openings
(the `b·m` of every `D`/`Z` row, in row order: exactly what the instruction releases), or `none`
for an abort. It computes what the evaluator computes, `(a·m)·(b·m)⁻¹` with `⁻¹` the Fermat power
`FieldDag.inverse`.

PROVED HERE (standard axioms only):
  * `parse_render` (round trip), `parse_valid`, `render_parse` (the parser accepts only rendered
    valid programs: one text per program).
  * `eval_ofArtifact`: a V3 program translated from a FieldDag artifact (`ofArtifact`: each `div`
    becomes `D` with the next mask) computes, when it does not abort, exactly the FieldDag
    semantics of the artifact. So `FieldDag.compileAll_correct` and every theorem about the
    source expressions carry over to the V3 file (`eval_compileAll`). `eval_ofArtifact_some`: with
    nonzero masks it aborts only when a FieldDag denominator is zero.
  * `ofArtifact_masksOk`, `parse_masksOk` (P-INV (d) for every translated and every loaded
    program); `masksOk_once` (what the check means).
  * P-INV (a)–(c) as field lemmas: `masked_div` (o ≠ 0 ⇒ the result is a·b⁻¹), `opening_zero_iff`
    (o = 0 ↔ b = 0 ∨ m = 0), `opening_bijective` (for b ≠ 0, m ↦ b·m is a bijection).
These need one fact about F that is true because p is prime and is not proved in this Mathlib-free
package: `FieldInverse` (x ≠ 0 → x·x⁻¹ = 1, Fermat's little theorem). Theorems that use it take it
as a hypothesis of that name; `proofs/TlsMpcProofs/FieldBridge.lean` (`toZMod_inverse`, with the
primality of p from `Prime25519.lean`) is where it is discharged.

Emitter isolation (rule 4): this module imports only FieldDag and FieldDagMulti; it is imported by
`EmitWordMask` (V3 export) and by `TlsMpc/Node/Engine.lean`.
-/

namespace TlsMpc.FieldDag.V3

open TlsMpc.FieldDag (F modulus ofNat inverse power)

/-! ## Programs -/

/-- An output's mark: `never` (0) stays in the engine; `pub` (1) is a declared check value or
flag, which both parties may open. The digits are the kernel layout's (`kernel.h:25`). -/
inductive OMark where
  | never
  | pub
  deriving DecidableEq, Repr

/-- One row of a V3 program. Operands `a`, `b`, `k` are row indices, `i` a data input, `m` a mask
input. -/
inductive Row where
  | input (i : Nat)
  | const (n : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  /-- `a / b` by masked inversion with mask `m`; aborts when `b·m` opens to 0. -/
  | div (a b m : Nat)
  /-- Zero-tolerant `a / b` with mask `m`: 0 when `b·m` opens to 0. -/
  | zdiv (a b m : Nat)
  /-- The zero flag of the `Z` row `k`: 1 when its opening was 0, else 0 (public). -/
  | flag (k : Nat)
  deriving DecidableEq, Repr

structure Program where
  inputs : Nat
  masks : Nat
  rows : List Row
  outputs : List (Nat × OMark)
  deriving DecidableEq, Repr

namespace Row

/-- The mask a row names (`D` and `Z` rows only). -/
def mask? : Row → Option Nat
  | .div _ _ m => some m
  | .zdiv _ _ m => some m
  | _ => none

def isZ : Row → Bool
  | .zdiv .. => true
  | _ => false

/-- The row is well formed at position `index` of a program with `inputs` data inputs and
`masks` masks, whose rows are `rows`. -/
def valid (inputs masks : Nat) (rows : List Row) (index : Nat) : Row → Bool
  | .input i => decide (i < inputs)
  | .const n => decide (n < modulus)
  | .add a b => decide (a < index) && decide (b < index)
  | .sub a b => decide (a < index) && decide (b < index)
  | .mul a b => decide (a < index) && decide (b < index)
  | .div a b m => decide (a < index) && decide (b < index) && decide (m < masks)
  | .zdiv a b m => decide (a < index) && decide (b < index) && decide (m < masks)
  | .flag k => decide (k < index) && ((rows[k]?).map isZ).getD false

end Row

namespace Program

/-- The masks named by the `D`/`Z` rows, in row order. -/
def maskUses (p : Program) : List Nat := p.rows.filterMap Row.mask?

/-- **P-INV (d), as a check**: the `D`/`Z` rows name the masks `0, 1, …, masks − 1`, in order. -/
def masksOk (p : Program) : Bool := p.maskUses == List.range p.masks

/-- Every row is well formed where it stands, every output names a row, every mask is used once. -/
def valid (p : Program) : Bool :=
  (p.rows.zipIdx.all fun e => e.1.valid p.inputs p.masks p.rows e.2) &&
    (p.outputs.all fun o => decide (o.1 < p.rows.length)) && p.masksOk

/-- How many rows open a value (one opening each, per instance). -/
def openings (p : Program) : Nat := p.maskUses.length

end Program

/-! ## P-INV (d): what `masksOk` means -/

/-- **P-INV (d).** In a program that passes `masksOk`, every mask `j < masks` is named by exactly
one `D`/`Z` row, and no row names any other mask. (No other kind of row can read a mask: masks
are a separate input vector that only `D`/`Z` rows address.) -/
theorem masksOk_once (p : Program) (h : p.masksOk = true) (j : Nat) :
    p.maskUses.count j = if j < p.masks then 1 else 0 := by
  simp only [Program.masksOk, beq_iff_eq] at h
  rw [h, List.count_range]

/-! ## The semantics over F -/

/-- The evaluation state: every row's value so far, and the openings so far (in row order). -/
structure State where
  vals : Array F := #[]
  opened : List F := []

/-! ### An executable inverse

`FieldDag.inverse` is `power x (p − 2)`, unary recursion: a definition, not a computation. The V3
semantics computes it by square and multiply (`powFast`, about 255 steps), proved equal
(`inverseFast_eq`), so `eval` runs (the Rust test vectors are computed by it). -/

theorem ofNat_one : ofNat 1 = (1 : F) := rfl

theorem power_add (x : F) (a b : Nat) : power x (a + b) = power x a * power x b := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    show power x b = ofNat 1 * power x b
    rw [ofNat_one]
    grind
  | succ a ih =>
    rw [Nat.succ_add, power, power, ih]
    grind

/-- `x^n` by square and multiply. -/
def powFast (x : F) (n : Nat) : F :=
  if n = 0 then ofNat 1
  else
    let half := powFast x (n / 2)
    if n % 2 = 0 then half * half else x * (half * half)
termination_by n
decreasing_by omega

theorem powFast_eq (x : F) (n : Nat) : powFast x n = power x n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [powFast]
    split
    · next h => subst h; rfl
    · next h =>
      have e := ih (n / 2) (by omega)
      simp only [e]
      split
      · next h2 =>
        rw [← power_add]
        congr 1
        omega
      · next h2 =>
        rw [← power_add]
        have : n = (n / 2 + n / 2) + 1 := by omega
        conv => rhs; rw [this]
        rfl

/-- The inverse the semantics computes. -/
def inverseFast (x : F) : F := powFast x (modulus - 2)

theorem inverseFast_eq (x : F) : inverseFast x = inverse x := powFast_eq x _

/-- A row's value (0 for a dangling index, as FieldDag's `run`). -/
def get (vals : Array F) (a : Nat) : F := vals[a]?.getD (ofNat 0)

/-- One row. `input i` and `mask m` are the data inputs and masks of this instance. -/
def step (rows : List Row) (input mask : Nat → F) (s : State) : Row → Option State
  | .input i => some { s with vals := s.vals.push (input i) }
  | .const n => some { s with vals := s.vals.push (ofNat n) }
  | .add a b => some { s with vals := s.vals.push (get s.vals a + get s.vals b) }
  | .sub a b => some { s with vals := s.vals.push (get s.vals a - get s.vals b) }
  | .mul a b => some { s with vals := s.vals.push (get s.vals a * get s.vals b) }
  | .div a b m =>
    let o := get s.vals b * mask m
    if o = 0 then none
    else some ⟨s.vals.push (get s.vals a * mask m * inverseFast o), s.opened ++ [o]⟩
  | .zdiv a b m =>
    let o := get s.vals b * mask m
    some ⟨s.vals.push (if o = 0 then ofNat 0 else get s.vals a * mask m * inverseFast o), s.opened ++ [o]⟩
  | .flag k =>
    match rows[k]? with
    | some (.zdiv _ b m) => some { s with vals := s.vals.push (if get s.vals b * mask m = 0 then ofNat 1 else ofNat 0) }
    | _ => some { s with vals := s.vals.push (ofNat 0) }

/-- All rows from state `s`. -/
def runFrom (rows : List Row) (input mask : Nat → F) (s : State) : Option State :=
  rows.foldlM (step rows input mask) s

/-- **The V3 semantics**: the outputs and the openings, or `none` (a `D` row's opening was 0). -/
def eval (p : Program) (input mask : Nat → F) : Option (List F × List F) :=
  (runFrom p.rows input mask {}).map fun s => (p.outputs.map fun o => get s.vals o.1, s.opened)

/-- Running rows adds one opening per `D`/`Z` row, and nothing else. -/
theorem foldlM_opened (rows : List Row) (input mask : Nat → F) :
    ∀ (rs : List Row) (s s' : State), rs.foldlM (step rows input mask) s = some s' →
      s'.opened.length = s.opened.length + (rs.filterMap Row.mask?).length := by
  intro rs
  induction rs with
  | nil =>
    intro s s' h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | cons r rs ih =>
    intro s s' h
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    cases r with
    | input i => simp only [step, Option.bind_some] at h; simp [Row.mask?, ih _ _ h]
    | const n => simp only [step, Option.bind_some] at h; simp [Row.mask?, ih _ _ h]
    | add a b => simp only [step, Option.bind_some] at h; simp [Row.mask?, ih _ _ h]
    | sub a b => simp only [step, Option.bind_some] at h; simp [Row.mask?, ih _ _ h]
    | mul a b => simp only [step, Option.bind_some] at h; simp [Row.mask?, ih _ _ h]
    | div a b m =>
      simp only [step] at h
      split at h
      · simp at h
      · simp only [Option.bind_some] at h
        simp only [ih _ _ h, Row.mask?, List.filterMap_cons, List.length_append, List.length_cons,
          List.length_nil]
        omega
    | zdiv a b m =>
      simp only [step, Option.bind_some] at h
      simp only [ih _ _ h, Row.mask?, List.filterMap_cons, List.length_append, List.length_cons,
        List.length_nil]
      omega
    | flag k =>
      simp only [step] at h
      split at h <;> (simp only [Option.bind_some] at h; simp [Row.mask?, ih _ _ h])

/-- **A program opens exactly one value per `D`/`Z` row** (and has one value per output). -/
theorem eval_lengths (p : Program) (input mask : Nat → F) (outs opened : List F)
    (h : eval p input mask = some (outs, opened)) :
    opened.length = p.openings ∧ outs.length = p.outputs.length := by
  simp only [eval, runFrom, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨s, hs, rfl, rfl⟩ := h
  have := foldlM_opened p.rows input mask p.rows {} s hs
  simp only [Program.openings, Program.maskUses, List.length_map]
  simpa using this

/-! ## P-INV (a)–(c): masked inversion, as field facts -/

/-- Fermat's little theorem for p = 2^255 − 19 in the form the masked inversion needs. True
because p is prime; discharged in the Mathlib package (`proofs/`, `FieldBridge.toZMod_inverse`). -/
def FieldInverse : Prop := ∀ x : F, x ≠ 0 → x * inverse x = 1

theorem mul_ne_zero_left {b m : F} (h : b * m ≠ 0) : b ≠ 0 := by
  intro hb
  apply h
  subst hb
  grind

theorem mul_ne_zero_right {b m : F} (h : b * m ≠ 0) : m ≠ 0 := by
  intro hm
  apply h
  subst hm
  grind

/-- No zero divisors (from `FieldInverse`). -/
theorem mul_ne_zero (hinv : FieldInverse) {b m : F} (hb : b ≠ 0) (hm : m ≠ 0) : b * m ≠ 0 := by
  intro h
  have h1 := hinv b hb
  apply hm
  grind

/-- **P-INV (a).** When the opening `o = b·m` is not 0, the evaluator's `(a·m)·o⁻¹` is `a·b⁻¹`. -/
theorem masked_div (hinv : FieldInverse) (a b m : F) (h : b * m ≠ 0) :
    a * m * inverse (b * m) = a * inverse b := by
  have h1 := hinv (b * m) h
  have h2 := hinv b (mul_ne_zero_left h)
  grind

/-- **P-INV (b).** The opening is 0 iff the denominator or the mask is. -/
theorem opening_zero_iff (hinv : FieldInverse) (b m : F) : b * m = 0 ↔ b = 0 ∨ m = 0 := by
  constructor
  · intro h
    by_cases hb : b = 0
    · exact Or.inl hb
    · by_cases hm : m = 0
      · exact Or.inr hm
      · exact absurd h (mul_ne_zero hinv hb hm)
  · rintro (h | h) <;> subst h <;> grind

/-- **P-INV (c).** For `b ≠ 0`, `m ↦ b·m` is a bijection of F (so a uniform mask makes the opening
uniform, whatever `b`): injective, with inverse `o ↦ b⁻¹·o`. -/
theorem opening_bijective (hinv : FieldInverse) (b : F) (hb : b ≠ 0) :
    (∀ m m' : F, b * m = b * m' → m = m') ∧ (∀ o : F, b * (inverse b * o) = o) := by
  have h1 := hinv b hb
  refine ⟨fun m m' h => ?_, fun o => by grind⟩
  have : inverse b * (b * m) = inverse b * (b * m') := by rw [h]
  grind

/-! ## From FieldDag: every `div` becomes a `D` row with the next mask -/

/-- The rows of FieldDag nodes, the `div`s numbered from mask `k`. -/
def ofNodes : Nat → List FieldDag.Node → List Row
  | _, [] => []
  | k, .input i :: ns => .input i :: ofNodes k ns
  | k, .const n :: ns => .const n :: ofNodes k ns
  | k, .bin .add a b :: ns => .add a b :: ofNodes k ns
  | k, .bin .sub a b :: ns => .sub a b :: ofNodes k ns
  | k, .bin .mul a b :: ns => .mul a b :: ofNodes k ns
  | k, .bin .div a b :: ns => .div a b k :: ofNodes (k + 1) ns

/-- How many divisions. -/
def divCount : List FieldDag.Node → Nat
  | [] => 0
  | .bin .div _ _ :: ns => divCount ns + 1
  | _ :: ns => divCount ns

/-- The V3 program of a multi-output FieldDag artifact with `inputs` data inputs; output `j`
gets the mark `marks j`. -/
def ofArtifact (inputs : Nat) (a : FieldDag.MultiArtifact) (marks : Nat → OMark) : Program where
  inputs := inputs
  masks := divCount a.nodes
  rows := ofNodes 0 a.nodes
  outputs := a.outputs.zipIdx.map fun e => (e.1, marks e.2)

theorem maskUses_ofNodes (k : Nat) (ns : List FieldDag.Node) :
    (ofNodes k ns).filterMap Row.mask? = List.range' k (divCount ns) := by
  induction ns generalizing k with
  | nil => rfl
  | cons n ns ih =>
    cases n with
    | input i => simp [ofNodes, divCount, Row.mask?, ih]
    | const c => simp [ofNodes, divCount, Row.mask?, ih]
    | bin op a b =>
      cases op with
      | add => simp [ofNodes, divCount, Row.mask?, ih]
      | sub => simp [ofNodes, divCount, Row.mask?, ih]
      | mul => simp [ofNodes, divCount, Row.mask?, ih]
      | div =>
        simp only [ofNodes, divCount, List.filterMap_cons, Row.mask?, ih]
        rw [List.range'_succ]

/-- **P-INV (d) for every translated program**: the `D` rows name the masks in order. -/
theorem ofArtifact_masksOk (inputs : Nat) (a : FieldDag.MultiArtifact) (marks : Nat → OMark) :
    (ofArtifact inputs a marks).masksOk = true := by
  simp [Program.masksOk, Program.maskUses, ofArtifact, maskUses_ofNodes, List.range_eq_range']

theorem length_ofNodes (k : Nat) (ns : List FieldDag.Node) : (ofNodes k ns).length = ns.length := by
  induction ns generalizing k with
  | nil => rfl
  | cons n ns ih =>
    cases n with
    | input i => simp [ofNodes, ih]
    | const c => simp [ofNodes, ih]
    | bin op a b => cases op <;> simp [ofNodes, ih]

/-- The FieldDag value pushed by a node, through `get` (the same default, `ofNat 0`). -/
theorem fieldDag_step (input : Nat → F) (vals : Array F) (n : FieldDag.Node) :
    FieldDag.step (FieldDag.concrete input) vals n =
      vals.push (match n with
        | .input i => input i
        | .const c => ofNat c
        | .bin op a b => op.eval (get vals a) (get vals b)) := by
  cases n <;> rfl

/-- **Soundness of the translation, row by row**: a run of the translated rows that does not abort
leaves exactly the values FieldDag's `run` computes. -/
theorem runFrom_ofNodes (hinv : FieldInverse) (rows : List Row) (input mask : Nat → F) :
    ∀ (ns : List FieldDag.Node) (k : Nat) (s s' : State),
      (ofNodes k ns).foldlM (step rows input mask) s = some s' →
      s'.vals = FieldDag.run (FieldDag.concrete input) ns s.vals := by
  intro ns
  induction ns with
  | nil =>
    intro k s s' h
    simp only [ofNodes, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | cons n ns ih =>
    intro k s s' h
    have hrun : FieldDag.run (FieldDag.concrete input) (n :: ns) s.vals =
        FieldDag.run (FieldDag.concrete input) ns (FieldDag.step (FieldDag.concrete input) s.vals n) := rfl
    rw [hrun, fieldDag_step]
    cases n with
    | input i =>
      simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some] at h
      exact ih k _ _ h
    | const c =>
      simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some] at h
      exact ih k _ _ h
    | bin op a b =>
      cases op with
      | add =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some] at h
        exact ih k _ _ h
      | sub =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some] at h
        exact ih k _ _ h
      | mul =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some] at h
        exact ih k _ _ h
      | div =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind] at h
        split at h
        · simp at h
        · next ho =>
          simp only [Option.bind_some] at h
          have e := ih (k + 1) _ _ h
          rw [e]
          simp only [FieldDag.Bin.eval, inverseFast_eq]
          rw [masked_div hinv _ _ _ ho]

/-- The FieldDag denominators of a run are nonzero (the condition under which FieldDag's `div` is
a true division and the runtime does not abort). -/
def DivisorsNonzero (input : Nat → F) : Array F → List FieldDag.Node → Prop
  | _, [] => True
  | vals, n :: ns =>
    (match n with
     | .bin .div _ b => get vals b ≠ 0
     | _ => True) ∧ DivisorsNonzero input (FieldDag.step (FieldDag.concrete input) vals n) ns

/-- **Completeness of the translation, row by row**: with nonzero masks and nonzero FieldDag
denominators, the translated rows do not abort. -/
theorem runFrom_ofNodes_some (hinv : FieldInverse) (rows : List Row) (input mask : Nat → F)
    (hm : ∀ j, mask j ≠ 0) :
    ∀ (ns : List FieldDag.Node) (k : Nat) (s : State), DivisorsNonzero input s.vals ns →
      ∃ s', (ofNodes k ns).foldlM (step rows input mask) s = some s' := by
  intro ns
  induction ns with
  | nil => intro k s _; exact ⟨s, rfl⟩
  | cons n ns ih =>
    intro k s hd
    obtain ⟨h0, hd⟩ := hd
    rw [fieldDag_step] at hd
    cases n with
    | input i =>
      simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some]
      exact ih k _ hd
    | const c =>
      simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some]
      exact ih k _ hd
    | bin op a b =>
      cases op with
      | add =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some]
        exact ih k _ hd
      | sub =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some]
        exact ih k _ hd
      | mul =>
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, Option.bind_some]
        exact ih k _ hd
      | div =>
        have ho : get s.vals b * mask k ≠ 0 := mul_ne_zero hinv h0 (hm k)
        simp only [ofNodes, List.foldlM_cons, step, Option.bind_eq_bind, if_neg ho, Option.bind_some]
        refine ih (k + 1) _ ?_
        simp only [FieldDag.Bin.eval] at hd
        rw [inverseFast_eq, masked_div hinv _ _ _ ho]
        exact hd

/-- **V3 evaluation agrees with the FieldDag semantics.** A translated artifact that does not abort
outputs exactly FieldDag's results (`FieldDag.result`), in order. -/
theorem eval_ofArtifact (hinv : FieldInverse) (inputs : Nat) (a : FieldDag.MultiArtifact)
    (marks : Nat → OMark) (input mask : Nat → F) (outs opened : List F)
    (h : eval (ofArtifact inputs a marks) input mask = some (outs, opened)) :
    outs = a.outputs.map (FieldDag.result (FieldDag.concrete input) a.nodes) := by
  simp only [eval, runFrom, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨s, hs, rfl, -⟩ := h
  have e := runFrom_ofNodes hinv _ input mask a.nodes 0 {} s hs
  have hl : (a.outputs.zipIdx.map fun e => (e.1, marks e.2)).map Prod.fst = a.outputs := by
    rw [List.map_map]
    exact List.zipIdx_map_fst 0 a.outputs
  have hg : (fun o : Nat × OMark => get s.vals o.1) = (fun o => get s.vals o) ∘ Prod.fst := rfl
  simp only [ofArtifact]
  rw [hg, ← List.map_map, hl]
  apply List.map_congr_left
  intro o _
  simp only [get, FieldDag.result, e]
  rfl

/-- With nonzero masks, a translated artifact aborts only on a zero FieldDag denominator. -/
theorem eval_ofArtifact_some (hinv : FieldInverse) (inputs : Nat) (a : FieldDag.MultiArtifact)
    (marks : Nat → OMark) (input mask : Nat → F) (hm : ∀ j, mask j ≠ 0)
    (hd : DivisorsNonzero input #[] a.nodes) :
    (eval (ofArtifact inputs a marks) input mask).isSome := by
  obtain ⟨s, hs⟩ := runFrom_ofNodes_some hinv (ofNodes 0 a.nodes) input mask hm a.nodes 0 {} hd
  simp [eval, runFrom, ofArtifact, hs]

/-- **Every theorem about a compiled field program carries over to its V3 file**: the outputs of
the V3 program of `compileAll es` are the source expressions' values (`compileAll_correct`). -/
theorem eval_compileAll (hinv : FieldInverse) (inputs : Nat) (es : List FieldDag.Expr)
    (a : FieldDag.MultiArtifact) (hc : FieldDag.compileAll es = some a) (marks : Nat → OMark)
    (input mask : Nat → F) (outs opened : List F)
    (h : eval (ofArtifact inputs a marks) input mask = some (outs, opened)) :
    outs = es.map (FieldDag.Expr.eval input) := by
  rw [eval_ofArtifact hinv inputs a marks input mask outs opened h]
  exact FieldDag.compileAll_correct es a hc input

/-! ## The text: printer -/

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- Decimal, most significant digit first, no leading zeros. -/
def decimal (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else decimal (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

def magic : List Char := "EMP_HYBRID_FIELD_DAG_V3".toList

def markChar : OMark → Char
  | .never => '0'
  | .pub => '1'

def Row.chars : Row → List Char
  | .input i => 'I' :: ' ' :: decimal i
  | .const n => 'C' :: ' ' :: decimal n
  | .add a b => 'A' :: ' ' :: (decimal a ++ ' ' :: decimal b)
  | .sub a b => 'S' :: ' ' :: (decimal a ++ ' ' :: decimal b)
  | .mul a b => 'M' :: ' ' :: (decimal a ++ ' ' :: decimal b)
  | .div a b m => 'D' :: ' ' :: (decimal a ++ ' ' :: (decimal b ++ ' ' :: decimal m))
  | .zdiv a b m => 'Z' :: ' ' :: (decimal a ++ ' ' :: (decimal b ++ ' ' :: decimal m))
  | .flag k => 'F' :: ' ' :: decimal k

def outChars (o : Nat × OMark) : List Char := 'O' :: ' ' :: (decimal o.1 ++ [' ', markChar o.2])

def line (l : List Char) : List Char := l ++ ['\n']

/-- The text of a program, as characters. -/
def chars (p : Program) : List Char :=
  magic ++ '\n' ::
    (decimal p.inputs ++ ' ' :: (decimal p.masks ++ ' ' :: (decimal p.rows.length ++ ' ' ::
      (decimal p.outputs.length ++ '\n' ::
    (decimal modulus ++ '\n' ::
    ((p.rows.map fun r => line r.chars).flatten ++ (p.outputs.map fun o => line (outChars o)).flatten))))))

/-- **The V3 printer.** -/
def render (p : Program) : String := String.ofList (chars p)

/-- The printer the emitter uses: only valid programs are printed (so every exported file parses
back to its program, `parse_render`). -/
def renderValid (p : Program) : Except String String :=
  if p.valid then .ok (render p) else .error "V3 field program is not valid"

/-! ## The text: parser -/

/-- A parser: the value and the rest of the input, or `none`. -/
def P (α : Type) : Type := List Char → Option (α × List Char)

namespace P

def pure {α : Type} (a : α) : P α := fun s => some (a, s)
def bind {α β : Type} (d : P α) (f : α → P β) : P β := fun s =>
  match d s with
  | some (a, s') => f a s'
  | none => none

instance : Monad P where
  pure := P.pure
  bind := P.bind

@[simp] theorem bind_apply {α β : Type} (d : P α) (f : α → P β) (s : List Char) :
    (d >>= f) s = (match d s with
      | some (a, s') => f a s'
      | none => none) := rfl
@[simp] theorem pure_apply {α : Type} (a : α) (s : List Char) : (Pure.pure a : P α) s = some (a, s) := rfl

def fail {α : Type} : P α := fun _ => none

/-- The literal `l`. -/
def expect : List Char → P Unit
  | [], s => some ((), s)
  | _ :: _, [] => none
  | c :: l, d :: s => if c = d then expect l s else none

def anyChar : P Char
  | [] => none
  | c :: s => some (c, s)

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The longest run of digits at the front. -/
def spanDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: s => if isDigit c then let r := spanDigits s; (c :: r.1, r.2) else ([], c :: s)

def value (ds : List Char) : Nat := ds.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

/-- A decimal number in canonical form (at least one digit, no leading zero). -/
def nat : P Nat := fun s =>
  let r := spanDigits s
  if r.1 ≠ [] ∧ decimal (value r.1) = r.1 then some (value r.1, r.2) else none

def count {α : Type} (d : P α) : Nat → P (List α)
  | 0 => fun s => some ([], s)
  | n + 1 => fun s =>
    match d s with
    | some (x, s) =>
      match count d n s with
      | some (xs, s) => some (x :: xs, s)
      | none => none
    | none => none

end P

open P in
/-- One row line. -/
def rowP : P Row := do
  let c ← anyChar
  expect [' ']
  if c = 'I' then do let i ← nat; expect ['\n']; Pure.pure (.input i)
  else if c = 'C' then do let n ← nat; expect ['\n']; Pure.pure (.const n)
  else if c = 'A' then do let a ← nat; expect [' ']; let b ← nat; expect ['\n']; Pure.pure (.add a b)
  else if c = 'S' then do let a ← nat; expect [' ']; let b ← nat; expect ['\n']; Pure.pure (.sub a b)
  else if c = 'M' then do let a ← nat; expect [' ']; let b ← nat; expect ['\n']; Pure.pure (.mul a b)
  else if c = 'D' then do
    let a ← nat; expect [' ']; let b ← nat; expect [' ']; let m ← nat; expect ['\n']; Pure.pure (.div a b m)
  else if c = 'Z' then do
    let a ← nat; expect [' ']; let b ← nat; expect [' ']; let m ← nat; expect ['\n']; Pure.pure (.zdiv a b m)
  else if c = 'F' then do let k ← nat; expect ['\n']; Pure.pure (.flag k)
  else fail

open P in
/-- One output line. -/
def outP : P (Nat × OMark) := do
  expect ['O', ' ']
  let o ← nat
  expect [' ']
  let c ← anyChar
  expect ['\n']
  if c = '0' then Pure.pure (o, .never) else if c = '1' then Pure.pure (o, .pub) else fail

open P in
/-- The whole text, syntax only. -/
def programP : P Program := do
  expect magic
  expect ['\n']
  let inputs ← nat
  expect [' ']
  let masks ← nat
  expect [' ']
  let rows ← nat
  expect [' ']
  let outputs ← nat
  expect ['\n']
  expect (decimal modulus)
  expect ['\n']
  let rs ← count rowP rows
  let os ← count outP outputs
  Pure.pure ⟨inputs, masks, rs, os⟩

/-- **The V3 parser**: the text's program when the text is exactly a valid program's text. -/
def parseChars (s : List Char) : Option Program :=
  match programP s with
  | some (p, []) => if p.valid then some p else none
  | _ => none

def parse (s : String) : Option Program := parseChars s.toList

/-! ## Round trip -/

section RoundTrip

open P

theorem digitChar_isDigit (d : Nat) (h : d < 10) : isDigit (digitChar d) = true := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem digitChar_toNat (d : Nat) (h : d < 10) : (digitChar d).toNat - 48 = d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem decimal_digits (n : Nat) : ∀ c ∈ decimal n, isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact digitChar_isDigit n (by omega)
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · subst hc
        exact digitChar_isDigit _ (Nat.mod_lt _ (by omega))

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  rw [decimal]
  split <;> simp

theorem value_decimal (n : Nat) : value (decimal n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · simp only [value, List.foldl_cons, List.foldl_nil]
      rw [digitChar_toNat n (by omega)]
      omega
    · next hn =>
      have hv := ih (n / 10) (by omega)
      simp only [value, List.foldl_append, List.foldl_cons, List.foldl_nil] at hv ⊢
      rw [hv, digitChar_toNat _ (Nat.mod_lt _ (by omega))]
      omega

theorem spanDigits_append (ds rest : List Char) (hd : ∀ c ∈ ds, isDigit c = true)
    (hr : ∀ c, rest.head? = some c → isDigit c = false) :
    spanDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c s =>
      have := hr c rfl
      simp [spanDigits, this]
  | cons d ds ih =>
    have h1 := hd d (by simp)
    have h2 := ih (fun c hc => hd c (by simp [hc]))
    simp [spanDigits, h1, h2]

/-- A number followed by a non-digit. -/
theorem nat_decimal (n : Nat) (rest : List Char) (hr : ∀ c, rest.head? = some c → isDigit c = false) :
    nat (decimal n ++ rest) = some (n, rest) := by
  simp only [nat, spanDigits_append (decimal n) rest (decimal_digits n) hr, value_decimal]
  simp [decimal_ne_nil]

theorem expect_append (l rest : List Char) : expect l (l ++ rest) = some ((), rest) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [expect, ih]

theorem nat_space (n : Nat) (rest : List Char) : nat (decimal n ++ ' ' :: rest) = some (n, ' ' :: rest) :=
  nat_decimal n _ (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc; subst hc; decide)

theorem nat_newline (n : Nat) (rest : List Char) : nat (decimal n ++ '\n' :: rest) = some (n, '\n' :: rest) :=
  nat_decimal n _ (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc; subst hc; decide)

theorem expect_one (c : Char) (rest : List Char) : expect [c] (c :: rest) = some ((), rest) := by
  simp [expect]

theorem rowP_chars (r : Row) (rest : List Char) : rowP (line r.chars ++ rest) = some (r, rest) := by
  cases r <;>
    simp [rowP, Row.chars, line, anyChar, expect_one, List.append_assoc, nat_space, nat_newline]

theorem outP_chars (o : Nat × OMark) (rest : List Char) : outP (line (outChars o) ++ rest) = some (o, rest) := by
  obtain ⟨n, m⟩ := o
  cases m <;> simp [outP, outChars, markChar, line, anyChar, expect, List.append_assoc, nat_space]

theorem count_chars {α : Type} (d : P α) (e : α → List Char) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, d (e x ++ s) = some (x, s)) →
      ∀ s, count d l.length ((l.map e).flatten ++ s) = some (l, s)
  | [], _, s => rfl
  | x :: l, h, s => by
    have hx := h x (by simp) ((l.map e).flatten ++ s)
    have hl := count_chars d e l (fun y hy => h y (by simp [hy])) s
    simp only [List.map_cons, List.flatten_cons, List.length_cons, count, List.append_assoc, hx, hl]

theorem programP_chars (p : Program) : programP (chars p) = some (p, []) := by
  have hr := count_chars rowP (fun r => line r.chars) p.rows (fun r _ s => rowP_chars r s)
    ((p.outputs.map fun o => line (outChars o)).flatten)
  have ho := count_chars outP (fun o => line (outChars o)) p.outputs (fun o _ s => outP_chars o s) []
  simp only [List.append_nil] at ho
  simp only [programP, chars, P.bind_apply, P.pure_apply, expect_append, expect_one, nat_space,
    nat_newline, hr, ho]

/-- **Round trip**: a valid program's text parses back to it. -/
theorem parse_render (p : Program) (hp : p.valid = true) : parse (render p) = some p := by
  simp [parse, render, parseChars, programP_chars, hp]

/-- Every program the parser accepts is valid (in particular P-INV (d), `masksOk`). -/
theorem parse_valid (s : String) (p : Program) (h : parse s = some p) : p.valid = true := by
  simp only [parse, parseChars] at h
  split at h
  · split at h
    · next hv => simp only [Option.some.injEq] at h; subst h; exact hv
    · cases h
  · cases h

/-- **P-INV (d) for every loaded program.** -/
theorem parse_masksOk (s : String) (p : Program) (h : parse s = some p) : p.masksOk = true := by
  have := parse_valid s p h
  simp only [Program.valid, Bool.and_eq_true] at this
  exact this.2

/-! ### The parser accepts nothing but rendered texts -/

theorem bind_some {α β : Type} {d : P α} {f : α → P β} {s : List Char} {b : β} {r : List Char}
    (h : (d >>= f) s = some (b, r)) : ∃ a s', d s = some (a, s') ∧ f a s' = some (b, r) := by
  simp only [P.bind_apply] at h
  split at h
  · next a s' hd => exact ⟨a, s', hd, h⟩
  · cases h

theorem expect_inv {l s r : List Char} {u : Unit} (h : expect l s = some (u, r)) : s = l ++ r := by
  induction l generalizing s with
  | nil => simp only [expect, Option.some.injEq, Prod.mk.injEq] at h; simp [h.2]
  | cons c l ih =>
    cases s with
    | nil => simp [expect] at h
    | cons d s =>
      simp only [expect] at h
      split at h
      · next hc => subst hc; simp [ih h]
      · cases h

theorem anyChar_inv {s r : List Char} {c : Char} (h : anyChar s = some (c, r)) : s = c :: r := by
  cases s with
  | nil => simp [anyChar] at h
  | cons d s => simp only [anyChar, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem spanDigits_eq (s : List Char) : (spanDigits s).1 ++ (spanDigits s).2 = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [spanDigits]
    split
    · simp [ih]
    · rfl

theorem nat_inv {s r : List Char} {n : Nat} (h : nat s = some (n, r)) : s = decimal n ++ r := by
  simp only [nat] at h
  split at h
  · next hc =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hc.2, spanDigits_eq]
  · cases h

theorem pure_inv {α : Type} {a b : α} {s r : List Char} (h : (Pure.pure a : P α) s = some (b, r)) :
    a = b ∧ s = r := by
  simp only [P.pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  exact h

set_option hygiene false in
/-- The rest of a row line once its letter is known: numbers and literals, then `pure`. -/
local macro "row_tail" : tactic => `(tactic| (
    repeat (first
      | (obtain ⟨_, _, h3, h⟩ := bind_some h; first | rw [nat_inv h3] | rw [expect_inv h3])
      | (obtain ⟨rfl, rfl⟩ := pure_inv h))
    simp [line, Row.chars]))

theorem fail_inv {α : Type} {s : List Char} {x : α × List Char} (h : (P.fail : P α) s = some x) : False := by
  cases h

theorem rowP_inv {s r : List Char} {row : Row} (h : rowP s = some (row, r)) : s = line row.chars ++ r := by
  obtain ⟨c, s1, h1, h⟩ := bind_some h
  obtain ⟨_, s2, h2, h⟩ := bind_some h
  rw [anyChar_inv h1, expect_inv h2]
  clear h1 h2
  by_cases hI : c = 'I'
  · subst hI; rw [if_pos rfl] at h; row_tail
  rw [if_neg hI] at h
  by_cases hC : c = 'C'
  · subst hC; rw [if_pos rfl] at h; row_tail
  rw [if_neg hC] at h
  by_cases hA : c = 'A'
  · subst hA; rw [if_pos rfl] at h; row_tail
  rw [if_neg hA] at h
  by_cases hS : c = 'S'
  · subst hS; rw [if_pos rfl] at h; row_tail
  rw [if_neg hS] at h
  by_cases hM : c = 'M'
  · subst hM; rw [if_pos rfl] at h; row_tail
  rw [if_neg hM] at h
  by_cases hD : c = 'D'
  · subst hD; rw [if_pos rfl] at h; row_tail
  rw [if_neg hD] at h
  by_cases hZ : c = 'Z'
  · subst hZ; rw [if_pos rfl] at h; row_tail
  rw [if_neg hZ] at h
  by_cases hF : c = 'F'
  · subst hF; rw [if_pos rfl] at h; row_tail
  rw [if_neg hF] at h
  exact (fail_inv h).elim

theorem outP_inv {s r : List Char} {o : Nat × OMark} (h : outP s = some (o, r)) : s = line (outChars o) ++ r := by
  obtain ⟨_, s1, h1, h⟩ := bind_some h
  obtain ⟨n, s2, h2, h⟩ := bind_some h
  obtain ⟨_, s3, h3, h⟩ := bind_some h
  obtain ⟨c, s4, h4, h⟩ := bind_some h
  obtain ⟨_, s5, h5, h⟩ := bind_some h
  rw [expect_inv h1, nat_inv h2, expect_inv h3, anyChar_inv h4, expect_inv h5]
  by_cases h0 : c = '0'
  · subst h0
    rw [if_pos rfl] at h
    obtain ⟨rfl, rfl⟩ := pure_inv h
    simp [line, outChars, markChar]
  rw [if_neg h0] at h
  by_cases h1 : c = '1'
  · subst h1
    rw [if_pos rfl] at h
    obtain ⟨rfl, rfl⟩ := pure_inv h
    simp [line, outChars, markChar]
  rw [if_neg h1] at h
  exact (fail_inv h).elim

theorem count_inv {α : Type} (d : P α) (e : α → List Char)
    (hd : ∀ s x r, d s = some (x, r) → s = e x ++ r) :
    ∀ (n : Nat) (s r : List Char) (xs : List α), count d n s = some (xs, r) →
      s = (xs.map e).flatten ++ r ∧ xs.length = n
  | 0, s, r, xs, h => by
    simp only [count, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, s, r, xs, h => by
    simp only [count] at h
    split at h
    · next x s1 h1 =>
      split at h
      · next ys s2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e2, l2⟩ := count_inv d e hd n s1 s2 ys h2
        simp [hd _ _ _ h1, e2, l2]
      · cases h
    · cases h

theorem programP_inv {s r : List Char} {p : Program} (h : programP s = some (p, r)) : s = chars p ++ r := by
  obtain ⟨_, s1, h1, h⟩ := bind_some h
  obtain ⟨_, s2, h2, h⟩ := bind_some h
  obtain ⟨i, s3, h3, h⟩ := bind_some h
  obtain ⟨_, s4, h4, h⟩ := bind_some h
  obtain ⟨m, s5, h5, h⟩ := bind_some h
  obtain ⟨_, s6, h6, h⟩ := bind_some h
  obtain ⟨nr, s7, h7, h⟩ := bind_some h
  obtain ⟨_, s8, h8, h⟩ := bind_some h
  obtain ⟨no, s9, h9, h⟩ := bind_some h
  obtain ⟨_, s10, h10, h⟩ := bind_some h
  obtain ⟨_, s11, h11, h⟩ := bind_some h
  obtain ⟨_, s12, h12, h⟩ := bind_some h
  obtain ⟨rs, s13, h13, h⟩ := bind_some h
  obtain ⟨os, s14, h14, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := pure_inv h
  obtain ⟨e13, l13⟩ := count_inv rowP (fun r => line r.chars) (fun _ _ _ h => rowP_inv h) nr s12 s13 rs h13
  obtain ⟨e14, l14⟩ := count_inv outP (fun o => line (outChars o)) (fun _ _ _ h => outP_inv h) no s13 s14 os h14
  rw [expect_inv h1, expect_inv h2, nat_inv h3, expect_inv h4, nat_inv h5, expect_inv h6, nat_inv h7,
    expect_inv h8, nat_inv h9, expect_inv h10, expect_inv h11, expect_inv h12, e13, e14]
  subst l13 l14
  simp [chars]

/-- **The parser accepts exactly the rendered valid programs**: a text it accepts is the text of
its program (so a pinned file is one program, and one program has one file). -/
theorem render_parse (s : String) (p : Program) (h : parse s = some p) : render p = s := by
  simp only [parse, parseChars] at h
  split at h
  · next p' hp =>
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      have e := programP_inv hp
      simp only [List.append_nil] at e
      simp only [render, ← e, String.ofList_toList]
    · cases h
  · cases h

end RoundTrip

/-! ## P-FIELDPROG: which outputs are public -/

/-- The role a program's author declares for an output: a secret result, a public value both
parties open (`check`: a check value that must be zero, or another value the flow opens by
design, such as a masked point), or a zero flag (an `F` row). -/
inductive Role where
  | secret
  | check
  | flag
  deriving DecidableEq, Repr

def Role.mark : Role → OMark
  | .secret => .never
  | .check => .pub
  | .flag => .pub

/-- **P-FIELDPROG, as a check**: the program has one output per declared role, each output's mark
is its role's (public exactly for the declared checks and flags), and every flag output is an `F`
row. -/
def Program.declares (p : Program) (roles : List Role) : Bool :=
  p.outputs.map (·.2) == roles.map Role.mark &&
    (p.outputs.zip roles).all fun e =>
      e.2 != .flag || match p.rows[e.1.1]? with
        | some (.flag _) => true
        | _ => false

/-- The positions of the public marks of a list of marks. -/
def publicPositions (marks : List OMark) : List Nat :=
  (marks.zipIdx.filter fun e => e.1 == .pub).map (·.2)

/-- The positions of the public outputs. -/
def Program.publicOutputs (p : Program) : List Nat := publicPositions (p.outputs.map (·.2))

/-- A program that declares `roles` has its public outputs exactly at the declared checks and
flags. -/
theorem declares_publicOutputs (p : Program) (roles : List Role) (h : p.declares roles = true) :
    p.publicOutputs = publicPositions (roles.map Role.mark) := by
  simp only [Program.declares, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Program.publicOutputs, h.1]

/-- The marks of a list of roles, as `ofArtifact` takes them. -/
def marksOf (roles : List Role) (j : Nat) : OMark := (roles.getD j .secret).mark

/-- **P-FIELDPROG for every translated program**: the V3 program of an artifact with one output
per declared role (no flags: FieldDag has no `Z` rows) declares those roles. -/
theorem ofArtifact_declares (inputs : Nat) (a : FieldDag.MultiArtifact) (roles : List Role)
    (hl : a.outputs.length = roles.length) (hf : Role.flag ∉ roles) :
    (ofArtifact inputs a (marksOf roles)).declares roles = true := by
  have hm : ((a.outputs.zipIdx.map fun e => (e.1, marksOf roles e.2)).map (·.2)) = roles.map Role.mark := by
    apply List.ext_getElem
    · simp [hl]
    · intro i h1 h2
      simp only [List.length_map, List.length_zipIdx] at h1
      simp [marksOf, List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ h1)]
  simp only [Program.declares, ofArtifact, hm, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro e he
  have hr : e.2 ∈ roles := (List.of_mem_zip he).2
  have hne : e.2 ≠ .flag := fun h => hf (h ▸ hr)
  simp [hne]

/-! ## A natively V3 program: the masked quotient with its zero flag

`x25519_fast.h` (`quotient`, `evaluate_many`) and `hinted_points.h` divide `x` by `z` through
`field-mask-pair` (`x·r`, `z·r`) and a C++ opening and division, with `r` from `RAND_bytes`. In V3
that is one program: a `Z` row with an explicit mask and the `F` row of its zero flag. FieldDag
cannot express it (no zero-tolerant division), so it is written here as rows; its properties are
checked by `decide` on the rows (the per-program pattern of P-INV (d) and P-FIELDPROG; for
programs compiled from FieldDag, `ofArtifact_masksOk` and `ofArtifact_declares` hold for every
artifact, so no per-program computation is needed). -/

/-- `x / z` (0 when `z = 0`) and the public zero flag. Inputs `x` (0), `z` (1); one mask. -/
def quotient : Program where
  inputs := 2
  masks := 1
  rows := [.input 0, .input 1, .zdiv 0 1 0, .flag 2]
  outputs := [(2, .never), (3, .pub)]

/-- The quotient program is well formed (so it renders and parses back, `parse_render`). -/
theorem quotient_valid : quotient.valid = true := by decide

/-- **P-INV (d) for the quotient program**, by `decide` on its rows. -/
theorem quotient_masksOk : quotient.masksOk = true := by decide

/-- **P-FIELDPROG for the quotient program**, by `decide`: output 0 is secret, output 1 is the
declared zero flag (an `F` row), and it is the only public output. -/
theorem quotient_declares : quotient.declares [.secret, .flag] = true ∧ quotient.publicOutputs = [1] := by
  decide

/-- The quotient program's semantics, row by row: one opening, `z·m`. -/
theorem quotient_eval (input mask : Nat → F) :
    eval quotient input mask =
      some ([if input 1 * mask 0 = 0 then ofNat 0 else input 0 * mask 0 * inverse (input 1 * mask 0),
             if input 1 * mask 0 = 0 then ofNat 1 else ofNat 0], [input 1 * mask 0]) := by
  rw [← inverseFast_eq]
  rfl

theorem inverse_zero : inverse 0 = 0 := by
  have h : modulus - 2 = (modulus - 3) + 1 := by decide
  rw [inverse, h, FieldDag.power]
  grind

/-- **What the quotient computes** (with a nonzero mask): `x·z⁻¹` (which is 0 for `z = 0`, as
FieldDag's `div`), and the flag 1 exactly when `z = 0`. The released opening is `z·m`, uniform
for `z ≠ 0` (`opening_bijective`) and 0 for `z = 0`. -/
theorem quotient_spec (hinv : FieldInverse) (input mask : Nat → F) (hm : mask 0 ≠ 0) :
    eval quotient input mask =
      some ([input 0 * inverse (input 1), if input 1 = 0 then ofNat 1 else ofNat 0], [input 1 * mask 0]) := by
  rw [quotient_eval]
  by_cases hz : input 1 = 0
  · rw [hz]
    have ho : (0 : F) * mask 0 = 0 := by grind
    have hx : input 0 * (0 : F) = ofNat 0 := by rw [show ofNat 0 = (0 : F) from rfl]; grind
    simp only [ho, if_true, inverse_zero, hx]
  · have ho := mul_ne_zero hinv hz hm
    simp only [ho, hz, if_false, masked_div hinv _ _ _ ho]

#print axioms parse_render
#print axioms render_parse
#print axioms eval_ofArtifact
#print axioms eval_ofArtifact_some
#print axioms eval_compileAll
#print axioms ofArtifact_masksOk
#print axioms ofArtifact_declares
#print axioms quotient_declares
#print axioms quotient_spec

end TlsMpc.FieldDag.V3
