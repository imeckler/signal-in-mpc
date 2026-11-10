import Std.Tactic

/-!
Original-output equivalence for the tiny-kernel padding transformation of
`pad_program.h`.

The model mirrors the C++ by inspection (it is not extracted from it): a dense
SSA program whose wire `numInputs + i` is the output of gate `i`; padding inserts
`2*d` fresh inputs after the original inputs, shifts every original non-input
wire by `2*d`, appends `d` AND gates over the fresh inputs and appends their
outputs after the original outputs. Value semantics only: no statement about the
backend's checks, about secrecy of the dummy inputs, or about pruning.
-/
namespace EmpHybrid.Padding

inductive Gate where
  | and (a b : Nat)
  | xor (a b : Nat)
  | not (a : Nat)
  | const (v : Bool)

structure Program where
  numInputs : Nat
  gates : List Gate
  outputs : List Nat

/-- Total lookup; out-of-range wires read `false` (excluded by well-formedness). -/
def nth : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, i + 1 => nth bs i

def Gate.eval (env : List Bool) : Gate → Bool
  | .and a b => nth env a && nth env b
  | .xor a b => nth env a != nth env b
  | .not a => !(nth env a)
  | .const v => v

/-- Values produced by a gate list, each gate seeing all earlier wires. -/
def vals (env : List Bool) : List Gate → List Bool
  | [] => []
  | g :: gs => g.eval env :: vals (env ++ [g.eval env]) gs

def Program.eval (p : Program) (inputs : List Bool) : List Bool :=
  p.outputs.map (nth (inputs ++ vals inputs p.gates))

/-- Every operand refers to an earlier wire. -/
def Gate.wf (bound : Nat) : Gate → Prop
  | .and a b => a < bound ∧ b < bound
  | .xor a b => a < bound ∧ b < bound
  | .not a => a < bound
  | .const _ => True

def gatesWf (bound : Nat) : List Gate → Prop
  | [] => True
  | g :: gs => g.wf bound ∧ gatesWf (bound + 1) gs

structure Program.wf (p : Program) : Prop where
  gates : gatesWf p.numInputs p.gates
  outputs : ∀ o ∈ p.outputs, o < p.numInputs + p.gates.length

def remap (n k w : Nat) : Nat := if w < n then w else w + k

def Gate.remap (n k : Nat) : Gate → Gate
  | .and a b => .and (Padding.remap n k a) (Padding.remap n k b)
  | .xor a b => .xor (Padding.remap n k a) (Padding.remap n k b)
  | .not a => .not (Padding.remap n k a)
  | .const v => .const v

/-- `pad_program` with `d` dummy ANDs. -/
def pad (p : Program) (d : Nat) : Program where
  numInputs := p.numInputs + 2 * d
  gates := p.gates.map (Gate.remap p.numInputs (2 * d)) ++
    (List.range d).map (fun i => Gate.and (p.numInputs + i) (p.numInputs + d + i))
  outputs := p.outputs.map (remap p.numInputs (2 * d)) ++
    (List.range d).map (fun i => p.numInputs + 2 * d + p.gates.length + i)

theorem nth_append_left (l r : List Bool) (i : Nat) (h : i < l.length) :
    nth (l ++ r) i = nth l i := by
  induction l generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => simp [nth]
    | succ j =>
      simp only [List.cons_append, nth]
      exact ih j (by simpa using h)

theorem nth_append_right (l r : List Bool) (j : Nat) :
    nth (l ++ r) (l.length + j) = nth r j := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    have : (b :: bs).length + j = (bs.length + j) + 1 := by simp; omega
    rw [this]
    simp only [List.cons_append, nth]
    exact ih

/-- A remapped wire reads, in the padded environment, what the wire read originally. -/
theorem nth_remap (xs ds vs : List Bool) (w : Nat) (h : w < xs.length + vs.length) :
    nth (xs ++ ds ++ vs) (remap xs.length ds.length w) = nth (xs ++ vs) w := by
  unfold remap
  by_cases hw : w < xs.length
  · simp only [hw, if_true]
    rw [List.append_assoc, nth_append_left _ _ _ hw, nth_append_left _ _ _ hw]
  · simp only [hw, if_false]
    obtain ⟨j, rfl⟩ : ∃ j, w = xs.length + j := ⟨w - xs.length, by omega⟩
    rw [nth_append_right]
    have : xs.length + j + ds.length = (xs ++ ds).length + j := by simp; omega
    rw [this, nth_append_right]

theorem eval_remap (xs ds vs : List Bool) (g : Gate) (h : g.wf (xs.length + vs.length)) :
    (g.remap xs.length ds.length).eval (xs ++ ds ++ vs) = g.eval (xs ++ vs) := by
  cases g with
  | and a b => simp only [Gate.remap, Gate.eval, nth_remap xs ds vs a h.1, nth_remap xs ds vs b h.2]
  | xor a b => simp only [Gate.remap, Gate.eval, nth_remap xs ds vs a h.1, nth_remap xs ds vs b h.2]
  | not a => simp only [Gate.remap, Gate.eval, nth_remap xs ds vs a h]
  | const v => rfl

/-- The remapped original gates compute exactly the original gate values. -/
theorem vals_remap (xs ds : List Bool) (gs : List Gate) (vs : List Bool)
    (h : gatesWf (xs.length + vs.length) gs) :
    vals (xs ++ ds ++ vs) (gs.map (Gate.remap xs.length ds.length)) = vals (xs ++ vs) gs := by
  induction gs generalizing vs with
  | nil => rfl
  | cons g gs ih =>
    have hg := eval_remap xs ds vs g h.1
    have hrest : gatesWf (xs.length + (vs ++ [g.eval (xs ++ vs)]).length) gs := by
      simpa [Nat.add_assoc] using h.2
    have := ih (vs ++ [g.eval (xs ++ vs)]) hrest
    simp only [List.map_cons, vals]
    rw [hg]
    congr 1
    simpa [List.append_assoc] using this

theorem vals_length (env : List Bool) (gs : List Gate) : (vals env gs).length = gs.length := by
  induction gs generalizing env with
  | nil => rfl
  | cons g gs ih => simp [vals, ih]

theorem vals_append (env : List Bool) (gs hs : List Gate) :
    vals env (gs ++ hs) = vals env gs ++ vals (env ++ vals env gs) hs := by
  induction gs generalizing env with
  | nil => simp [vals]
  | cons g gs ih => simp [vals, ih, List.append_assoc]

/-- Padding leaves every original output unchanged, for any dummy-input values. -/
theorem pad_original_outputs (p : Program) (d : Nat) (xs ds : List Bool)
    (hp : p.wf) (hxs : xs.length = p.numInputs) (hds : ds.length = 2 * d) :
    ((pad p d).eval (xs ++ ds)).take p.outputs.length = p.eval xs := by
  obtain ⟨n, gates, outputs⟩ := p
  simp only at hxs
  subst hxs
  have hg : gatesWf xs.length gates := hp.gates
  have ho : ∀ o ∈ outputs, o < xs.length + gates.length := hp.outputs
  have hv : vals (xs ++ ds) (gates.map (Gate.remap xs.length (2 * d))) = vals xs gates := by
    have := vals_remap xs ds gates [] (by simpa using hg)
    simpa [hds] using this
  simp only [Program.eval, pad, List.map_append, vals_append, hv]
  rw [List.take_left' (by simp)]
  simp only [List.map_map]
  apply List.map_congr_left
  intro o hmem
  have hlt := ho o hmem
  simp only [Function.comp]
  rw [← List.append_assoc (xs ++ ds), nth_append_left]
  · have := nth_remap xs ds (vals xs gates) o (by simpa [vals_length] using hlt)
    simpa [hds] using this
  · unfold remap
    simp only [List.length_append, vals_length, hds]
    split <;> omega

/-- Zero dummies is the identity transformation on outputs. -/
theorem pad_zero (p : Program) (xs : List Bool) (hp : p.wf) (hxs : xs.length = p.numInputs) :
    (pad p 0).eval xs = p.eval xs := by
  have h := pad_original_outputs p 0 xs [] hp hxs rfl
  rw [List.append_nil] at h
  rw [← h]
  symm
  apply List.take_of_length_le
  simp [pad, Program.eval]

#print axioms pad_original_outputs
#print axioms pad_zero
end EmpHybrid.Padding
