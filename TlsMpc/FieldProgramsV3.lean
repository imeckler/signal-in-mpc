import TlsMpc.FieldDagV3
import TlsMpc.FieldBits
import TlsMpc.EdwardsShare

/-!
# The V3 field programs: declarations, P-FIELDPROG and P-INV (d) per program

REORGANIZATION_PLAN.md 5.5 and 7.1 (stage S9). A declaration names a field program, its data
inputs, its FieldDag source expressions and the ROLE of each output (`secret`, or `check`: a value
both parties open). Its V3 program is `ofArtifact` of the validated compilation, with the roles'
marks (`Decl.program`); the emitter prints exactly that (`EmitWordMask`, mode `v3`).

THE GENERAL STATEMENTS (any declaration, any compilation the validator accepts):
  * `Decl.checks` — P-INV (d) (every mask feeds exactly one `D` row) and P-FIELDPROG, structural
    (the public outputs are exactly the declared checks: `declares`, `publicOutputs`).
  * `Decl.values` — P-FIELDPROG, values: a run that does not abort outputs the source
    expressions' values (`FieldDagV3.eval_compileAll`, so every theorem about the expressions
    carries over), under `FieldInverse`.
THE PATTERN PER PROGRAM (here for the two smallest exported programs, `field-bit-check` and
`edwards-on-curve`): `ok` by `decide` on the declaration (a few list comparisons: its cost is the
size of the role list, not of the DAG, which is never computed in the kernel: `compileAll` uses
native hashing, `mixHash`, which the kernel cannot evaluate, so a per-program `decide` on a
COMPILED DAG is not possible; the generic theorems make it unnecessary), the public positions by
`rfl`, and the values by the expressions' own lemmas. A natively V3 program (rows written by hand,
such as `FieldDagV3.quotient`) is checked by `decide` on its rows instead.

Emitter isolation (rule 4): no `TlsMpc/Node` import; `EmitWordMask` imports this module.
-/

namespace TlsMpc.FieldProgramsV3

open TlsMpc.FieldDag TlsMpc.FieldDag.V3

/-- A V3 field program as exported: its name (the emitter's mode and the file name), its data
inputs, its source expressions and the role of each output. -/
structure Decl where
  name : String
  inputs : Nat
  exprs : List Expr
  roles : List Role

/-- One role per expression, and no flag (FieldDag has no `Z` rows). -/
def Decl.ok (d : Decl) : Bool := d.exprs.length == d.roles.length && !d.roles.contains .flag

/-- The V3 program of a declaration: the validated compilation of its expressions, its divisions
as `D` rows with masks in order, its outputs marked by their roles. -/
def Decl.program (d : Decl) : Option Program :=
  (compileAll d.exprs).map fun a => ofArtifact d.inputs a (marksOf d.roles)

theorem Decl.program_eq {d : Decl} {p : Program} (hp : d.program = some p) :
    ∃ a, compileAll d.exprs = some a ∧ p = ofArtifact d.inputs a (marksOf d.roles) := by
  simp only [Decl.program, Option.map_eq_some_iff] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  exact ⟨a, ha, rfl⟩

/-- **P-INV (d) and P-FIELDPROG (structural), for every declaration**: every mask feeds exactly
one `D` row, and the outputs marked public are exactly the declared checks. -/
theorem Decl.checks (d : Decl) (hd : d.ok = true) (p : Program) (hp : d.program = some p) :
    p.masksOk = true ∧ p.declares d.roles = true ∧
      p.publicOutputs = publicPositions (d.roles.map Role.mark) := by
  obtain ⟨a, ha, rfl⟩ := Decl.program_eq hp
  simp only [Decl.ok, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hd
  have hl : a.outputs.length = d.roles.length := by
    have := congrArg List.length (FieldDag.compileAll_correct d.exprs a ha (fun _ => 0))
    simp only [List.length_map] at this
    rw [this, hd.1]
  have hdecl := ofArtifact_declares d.inputs a d.roles hl hd.2
  exact ⟨ofArtifact_masksOk _ _ _, hdecl, declares_publicOutputs _ _ hdecl⟩

/-- **P-FIELDPROG (values), for every declaration**: a run of its V3 program that does not abort
outputs the source expressions' values. -/
theorem Decl.values (hinv : FieldInverse) (d : Decl) (p : Program) (hp : d.program = some p)
    (input mask : Nat → F) (outs opened : List F) (h : V3.eval p input mask = some (outs, opened)) :
    outs = d.exprs.map (Expr.eval input) := by
  obtain ⟨a, ha, rfl⟩ := Decl.program_eq hp
  exact eval_compileAll hinv d.inputs d.exprs a ha _ input mask outs opened h

/-! ## Per program: the two smallest exported programs -/

/-- `field-bit-check`: `b·(b − 1)`, opened by both parties (zero exactly on bits). -/
def bitCheck : Decl := ⟨"field-bit-check", 1, [FieldBits.bitCheck], [.check]⟩

/-- `edwards-on-curve`: the scaled curve equation of a party's point, opened by both parties. -/
def onCurve : Decl := ⟨"edwards-on-curve", 2, [EdwardsShare.onCurve], [.check]⟩

theorem bitCheck_ok : bitCheck.ok = true := by decide
theorem onCurve_ok : onCurve.ok = true := by decide

/-- **P-INV (d) and P-FIELDPROG for `field-bit-check`**: no mask is used twice, its only output
is public and is the declared check, and (with `FieldInverse`) a run outputs `b·(b − 1)`, which is
0 for a bit input (`FieldBits.bitCheck_bit`): an honest party's check reveals nothing. -/
theorem bitCheck_fieldprog (hinv : FieldInverse) (p : Program) (hp : bitCheck.program = some p) :
    p.masksOk = true ∧ p.declares [.check] = true ∧ p.publicOutputs = [0] ∧
      ∀ input mask outs opened, V3.eval p input mask = some (outs, opened) →
        outs = [input 0 * (input 0 - ofNat 1)] ∧
        ∀ b : Bool, input 0 = X25519.bitValue b → outs = [0] := by
  obtain ⟨h1, h2, h3⟩ := Decl.checks bitCheck bitCheck_ok p hp
  refine ⟨h1, h2, h3, fun input mask outs opened h => ?_⟩
  have hv := Decl.values hinv bitCheck p hp input mask outs opened h
  refine ⟨hv, fun b hb => ?_⟩
  rw [hv]
  have := FieldBits.bitCheck_bit input b hb
  simp only [List.map_cons, List.map_nil, bitCheck] at this ⊢
  rw [this]

/-- **P-INV (d) and P-FIELDPROG for `edwards-on-curve`**: its only output is public and is the
declared check, `121666·(y² − x² − 1) + 121665·x²·y²` (`EdwardsShare.onCurve_eval`). -/
theorem onCurve_fieldprog (hinv : FieldInverse) (p : Program) (hp : onCurve.program = some p) :
    p.masksOk = true ∧ p.declares [.check] = true ∧ p.publicOutputs = [0] ∧
      ∀ input mask outs opened, V3.eval p input mask = some (outs, opened) →
        outs = [ofNat 121666 * (input 1 * input 1 - input 0 * input 0 - ofNat 1) +
          ofNat 121665 * (input 0 * input 0 * (input 1 * input 1))] := by
  obtain ⟨h1, h2, h3⟩ := Decl.checks onCurve onCurve_ok p hp
  refine ⟨h1, h2, h3, fun input mask outs opened h => ?_⟩
  rw [Decl.values hinv onCurve p hp input mask outs opened h]
  rfl

#print axioms Decl.checks
#print axioms bitCheck_fieldprog
#print axioms onCurve_fieldprog

end TlsMpc.FieldProgramsV3
