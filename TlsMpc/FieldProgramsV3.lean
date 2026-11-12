import TlsMpc.FieldDagV3
import TlsMpc.FieldBits
import TlsMpc.X25519Fast
import TlsMpc.EdwardsShare
import TlsMpc.EdwardsAffine
import TlsMpc.EstablishField
import TlsMpc.ReceiveField
import TlsMpc.EdwardsHinted

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

/-! ## Every exported V3 program (the emitter's mode `v3 NAME`)

The roles say which outputs the C++ flows of today open publicly (`checked_open` to both parties),
surveyed per program from `handshake_backend/EmpHybridWork` (FIELD_PROGRAMS_V3.md has the
evidence): those are `check` (public); everything else is `secret`. `field-mask-pair` has no V3
form: its job (opening `z·r` and dividing in C++) is the `Z` row of `field-quotient`
(`FieldDagV3.quotient`). Outputs that a flow opens only after multiplying by a mask through the
quotient stay `secret` (the quotient opens `z·m` itself). `xeddsa-recover`'s outputs are opened
today only when its input is public (the server key), where S11 evaluates the Lean definition
locally instead, so they are `secret` here. -/

/-- The first `k` of `n` outputs public, the rest secret. -/
def firstPublic (k n : Nat) : List Role := List.replicate k .check ++ List.replicate (n - k) .secret

def secretAll (n : Nat) : List Role := List.replicate n .secret

/-- A declaration whose first `k` outputs are public. -/
def first (name : String) (inputs : Nat) (exprs : List Expr) (k : Nat) : Decl :=
  ⟨name, inputs, exprs, firstPublic k exprs.length⟩

/-- The declaration of an exported program, by name. -/
def find : String → Option Decl
  | "field-bit-check" => some bitCheck
  | "field-bit-xor" => some (first "field-bit-xor" 2 [FieldBits.bitXor] 0)
  | "field-recompose" => some (first "field-recompose" 256 [FieldBits.recompose] 1)
  | "x25519-fast" => some (first "x25519-fast" 257 X25519Fast.exprs 0)
  | "edwards-on-curve" => some onCurve
  | "edwards-add-u" => some (first "edwards-add-u" 4 EdwardsShare.addU 0)
  | "edwards-prepare" =>
    some (first "edwards-prepare" (2 + 2 * EdwardsAffine.scalarBits) EdwardsAffine.prepare EdwardsAffine.prepareChecks)
  | "edwards-offset-sum" => some (first "edwards-offset-sum" (2 + 3 * EdwardsAffine.windows) EdwardsAffine.offsetSum 0)
  | "xeddsa-recover" => some (first "xeddsa-recover" 1 EstablishField.recover 0)
  | "xeddsa-check" => some (first "xeddsa-check" 512 EstablishField.check 0)
  | "receive-torsion" => some (first "receive-torsion" 2 ReceiveField.torsion 0)
  -- w (opened after the checks), the two bit checks, the two curve checks; b secret
  | "lift-open" => some ⟨"lift-open", 8, EdwardsHinted.liftOpen (), firstPublic 5 6⟩
  -- valid (opened by Hinted::prepare), the point (secret), Z = P + M_A + M_B (opened)
  | "lift-point" => some ⟨"lift-point", 9, EdwardsHinted.liftPoint (), [.check, .secret, .secret, .check, .check]⟩
  | "edwards-prepare-hinted" =>
    some (first "edwards-prepare-hinted" EdwardsHinted.prepareInputs (EdwardsHinted.prepareHinted ())
      EdwardsHinted.prepareHintedChecks)
  | "edwards-offset-sum-fast" =>
    some (first "edwards-offset-sum-fast" (2 + 3 * EdwardsAffine.windows) (EdwardsHinted.offsetSumFast ()) 0)
  | "edwards-bit-table" =>
    some (first "edwards-bit-table" EdwardsHinted.bitTableInputs (EdwardsHinted.bitTable ())
      (2 * (EdwardsAffine.windows - 1)))
  | "edwards-bit-sum" => some (first "edwards-bit-sum" EdwardsHinted.bitSumInputs (EdwardsHinted.bitSum ()) 0)
  | "edwards-affine-bit-sum" =>
    some (first "edwards-affine-bit-sum" EdwardsHinted.affineBitSumInputs (EdwardsHinted.affineBitSum ()) 0)
  | "edwards-signature-sum" =>
    some (first "edwards-signature-sum" EdwardsHinted.signatureSumInputs (EdwardsHinted.signatureSum ()) 0)
  | "edwards-torsion-hinted" => some (first "edwards-torsion-hinted" 7 (EdwardsHinted.torsionHinted ()) 0)
  | _ => none

/-- Every name `find` knows, and the natively V3 `field-quotient` (the export's list). -/
def names : List String :=
  ["field-quotient", "field-bit-check", "field-bit-xor", "field-recompose", "x25519-fast", "edwards-on-curve",
   "edwards-add-u", "edwards-prepare", "edwards-offset-sum", "xeddsa-recover", "xeddsa-check", "receive-torsion",
   "lift-open", "lift-point", "edwards-prepare-hinted", "edwards-offset-sum-fast", "edwards-bit-table",
   "edwards-bit-sum", "edwards-affine-bit-sum", "edwards-signature-sum", "edwards-torsion-hinted"]

/-- **The V3 text of an exported program** (what `EmitWordMask v3 NAME` prints): the declaration
must be `ok`, its expressions must pass FieldDag's validator, and the program must be valid
(`renderValid`), so the text parses back to it (`parse_render`) and `Decl.checks` /
`Decl.values` apply to it. -/
def v3Text (name : String) : Except String String :=
  if name = "field-quotient" then renderValid quotient
  else match find name with
    | none => .error "unknown V3 field program"
    | some d =>
      if !d.ok then .error "V3 declaration: one role per output, no flag"
      else match d.program with
        | none => .error "field program failed its translation validator"
        | some p => renderValid p

theorem v3Text_quotient : v3Text "field-quotient" = .ok (render quotient) := by
  simp only [v3Text, if_true, renderValid, quotient_valid, if_true]

/-- **What an exported text is**: the rendering of a valid program that satisfies P-INV (d) and
P-FIELDPROG for its declaration (`Decl.checks`), or of `quotient`. -/
theorem v3Text_spec (name s : String) (h : v3Text name = .ok s) :
    s = render quotient ∨
      ∃ d p, find name = some d ∧ d.program = some p ∧ s = render p ∧ p.valid = true ∧
        p.masksOk = true ∧ p.declares d.roles = true := by
  simp only [v3Text] at h
  split at h
  · left
    simp only [renderValid] at h
    split at h
    · exact (Except.ok.inj h).symm
    · cases h
  · right
    split at h
    · cases h
    · next d hd =>
      split at h
      · cases h
      · next hok =>
        split at h
        · cases h
        · next p hp =>
          simp only [renderValid] at h
          split at h
          · next hv =>
            obtain ⟨h1, h2, -⟩ := Decl.checks d (by simpa using hok) p hp
            exact ⟨d, p, hd, hp, (Except.ok.inj h).symm, hv, h1, h2⟩
          · cases h

#print axioms Decl.checks
#print axioms bitCheck_fieldprog
#print axioms onCurve_fieldprog
#print axioms v3Text_spec

end TlsMpc.FieldProgramsV3
