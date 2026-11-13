import TlsMpc.FlatLowering
import TlsMpc.HybridKernels

/-!
# A kernel's flat circuit and layout file, as the emitters write them (T2, proof track P3)

The four kernel emitters (`flat_kernel_emitter`, `bundle_slot_emitter`, `ceremony_kernel_emitter`,
`kem_kernel_emitter`) each carried an identical copy of `selection`, `fieldName`, `layoutText` and
`lowerKernel`; they now share these. The definitions print exactly what the copies printed:
`layoutText` is the same `++` chains (`layoutText_eq_before`, against the former definition kept
here verbatim as `layoutTextBefore`), and `fieldName` is the same test (non-empty, alphanumeric)
read off the characters.

PROVED (standard axioms only):
* `parseLayout_layoutText`: a loader's reading of the layout file (`parseLayout`:
  `EMP_HYBRID_KERNEL_LAYOUT_V1`, then `I NAME BITS` rows, then `O NAME BITS MARK` rows) gives back
  exactly the kernel's declared input fields (name, bits) and output fields (name, bits, open mark),
  in order, whenever the names are alphanumeric (which `lowerKernel` checks).
* `openCode_spec`: the open mark is 1 exactly for an output marked `opened` with no single
  audience, 2 / 3 exactly for an output to party 1 / 2, and 0 for a private one.
* `lowerKernel_loaded`: if `lowerKernel k` returns `flat`, the circuit text the printer writes
  parses back to `flat` (`FlatLowering.parseFlat_render`), the layout file parses back to the
  kernel's fields and marks, and `flat` is `lowerExpr` of the kernel's joined outputs (so
  `FlatLowering.lowerExpr_loaded`: output `k` carries bit `chosen[k]` of the joined value).

NOT PROVED: that `selection` maps each named output bit to the right bit of the joined value (the
emitter's arithmetic); that the engines' loaders read the files as `parseFlat`/`parseLayout` do.
-/
namespace TlsMpc.FlatKernelLayout
open Std.Tactic.BVDecide
open TlsMpc.FlatLowering (expectLit parseNat expectLit_append parseNat_digits noDigit_space noDigit_newline
  toList_toString)

/-- For every output bit, in field order, its bit index in the joined value. `byteCount` is
the number of output bytes of all fields together; byte 0 is the most significant byte of
the joined value. -/
def selection (fields : List HybridKernel.Output) (byteCount : Nat) :
    Except String (Array (Fin (8 * byteCount))) := do
  let mut chosen : Array (Fin (8 * byteCount)) := #[]
  let mut offset := 0
  for field in fields do
    unless field.bits ≤ 8 * field.value.length && 0 < field.bits do
      throw s!"output field {field.name} width"
    for bit in List.range field.bits do
      let i := 8 * offset + bit
      if h : i < 8 * byteCount then
        chosen := chosen.push ⟨8 * (byteCount - 1 - i / 8) + i % 8, by omega⟩
      else throw "output index"
    offset := offset + field.value.length
  pure chosen

/-- A field name the layout file can carry: non-empty and alphanumeric (the same test as
`!name.isEmpty && name.all Char.isAlphanum`, read off the characters). -/
def fieldName (name : String) : Bool := !name.toList.isEmpty && name.toList.all Char.isAlphanum

/-- The open mark of an output row: 2 / 3 when it may be opened to party 1 / 2 only, 1 when it is
opened to both, 0 when it stays private. -/
def openCode (o : HybridKernel.Output) : Nat :=
  if o.audience == 1 then 2 else if o.audience == 2 then 3 else if o.opened then 1 else 0

def inputRow (f : String × HybridKernel.Shape) : String := "I " ++ f.1 ++ " " ++ toString f.2.bits ++ "\n"

def outputRow (o : HybridKernel.Output) : String :=
  "O " ++ o.name ++ " " ++ toString o.bits ++ " " ++ toString (openCode o) ++ "\n"

/-- The layout file (`EMP_HYBRID_KERNEL_LAYOUT_V1`), from the kernel's declared fields. -/
def layoutText (k : HybridKernel.Kernel) : String :=
  "EMP_HYBRID_KERNEL_LAYOUT_V1\n" ++ String.join (k.inputs.map inputRow) ++ String.join (k.outputs.map outputRow)

/-- The emitters' former `layoutText`, verbatim (for `layoutText_eq_before`). -/
def layoutTextBefore (k : HybridKernel.Kernel) : String :=
  let inputs := k.inputs.map fun f => s!"I {f.1} {f.2.bits}\n"
  let outputs := k.outputs.map fun f =>
    let opened := if f.audience == 1 then 2 else if f.audience == 2 then 3 else if f.opened then 1 else 0
    s!"O {f.name} {f.bits} {opened}\n"
  "EMP_HYBRID_KERNEL_LAYOUT_V1\n" ++ String.join inputs ++ String.join outputs

/-- **The layout file is byte for byte what the emitters wrote before.** -/
theorem layoutText_eq_before (k : HybridKernel.Kernel) : layoutText k = layoutTextBefore k := by
  unfold layoutText layoutTextBefore inputRow outputRow openCode
  simp only [toString, String.append_assoc]

/-- The kernel's input widths, one entry per variable (8 per byte, 255 for a word). -/
def inputWidths (k : HybridKernel.Kernel) : Array Nat :=
  (k.inputs.flatMap fun f => match f.2 with
    | .bytes count => List.replicate count 8
    | .word => [255]).toArray

/-- The kernel lowered to a flat gate list, with the emitters' checks (the same checks, in the
same order and with the same messages, as the former `do` block; written with explicit matches so
that `lowerKernel_ok` can read off what success means). -/
def lowerKernel (k : HybridKernel.Kernel) : Except String FlatLowering.Flat :=
  let bytes := k.outputs.flatMap (·.value)
  match selection k.outputs bytes.length with
  | .error e => .error e
  | .ok chosen =>
    let names := k.inputs.map (·.1)
    if !(names.eraseDups.length == names.length &&
        (k.outputs.map (·.name)).eraseDups.length == k.outputs.length) then .error "duplicate field name"
    else if !(names.all fieldName && k.outputs.all (fieldName ·.name)) then .error "field name"
    else
      match FlatLowering.lowerExpr (ByteCircuit.joinExpr bytes) (inputWidths k) chosen with
      | .error e => .error e
      | .ok flat =>
          if (k.inputs.map (·.2.bits)).foldl (· + ·) 0 == flat.inputs &&
              (k.outputs.map (·.bits)).foldl (· + ·) 0 == flat.outputs.size then .ok flat
          else .error "kernel layout"

/-! ### Reading the layout file back -/

/-- The alphanumeric characters at the head, and the rest. -/
def splitName : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if c.isAlphanum then (c :: (splitName cs).1, (splitName cs).2) else ([], c :: cs)

def parseName (cs : List Char) : Option (String × List Char) :=
  match splitName cs with
  | ([], _) => none
  | (n, rest) => some (String.ofList n, rest)

/-- `I NAME BITS` rows, as long as they come. -/
def parseInputs : Nat → List Char → Option (List (String × Nat) × List Char)
  | fuel + 1, 'I' :: ' ' :: cs =>
      match parseName cs with
      | some (name, cs) =>
          match expectLit [' '] cs with
          | some cs =>
              match parseNat cs with
              | some (bits, cs) =>
                  match expectLit ['\n'] cs with
                  | some cs =>
                      match parseInputs fuel cs with
                      | some (rows, rest) => some ((name, bits) :: rows, rest)
                      | none => none
                  | none => none
              | none => none
          | none => none
      | none => none
  | _, cs => some ([], cs)

/-- `O NAME BITS MARK` rows up to the end of the file. -/
def parseOutputRows : Nat → List Char → Option (List (String × Nat × Nat))
  | _, [] => some []
  | fuel + 1, 'O' :: ' ' :: cs =>
      match parseName cs with
      | some (name, cs) =>
          match expectLit [' '] cs with
          | some cs =>
              match parseNat cs with
              | some (bits, cs) =>
                  match expectLit [' '] cs with
                  | some cs =>
                      match parseNat cs with
                      | some (mark, cs) =>
                          match expectLit ['\n'] cs with
                          | some cs =>
                              match parseOutputRows fuel cs with
                              | some rows => some ((name, bits, mark) :: rows)
                              | none => none
                          | none => none
                      | none => none
                  | none => none
              | none => none
          | none => none
      | none => none
  | _, _ => none

/-- **A loader's reading of a layout file**: the input rows (name, bits) and the output rows
(name, bits, open mark). -/
def parseLayout (cs : List Char) : Option (List (String × Nat) × List (String × Nat × Nat)) :=
  match expectLit "EMP_HYBRID_KERNEL_LAYOUT_V1\n".toList cs with
  | none => none
  | some cs =>
    match parseInputs cs.length cs with
    | none => none
    | some (ins, cs) =>
      match parseOutputRows cs.length cs with
      | none => none
      | some outs => some (ins, outs)

/-- The kernel's declared input fields, as the layout file should list them. -/
def inputFields (k : HybridKernel.Kernel) : List (String × Nat) := k.inputs.map fun f => (f.1, f.2.bits)

/-- The kernel's declared output fields with their open marks. -/
def outputFields (k : HybridKernel.Kernel) : List (String × Nat × Nat) :=
  k.outputs.map fun o => (o.name, o.bits, openCode o)

/-! ### Lemmas -/

/-- A name the parser reads back: non-empty, alphanumeric. -/
def ValidName (s : String) : Prop := s.toList ≠ [] ∧ ∀ c ∈ s.toList, c.isAlphanum = true

theorem fieldName_iff (s : String) : fieldName s = true ↔ ValidName s := by
  unfold fieldName ValidName
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, ne_eq]

theorem space_not_alnum : ' '.isAlphanum = false := rfl

theorem splitName_append (nm rest : List Char) (hn : ∀ c ∈ nm, c.isAlphanum = true) :
    splitName (nm ++ ' ' :: rest) = (nm, ' ' :: rest) := by
  induction nm with
  | nil => simp [splitName, space_not_alnum]
  | cons d ds ih =>
      have h1 : d.isAlphanum = true := hn d (by simp)
      have ih' := ih (fun c hc => hn c (by simp [hc]))
      simp only [List.cons_append, splitName, h1, if_true, ih']

theorem parseName_valid (name : String) (rest : List Char) (hv : ValidName name) :
    parseName (name.toList ++ ' ' :: rest) = some (name, ' ' :: rest) := by
  unfold parseName
  rw [splitName_append _ _ hv.2]
  cases h : name.toList with
  | nil => exact absurd h hv.1
  | cons d ds =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [← h, String.ofList_toList]

theorem lit_I : "I ".toList = ['I', ' '] := rfl
theorem lit_O : "O ".toList = ['O', ' '] := rfl
theorem lit_sp : " ".toList = [' '] := rfl
theorem lit_nl : "\n".toList = ['\n'] := rfl

theorem inputRow_chars (f : String × HybridKernel.Shape) :
    (inputRow f).toList = 'I' :: ' ' :: (f.1.toList ++ ' ' :: (Nat.toDigits 10 f.2.bits ++ ['\n'])) := by
  unfold inputRow
  simp only [String.toList_append, toList_toString, lit_I, lit_sp, lit_nl, List.append_assoc, List.cons_append,
    List.nil_append]

theorem outputRow_chars (o : HybridKernel.Output) :
    (outputRow o).toList = 'O' :: ' ' :: (o.name.toList ++ ' ' :: (Nat.toDigits 10 o.bits ++ ' ' ::
      (Nat.toDigits 10 (openCode o) ++ ['\n']))) := by
  unfold outputRow
  simp only [String.toList_append, toList_toString, lit_O, lit_sp, lit_nl, List.append_assoc, List.cons_append,
    List.nil_append]

theorem parseInputs_rows (rest : List Char) (hr : ∀ cs, rest ≠ 'I' :: ' ' :: cs) :
    ∀ (L : List (String × HybridKernel.Shape)) (fuel : Nat), L.length ≤ fuel → (∀ f ∈ L, ValidName f.1) →
      parseInputs fuel ((String.join (L.map inputRow)).toList ++ rest) =
        some (L.map (fun f => (f.1, f.2.bits)), rest) := by
  intro L
  induction L with
  | nil =>
      intro fuel _ _
      simp only [List.map_nil, String.join_nil, String.toList_empty, List.nil_append]
      cases fuel with
      | zero => simp [parseInputs]
      | succ fuel =>
          match rest, hr with
          | [], _ => simp [parseInputs]
          | [c], _ => simp [parseInputs]
          | c :: d :: cs, hr =>
              by_cases hc : c = 'I' ∧ d = ' '
              · obtain ⟨rfl, rfl⟩ := hc; exact absurd rfl (hr cs)
              · rw [parseInputs.eq_def]
                split
                · rename_i h; simp only [List.cons.injEq] at h; exact absurd ⟨h.1.symm ▸ rfl, h.2.1.symm ▸ rfl⟩ hc
                · rfl
  | cons f L ih =>
      intro fuel hl hv
      cases fuel with
      | zero => simp at hl
      | succ fuel =>
          have ih' := ih fuel (by simp at hl; omega) (fun g hg => hv g (by simp [hg]))
          rw [List.map_cons, String.join_cons, String.toList_append, inputRow_chars]
          simp only [List.cons_append, List.append_assoc]
          simp only [parseInputs]
          rw [parseName_valid _ _ (hv f (by simp))]
          simp only [expectLit, if_true]
          rw [parseNat_digits _ _ (noDigit_newline _)]
          simp only [expectLit, if_true, List.nil_append]
          rw [ih']
          simp

theorem parseOutputRows_rows :
    ∀ (L : List HybridKernel.Output) (fuel : Nat), L.length ≤ fuel → (∀ o ∈ L, ValidName o.name) →
      parseOutputRows fuel (String.join (L.map outputRow)).toList =
        some (L.map (fun o => (o.name, o.bits, openCode o))) := by
  intro L
  induction L with
  | nil => intro fuel _ _; cases fuel <;> simp [parseOutputRows]
  | cons o L ih =>
      intro fuel hl hv
      cases fuel with
      | zero => simp at hl
      | succ fuel =>
          have ih' := ih fuel (by simp at hl; omega) (fun g hg => hv g (by simp [hg]))
          rw [List.map_cons, String.join_cons, String.toList_append, outputRow_chars]
          simp only [List.cons_append, List.append_assoc]
          simp only [parseOutputRows]
          rw [parseName_valid _ _ (hv o (by simp))]
          simp only [expectLit, if_true]
          rw [parseNat_digits _ _ (noDigit_space _)]
          simp only [expectLit, if_true]
          rw [parseNat_digits _ _ (noDigit_newline _)]
          simp only [expectLit, if_true, List.nil_append]
          rw [ih']
          simp

theorem rows_length_in (L : List (String × HybridKernel.Shape)) :
    L.length ≤ (String.join (L.map inputRow)).toList.length := by
  induction L with
  | nil => simp
  | cons f L ih =>
      rw [List.map_cons, String.join_cons, String.toList_append, inputRow_chars]
      simp only [List.length_cons, List.length_append]
      omega

theorem rows_length_out (L : List HybridKernel.Output) :
    L.length ≤ (String.join (L.map outputRow)).toList.length := by
  induction L with
  | nil => simp
  | cons o L ih =>
      rw [List.map_cons, String.join_cons, String.toList_append, outputRow_chars]
      simp only [List.length_cons, List.length_append]
      omega

/-- **The layout file lists exactly the kernel's declared fields and open marks.** For a kernel
whose field names are alphanumeric (which `lowerKernel` checks: `lowerKernel_loaded`), a loader's
reading of `layoutText k` gives the input fields (name, bits) and the output fields (name, bits,
open mark `openCode`) in the kernel's order. -/
theorem parseLayout_layoutText (k : HybridKernel.Kernel) (hin : ∀ f ∈ k.inputs, ValidName f.1)
    (hout : ∀ o ∈ k.outputs, ValidName o.name) :
    parseLayout (layoutText k).toList = some (inputFields k, outputFields k) := by
  unfold parseLayout layoutText
  simp only [String.toList_append, List.append_assoc]
  rw [expectLit_append]
  simp only
  have hr : ∀ cs, (String.join (k.outputs.map outputRow)).toList ≠ 'I' :: ' ' :: cs := by
    intro cs
    cases h : k.outputs with
    | nil => simp
    | cons o os =>
        rw [List.map_cons, String.join_cons, String.toList_append, outputRow_chars]
        simp
  rw [parseInputs_rows _ hr k.inputs _ (by simp only [List.length_append]; have := rows_length_in k.inputs; omega)
    hin]
  simp only
  rw [parseOutputRows_rows k.outputs _ (rows_length_out k.outputs) hout]
  rfl

/-- **The open mark says who may see an output.** -/
theorem openCode_spec (o : HybridKernel.Output) :
    (openCode o = 2 ↔ o.audience = 1) ∧ (openCode o = 3 ↔ o.audience = 2) ∧
      (openCode o = 1 ↔ o.opened = true ∧ o.audience ≠ 1 ∧ o.audience ≠ 2) ∧
      (openCode o = 0 ↔ o.opened = false ∧ o.audience ≠ 1 ∧ o.audience ≠ 2) := by
  unfold openCode
  by_cases h1 : o.audience = 1
  · simp [h1]
  · by_cases h2 : o.audience = 2
    · simp [h2]
    · cases ho : o.opened <;> simp [h1, h2, ho]

theorem bind_ok {α β : Type} {e : Except String α} {f : α → Except String β} {r : β} (h : (e >>= f) = .ok r) :
    ∃ x, e = .ok x ∧ f x = .ok r := by
  cases e with
  | error s => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem unless_ok {β : Type} {c : Bool} {s : String} {f : PUnit → Except String β} {r : β}
    (h : ((unless c do throw s) >>= f) = .ok r) : c = true ∧ f PUnit.unit = .ok r := by
  cases c with
  | false => cases h
  | true => exact ⟨rfl, h⟩

/-- What `lowerKernel` returning `flat` says: the names passed the check, and `flat` is
`lowerExpr` of the kernel's joined output bytes for the kernel's input widths. -/
theorem lowerKernel_ok (k : HybridKernel.Kernel) (flat : FlatLowering.Flat) (h : lowerKernel k = .ok flat) :
    (∀ f ∈ k.inputs, ValidName f.1) ∧ (∀ o ∈ k.outputs, ValidName o.name) ∧
      ∃ chosen, FlatLowering.lowerExpr (ByteCircuit.joinExpr (k.outputs.flatMap (·.value))) (inputWidths k) chosen =
        .ok flat := by
  unfold lowerKernel at h
  simp only at h
  split at h
  · cases h
  · rename_i chosen _
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hnames
        split at h
        · cases h
        · rename_i flat' hl
          split at h
          · cases h
            have hn : ((k.inputs.map (·.1)).all fieldName && k.outputs.all (fieldName ·.name)) = true := by
              cases hb : ((k.inputs.map (·.1)).all fieldName && k.outputs.all (fieldName ·.name))
              · rw [hb] at hnames; exact absurd rfl hnames
              · rfl
            simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
              forall_apply_eq_imp_iff₂, fieldName_iff] at hn
            exact ⟨fun f hf => hn.1 f hf, fun o ho => hn.2 o ho, chosen, hl⟩
          · cases h

/-- **What the engines load for a kernel is that kernel.** If `lowerKernel k` returns `flat`: the
circuit text the printer writes parses back to `flat`; the layout file parses back to the kernel's
declared input fields, output fields and open marks; and `flat` is `lowerExpr` of the kernel's
joined output bytes, so `FlatLowering.lowerExpr_loaded` gives the value of every output wire. -/
theorem lowerKernel_loaded (k : HybridKernel.Kernel) (flat : FlatLowering.Flat) (h : lowerKernel k = .ok flat) :
    FlatLowering.parseFlat ((flat.printWith FlatLowering.appendOut).run "").2.toList = some flat ∧
      parseLayout (layoutText k).toList = some (inputFields k, outputFields k) ∧
      ∃ chosen, FlatLowering.lowerExpr (ByteCircuit.joinExpr (k.outputs.flatMap (·.value))) (inputWidths k) chosen =
        .ok flat := by
  obtain ⟨hin, hout, chosen, hl⟩ := lowerKernel_ok k flat h
  exact ⟨(FlatLowering.lowerExpr_loaded _ _ _ flat hl).1, parseLayout_layoutText k hin hout, chosen, hl⟩

/-- A sample layout file. -/
theorem layoutText_sample :
    layoutText ⟨"t", [("key", HybridKernel.Shape.bytes 2)],
      [HybridKernel.pub "status" [HybridKernel.const 0], HybridKernel.priv "state" []]⟩ =
      "EMP_HYBRID_KERNEL_LAYOUT_V1\nI key 16\nO status 8 1\nO state 0 0\n" := by
  decide

#print axioms layoutText_eq_before
#print axioms parseLayout_layoutText
#print axioms openCode_spec
#print axioms lowerKernel_ok
#print axioms lowerKernel_loaded
#print axioms layoutText_sample

end TlsMpc.FlatKernelLayout
