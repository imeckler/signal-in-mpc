import TlsMpc.FieldDag

/-! Multi-output compilation for `FieldDag`: several source expressions lowered to
one shared node list, each checked against its source by the same structural
validator as the single-output compiler. -/
namespace TlsMpc.FieldDag

def generateAll : List Expr → Draft → List Nat × Draft
  | [], s => ([], s)
  | e :: rest, s =>
      let (r, s1) := generate e s
      let (rs, s2) := generateAll rest s1
      (r :: rs, s2)

structure MultiArtifact where
  nodes : List Node
  outputs : List Nat

def symbolicOutputs (a : MultiArtifact) : List Expr := a.outputs.map (result symbolic a.nodes)

def validatesAll (es : List Expr) (a : MultiArtifact) : Bool :=
  let pair := ShareCommon.shareCommon' (symbolicOutputs a, es)
  topological a.nodes && (pair.1 == pair.2)

def compileAll (es : List Expr) : Option MultiArtifact :=
  let shared := ShareCommon.shareCommon' es
  let (outputs, draft) := generateAll shared {}
  let artifact : MultiArtifact := ⟨draft.nodes.toList, outputs⟩
  if validatesAll es artifact then some artifact else none

theorem validatesAll_correct (es : List Expr) (a : MultiArtifact) (valid : validatesAll es a = true)
    (input : Nat → F) :
    a.outputs.map (result (concrete input) a.nodes) = es.map (Expr.eval input) := by
  simp only [validatesAll, ShareCommon.shareCommon', Bool.and_eq_true] at valid
  have same : symbolicOutputs a = es := eq_of_beq valid.2
  rw [← same, symbolicOutputs, List.map_map]
  apply List.map_congr_left
  intro o _
  exact (result_map input a.nodes o).symm

/-- Every accepted multi-output artifact computes its source expressions, in order. -/
theorem compileAll_correct (es : List Expr) (a : MultiArtifact) (compiled : compileAll es = some a)
    (input : Nat → F) :
    a.outputs.map (result (concrete input) a.nodes) = es.map (Expr.eval input) := by
  unfold compileAll at compiled
  dsimp only at compiled
  cases hg : generateAll (ShareCommon.shareCommon' es) {} with
  | mk outputs draft =>
    rw [hg] at compiled
    dsimp only at compiled
    split at compiled
    · rename_i valid
      cases compiled
      exact validatesAll_correct _ _ valid input
    · contradiction

#print axioms compileAll_correct

end TlsMpc.FieldDag
