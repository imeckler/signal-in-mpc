import Std
import Init.ShareCommon

/-! Gate-level Boolean circuits with a verified translation validator.

The Boolean counterpart of `FieldDag`: expressions over XOR and AND with shared
subterms are lowered to a numbered node list, and the lowering is checked against
the source expressions before an artifact is returned. Circuits written against
this module control their own gate structure, so a circuit can use exactly the
AND gates its author intends (XOR is free in the Boolean engine).

The theorem covers every accepted compilation and every input assignment. The
text export and the MPC backend remain unverified. There is no reveal instruction.
-/
namespace TlsMpc.BoolDag

inductive Bin where
  | xor | and
  deriving DecidableEq, BEq, Hashable, Repr

def Bin.eval : Bin → Bool → Bool → Bool
  | .xor => Bool.xor
  | .and => (· && ·)

inductive Expr where
  | input : Nat → Expr
  | const : Bool → Expr
  | bin : Bin → Expr → Expr → Expr
with
  @[computed_field] hashCode : Expr → UInt64
    | .input i => mixHash 1 (hash i)
    | .const b => mixHash 2 (hash b)
    | .bin op a b => mixHash 3 (mixHash (hash op) (mixHash a.hashCode b.hashCode))
deriving DecidableEq

instance : Hashable Expr := ⟨Expr.hashCode⟩
def exprEq (a b : Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    if h : hash a ≠ hash b then .isFalse (fun hab => h (congrArg hash hab))
    else inferInstance
instance : DecidableEq Expr := exprEq
instance : BEq Expr := instBEqOfDecidableEq
instance : LawfulBEq Expr := inferInstance

def Expr.eval (input : Nat → Bool) : Expr → Bool
  | .input i => input i
  | .const b => b
  | .bin op a b => op.eval (a.eval input) (b.eval input)

inductive Node where
  | input : Nat → Node
  | const : Bool → Node
  | bin : Bin → Nat → Nat → Node
  deriving DecidableEq, Repr

structure Ops (B : Type) where
  input : Nat → B
  const : Bool → B
  bin : Bin → B → B → B

def concrete (input : Nat → Bool) : Ops Bool := ⟨input, id, Bin.eval⟩
def symbolic : Ops Expr := ⟨Expr.input, Expr.const, Expr.bin⟩

def step (ops : Ops B) (values : Array B) : Node → Array B
  | .input i => values.push (ops.input i)
  | .const b => values.push (ops.const b)
  | .bin op a b => values.push (ops.bin op (values[a]?.getD (ops.const false)) (values[b]?.getD (ops.const false)))

def run (ops : Ops B) (nodes : List Node) (values : Array B := #[]) : Array B :=
  nodes.foldl (step ops) values

def result (ops : Ops B) (nodes : List Node) (output : Nat) : B :=
  ((run ops nodes)[output]?).getD (ops.const false)

theorem step_map (input : Nat → Bool) (values : Array Expr) (node : Node) :
    (step symbolic values node).map (Expr.eval input) =
      step (concrete input) (values.map (Expr.eval input)) node := by
  have get (i : Nat) : (values[i]?.getD (.const false)).eval input =
      ((values.map (Expr.eval input))[i]?).getD false := by
    rw [Array.getElem?_map]
    cases values[i]? <;> rfl
  cases node <;> simp only [step, Array.map_push, symbolic, concrete, Expr.eval, id]
  rw [get, get]

theorem run_map (input : Nat → Bool) (nodes : List Node) (values : Array Expr) :
    (run symbolic nodes values).map (Expr.eval input) =
      run (concrete input) nodes (values.map (Expr.eval input)) := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node rest ih =>
      change (run symbolic rest (step symbolic values node)).map (Expr.eval input) =
        run (concrete input) rest (step (concrete input) (values.map (Expr.eval input)) node)
      rw [ih, step_map]

theorem result_map (input : Nat → Bool) (nodes : List Node) (output : Nat) :
    (result symbolic nodes output).eval input = result (concrete input) nodes output := by
  have hm := run_map input nodes #[]
  simp only [Array.map_empty] at hm
  unfold result
  rw [← hm, Array.getElem?_map]
  cases (run symbolic nodes)[output]? <;> rfl

structure Draft where
  nodes : Array Node := #[]
  cache : Std.HashMap Expr Nat := {}

def insert (s : Draft) (e : Expr) (node : Node) : Nat × Draft :=
  (s.nodes.size, ⟨s.nodes.push node, s.cache.insert e s.nodes.size⟩)

def generate (e : Expr) (s : Draft) : Nat × Draft :=
  match s.cache[e]? with
  | some ref => (ref, s)
  | none => match e with
    | .input i => insert s e (.input i)
    | .const b => insert s e (.const b)
    | .bin op a b =>
        let (ra, sa) := generate a s
        let (rb, sb) := generate b sa
        insert sb e (.bin op ra rb)

def generateAll : List Expr → Draft → List Nat × Draft
  | [], s => ([], s)
  | e :: rest, s =>
      let (r, s1) := generate e s
      let (rs, s2) := generateAll rest s1
      (r :: rs, s2)

/-- A multi-output circuit: one shared node list and one node index per output. -/
structure Artifact where
  nodes : List Node
  outputs : List Nat

def topological (nodes : List Node) : Bool :=
  ((nodes.zipIdx).all fun (node, index) => match node with
    | .bin _ a b => a < index && b < index
    | _ => true)

def symbolicOutputs (a : Artifact) : List Expr := a.outputs.map (result symbolic a.nodes)

/-- Structural comparison of every output with its source expression. Native
common-subexpression sharing makes this linear in the DAG size in normal use;
it is definitionally the identity. -/
def validates (es : List Expr) (a : Artifact) : Bool :=
  let pair := ShareCommon.shareCommon' (symbolicOutputs a, es)
  topological a.nodes && (pair.1 == pair.2)

def compile (es : List Expr) : Option Artifact :=
  let shared := ShareCommon.shareCommon' es
  let (outputs, draft) := generateAll shared {}
  let artifact : Artifact := ⟨draft.nodes.toList, outputs⟩
  if validates es artifact then some artifact else none

theorem validates_correct (es : List Expr) (a : Artifact) (valid : validates es a = true)
    (input : Nat → Bool) :
    a.outputs.map (result (concrete input) a.nodes) = es.map (Expr.eval input) := by
  simp only [validates, ShareCommon.shareCommon', Bool.and_eq_true] at valid
  have same : symbolicOutputs a = es := eq_of_beq valid.2
  rw [← same, symbolicOutputs, List.map_map]
  apply List.map_congr_left
  intro o _
  exact (result_map input a.nodes o).symm

/-- Every artifact returned by the compiler computes the source expressions, in
order. Failure is explicit; neither a generator bug nor a cache collision can
bypass the check. -/
theorem compile_correct (es : List Expr) (a : Artifact) (compiled : compile es = some a)
    (input : Nat → Bool) :
    a.outputs.map (result (concrete input) a.nodes) = es.map (Expr.eval input) := by
  unfold compile at compiled
  dsimp only at compiled
  cases hg : generateAll (ShareCommon.shareCommon' es) {} with
  | mk outputs draft =>
    rw [hg] at compiled
    dsimp only at compiled
    split at compiled
    · rename_i valid
      cases compiled
      exact validates_correct _ _ valid input
    · contradiction

/-- Number of AND nodes: the only gates with a cost in the Boolean engine. -/
def andCount (a : Artifact) : Nat :=
  (a.nodes.filter fun n => match n with | .bin .and _ _ => true | _ => false).length

#print axioms compile_correct

end TlsMpc.BoolDag
