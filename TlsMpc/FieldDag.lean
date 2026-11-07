import Std
import Init.ShareCommon

/-! Arithmetic circuit lowering with a verified translation validator.
The fast memoizing candidate generator is checked against the source expression
before an artifact is returned. The theorem covers every accepted compilation
and every field assignment. JSON/native execution and the MPC backend remain
unverified, as for the Boolean path. There is no reveal instruction.
-/
namespace TlsMpc.FieldDag

def modulus : Nat := 2 ^ 255 - 19
instance : NeZero modulus := ⟨by decide⟩
abbrev F := Fin modulus
def ofNat (n : Nat) : F := Fin.ofNat modulus n

inductive Bin where
  | add | sub | mul
  deriving DecidableEq, BEq, Hashable, Repr

def Bin.eval : Bin → F → F → F
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

inductive Expr where
  | input : Nat → Expr
  | const : Nat → Expr
  | bin : Bin → Expr → Expr → Expr
with
  @[computed_field] hashCode : Expr → UInt64
    | .input i => mixHash 1 (hash i)
    | .const n => mixHash 2 (hash n)
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

def Expr.eval (input : Nat → F) : Expr → F
  | .input i => input i
  | .const n => ofNat n
  | .bin op a b => op.eval (a.eval input) (b.eval input)

inductive Node where
  | input : Nat → Node
  | const : Nat → Node
  | bin : Bin → Nat → Nat → Node
  deriving DecidableEq, Repr

structure Ops (B : Type) where
  input : Nat → B
  const : Nat → B
  bin : Bin → B → B → B

def concrete (input : Nat → F) : Ops F := ⟨input, ofNat, Bin.eval⟩
def symbolic : Ops Expr := ⟨Expr.input, Expr.const, Expr.bin⟩

def step (ops : Ops B) (values : Array B) : Node → Array B
  | .input i => values.push (ops.input i)
  | .const n => values.push (ops.const n)
  | .bin op a b => values.push (ops.bin op (values[a]?.getD (ops.const 0)) (values[b]?.getD (ops.const 0)))

def run (ops : Ops B) (nodes : List Node) (values : Array B := #[]) : Array B :=
  nodes.foldl (step ops) values

def result (ops : Ops B) (nodes : List Node) (output : Nat) : B :=
  ((run ops nodes)[output]?).getD (ops.const 0)

theorem step_map (input : Nat → F) (values : Array Expr) (node : Node) :
    (step symbolic values node).map (Expr.eval input) =
      step (concrete input) (values.map (Expr.eval input)) node := by
  have get (i : Nat) : (values[i]?.getD (.const 0)).eval input =
      ((values.map (Expr.eval input))[i]?).getD (ofNat 0) := by
    rw [Array.getElem?_map]
    cases values[i]? <;> rfl
  cases node <;> simp only [step, Array.map_push, symbolic, concrete, Expr.eval]
  rw [get, get]

theorem run_map (input : Nat → F) (nodes : List Node) (values : Array Expr) :
    (run symbolic nodes values).map (Expr.eval input) =
      run (concrete input) nodes (values.map (Expr.eval input)) := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node rest ih =>
      change (run symbolic rest (step symbolic values node)).map (Expr.eval input) =
        run (concrete input) rest (step (concrete input) (values.map (Expr.eval input)) node)
      rw [ih, step_map]

theorem result_map (input : Nat → F) (nodes : List Node) (output : Nat) :
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
    | .const n => insert s e (.const n)
    | .bin op a b =>
        let (ra, sa) := generate a s
        let (rb, sb) := generate b sa
        insert sb e (.bin op ra rb)

structure Artifact where
  nodes : List Node
  output : Nat

def topological (nodes : List Node) : Bool :=
  ((nodes.zipIdx).all fun (node, index) => match node with
    | .bin _ a b => a < index && b < index
    | _ => true)

/-- Native common-subexpression sharing makes this exact structural comparison
linear in the DAG size in normal use. It is definitionally the identity. -/
def validates (e : Expr) (a : Artifact) : Bool :=
  let pair := ShareCommon.shareCommon' (result symbolic a.nodes a.output, e)
  topological a.nodes && decide (a.output < a.nodes.length) && (pair.1 == pair.2)

def compile (e : Expr) : Option Artifact :=
  let shared := ShareCommon.shareCommon' e
  let (output, draft) := generate shared {}
  let artifact : Artifact := ⟨draft.nodes.toList, output⟩
  if validates e artifact then some artifact else none

theorem validates_correct (e : Expr) (a : Artifact) (valid : validates e a = true) (input : Nat → F) :
    result (concrete input) a.nodes a.output = e.eval input := by
  simp only [validates, ShareCommon.shareCommon', Bool.and_eq_true] at valid
  have same : result symbolic a.nodes a.output = e := eq_of_beq valid.2
  rw [← result_map, same]

/-- Every artifact returned by the compiler has the source meaning. Failure
is explicit; neither a generator bug nor a cache collision can bypass checking. -/
theorem compile_correct (e : Expr) (a : Artifact) (compiled : compile e = some a) (input : Nat → F) :
    result (concrete input) a.nodes a.output = e.eval input := by
  unfold compile at compiled
  dsimp only at compiled
  cases hg : generate (ShareCommon.shareCommon' e) {} with
  | mk output draft =>
    rw [hg] at compiled
    dsimp only at compiled
    split at compiled
    · rename_i valid
      cases compiled
      exact validates_correct _ _ valid input
    · contradiction

end TlsMpc.FieldDag
