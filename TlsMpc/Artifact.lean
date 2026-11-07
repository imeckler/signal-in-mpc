import TlsMpc.Boolean

/-!
Erasure and export for the proved Boolean compiler. Theorems connect the exported
numeric instruction representation to source evaluation for every input.
The JSON transport, Lean native execution, adapter, and MPC runtime are trusted
execution components; this file does not claim to verify those components.
-/

namespace TlsMpc.Boolean

def Stack.toList : Stack n → List Bool
  | .nil => []
  | .cons value rest => value :: rest.toList

namespace Artifact

def step (env : Nat → Bool) : Op → List Bool → Option (List Bool)
  | .load index, stack => some (env index :: stack)
  | .literal value, stack => some (value :: stack)
  | .dup, value :: rest => some (value :: value :: rest)
  | .xor, b :: a :: rest => some (Bool.xor a b :: rest)
  | .and, b :: a :: rest => some ((a && b) :: rest)
  | .not, value :: rest => some ((!value) :: rest)
  | _, _ => none

def run (env : Nat → Bool) : List Op → List Bool → Option (List Bool)
  | [], stack => some stack
  | op :: rest, stack => (step env op stack).bind (run env rest)

theorem run_append (env : Nat → Bool) (first second : List Op) (stack : List Bool) :
    run env (first ++ second) stack = (run env first stack).bind (run env second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.cons_append, run]
      cases step env op stack <;> simp [ih]

/-- Flattening the indexed target preserves semantics and cannot underflow. -/
theorem schedule_correct (code : Code inputs a b) (env : Nat → Bool) (stack : Stack a) :
    run env code.schedule stack.toList =
      some ((code.run (fun i => env i.val) stack).toList) := by
  induction code with
  | load index => rfl
  | literal value => rfl
  | dup => cases stack <;> rfl
  | xor => cases stack with | cons b rest => cases rest <;> rfl
  | and => cases stack with | cons b rest => cases rest <;> rfl
  | not => cases stack <;> rfl
  | seq first second ihfirst ihsecond =>
      simp [Code.schedule, Code.run, run_append, ihfirst, ihsecond]

/-- Stable numeric ABI: load=0, literal=1, dup=2, xor=3, and=4, not=5. -/
def encode : Op → List Nat
  | .load index => [0, index]
  | .literal false => [1, 0]
  | .literal true => [1, 1]
  | .dup => [2]
  | .xor => [3]
  | .and => [4]
  | .not => [5]

def decode : List Nat → Option Op
  | [0, index] => some (.load index)
  | [1, 0] => some (.literal false)
  | [1, 1] => some (.literal true)
  | [2] => some .dup
  | [3] => some .xor
  | [4] => some .and
  | [5] => some .not
  | _ => none

theorem decode_encode (op : Op) : decode (encode op) = some op := by
  cases op with
  | literal value => cases value <;> rfl
  | _ => rfl

abbrev Block := List (List Nat)

def encodeBlock (ops : List Op) : Block := ops.map encode

def decodeBlock : Block → Option (List Op)
  | [] => some []
  | first :: rest => do
      let op ← decode first
      let tail ← decodeBlock rest
      pure (op :: tail)

theorem decode_encodeBlock (ops : List Op) : decodeBlock (encodeBlock ops) = some ops := by
  induction ops with
  | nil => rfl
  | cons first rest ih =>
      simp only [encodeBlock] at ih
      simp [encodeBlock, decodeBlock, decode_encode, ih]

def execute (env : Nat → Bool) (block : Block) (stack : List Bool) : Option (List Bool) :=
  (decodeBlock block).bind (fun ops => run env ops stack)

def exportExpr (expr : Expr inputs) : Block := encodeBlock (compile expr 0).schedule

/-- The numeric artifact, after decoding and execution, computes the source bit. -/
theorem exportExpr_correct (expr : Expr inputs) (env : Nat → Bool) :
    execute env (exportExpr expr) [] = some [expr.eval (fun i => env i.val)] := by
  simp only [execute, exportExpr, decode_encodeBlock, Option.bind_some]
  have h := schedule_correct (compile expr 0) env Stack.nil
  simpa only [compile_correct, Stack.toList] using h

def evaluateOutput (env : Nat → Bool) (block : Block) : Option Bool := do
  let [value] ← execute env block [] | none
  pure value

def exportProgram (outputs : List (Expr inputs)) : List Block := outputs.map exportExpr

def evaluateProgram (env : Nat → Bool) (blocks : List Block) : Option (List Bool) :=
  blocks.mapM (evaluateOutput env)

theorem exportProgram_correct (outputs : List (Expr inputs)) (env : Nat → Bool) :
    evaluateProgram env (exportProgram outputs) =
      some (outputs.map (Expr.eval (fun i => env i.val))) := by
  induction outputs with
  | nil => rfl
  | cons first rest ih =>
      simp [exportProgram, evaluateProgram, evaluateOutput, exportExpr_correct] at ih ⊢
      rw [ih]
      rfl

end Artifact
end TlsMpc.Boolean
