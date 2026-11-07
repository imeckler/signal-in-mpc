import Std

/-!
The first compiler core. This is an ideal Boolean semantics, not an MPC engine.
An input environment represents reconstructed values only in the mathematical
model. A future runtime implements the instructions on shares.

Both source and target are straight-line and have no reveal or I/O operation.
Secret selection lowers to one AND and two XORs, evaluating both alternatives.
Stack heights are indexed in the target type, ruling out stack underflow.
-/

namespace TlsMpc.Boolean

inductive Expr (inputs : Nat) where
  | input : Fin inputs → Expr inputs
  | literal : Bool → Expr inputs
  | xor : Expr inputs → Expr inputs → Expr inputs
  | and : Expr inputs → Expr inputs → Expr inputs
  | not : Expr inputs → Expr inputs
  | select : Expr inputs → Expr inputs → Expr inputs → Expr inputs
  deriving Repr

def Expr.eval (env : Fin inputs → Bool) : Expr inputs → Bool
  | .input i => env i
  | .literal b => b
  | .xor a b => Bool.xor (a.eval env) (b.eval env)
  | .and a b => a.eval env && b.eval env
  | .not a => !(a.eval env)
  | .select c a b => if c.eval env then a.eval env else b.eval env

inductive Stack : Nat → Type where
  | nil : Stack 0
  | cons : Bool → Stack n → Stack (n + 1)
  deriving Repr

inductive Code (inputs : Nat) : Nat → Nat → Type where
  | load : Fin inputs → Code inputs n (n + 1)
  | literal : Bool → Code inputs n (n + 1)
  | dup : Code inputs (n + 1) (n + 2)
  | xor : Code inputs (n + 2) (n + 1)
  | and : Code inputs (n + 2) (n + 1)
  | not : Code inputs (n + 1) (n + 1)
  | seq : Code inputs a b → Code inputs b c → Code inputs a c

def Code.run (env : Fin inputs → Bool) : Code inputs a b → Stack a → Stack b
  | .load i, s => .cons (env i) s
  | .literal b, s => .cons b s
  | .dup, .cons a s => .cons a (.cons a s)
  | .xor, .cons b (.cons a s) => .cons (Bool.xor a b) s
  | .and, .cons b (.cons a s) => .cons (a && b) s
  | .not, .cons a s => .cons (!a) s
  | .seq a b, s => b.run env (a.run env s)

def compile (e : Expr inputs) (height : Nat) : Code inputs height (height + 1) :=
  match e with
  | .input i => .load i
  | .literal b => .literal b
  | .xor a b => .seq (compile a height) (.seq (compile b (height + 1)) .xor)
  | .and a b => .seq (compile a height) (.seq (compile b (height + 1)) .and)
  | .not a => .seq (compile a height) .not
  | .select c a b =>
      .seq (compile b height)
        (.seq .dup
          (.seq (compile a (height + 2))
            (.seq .xor
              (.seq (compile c (height + 2))
                (.seq .and .xor)))))

private theorem select_identity (c a b : Bool) :
    Bool.xor b ((Bool.xor b a) && c) = (if c then a else b) := by
  cases c <;> cases a <;> cases b <;> rfl

/-- Correct for every input and every existing stack, not just a test vector. -/
theorem compile_correct (e : Expr inputs) (env : Fin inputs → Bool)
    (s : Stack height) :
    (compile e height).run env s = .cons (e.eval env) s := by
  induction e generalizing height with
  | input i => rfl
  | literal b => rfl
  | xor a b ha hb => simp [compile, Code.run, ha, hb, Expr.eval]
  | and a b ha hb => simp [compile, Code.run, ha, hb, Expr.eval]
  | not a ha => simp [compile, Code.run, ha, Expr.eval]
  | select c a b hc ha hb =>
      simp [compile, Code.run, hc, ha, hb, Expr.eval, select_identity]

def Expr.andCost : Expr inputs → Nat
  | .input _ | .literal _ => 0
  | .xor a b => a.andCost + b.andCost
  | .and a b => a.andCost + b.andCost + 1
  | .not a => a.andCost
  | .select c a b => c.andCost + a.andCost + b.andCost + 1

def Code.andCost : Code inputs a b → Nat
  | .and => 1
  | .seq a b => a.andCost + b.andCost
  | _ => 0

/-- The mux lowering uses one AND; neither alternative is compiled twice. -/
theorem compile_andCost (e : Expr inputs) (height : Nat) :
    (compile e height).andCost = e.andCost := by
  induction e generalizing height with
  | input i => rfl
  | literal b => rfl
  | xor a b ha hb => simp [compile, Code.andCost, Expr.andCost, ha, hb]
  | and a b ha hb => simp [compile, Code.andCost, Expr.andCost, ha, hb, Nat.add_assoc]
  | not a ha => simp [compile, Code.andCost, Expr.andCost, ha]
  | select c a b hc ha hb =>
      simp [compile, Code.andCost, Expr.andCost, hc, ha, hb]
      omega

inductive Op where
  | load (index : Nat)
  | literal (value : Bool)
  | dup | xor | and | not
  deriving DecidableEq, Repr

/-- A static instruction schedule; this is not yet a serialized backend format. -/
def Code.schedule : Code inputs a b → List Op
  | .load i => [.load i.val]
  | .literal b => [.literal b]
  | .dup => [.dup]
  | .xor => [.xor]
  | .and => [.and]
  | .not => [.not]
  | .seq a b => a.schedule ++ b.schedule

/-- The structural trace includes both branches and never depends on input values. -/
def Code.trace (env : Fin inputs → Bool) (code : Code inputs a b) (s : Stack a) :
    List Op × Stack b :=
  match code with
  | .seq first second =>
      let (t₁, s₁) := first.trace env s
      let (t₂, s₂) := second.trace env s₁
      (t₁ ++ t₂, s₂)
  | op => (op.schedule, op.run env s)

theorem trace_schedule (code : Code inputs a b) (env : Fin inputs → Bool)
    (s : Stack a) : (code.trace env s).1 = code.schedule := by
  induction code with
  | seq first second hfirst hsecond =>
      simp [Code.trace, Code.schedule, hfirst, hsecond]
  | _ => rfl

theorem trace_result (code : Code inputs a b) (env : Fin inputs → Bool)
    (s : Stack a) : (code.trace env s).2 = code.run env s := by
  induction code with
  | seq first second hfirst hsecond =>
      simp [Code.trace, Code.run, hfirst, hsecond]
  | _ => rfl

/-- Schedule independence only: this does not claim cryptographic MPC security. -/
theorem trace_input_independent (code : Code inputs a b)
    (env₁ env₂ : Fin inputs → Bool) (s₁ s₂ : Stack a) :
    (code.trace env₁ s₁).1 = (code.trace env₂ s₂).1 := by
  rw [trace_schedule, trace_schedule]

end TlsMpc.Boolean
