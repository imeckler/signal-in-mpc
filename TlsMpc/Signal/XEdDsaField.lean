import TlsMpc.X25519

/-! Edwards25519 field stages for Signal XEdDSA. These implement Montgomery
point recovery and [s]B - [h]A, using complete extended-coordinate addition
and fixed public scalar loops. There is no secret-dependent index or branch.

Compiler theorems prove equality to these executable formulas, not a group
law/security theorem or refinement to actual dalek. The hash scalar h must be
produced by SHA512(R||A||message) reduced modulo ell. Its 256 bits and s's 253
bits must be Boolean field elements. A's sign must be bound via canonical byte
conversion to signature[63]. These are unfinished composition obligations;
this module alone must never supply PQXDH validation status. -/
namespace TlsMpc.Signal.XEdDsaField
open FieldDag

def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752
def baseX : Nat := 15112221349535400772501151409588531511454012693041857206046113283949847762202
def baseY : Nat := 46316835694926478169428394003475163141307993866256225615783033603165251855960

structure Point (B : Type) where
  x : B
  y : B
  z : B
  t : B

def Point.map (f : B → C) (p : Point B) : Point C := ⟨f p.x,f p.y,f p.z,f p.t⟩
def affine (o : X25519.Ops B) (x y : B) : Point B := ⟨x,y,o.const 1,o.mul x y⟩
def identity (o : X25519.Ops B) : Point B := ⟨o.const 0,o.const 1,o.const 1,o.const 0⟩
def base (o : X25519.Ops B) : Point B := affine o (o.const baseX) (o.const baseY)

def add (o : X25519.Ops B) (p q : Point B) : Point B :=
  let a := o.mul (o.sub p.y p.x) (o.sub q.y q.x)
  let b := o.mul (o.add p.y p.x) (o.add q.y q.x)
  let c := o.mul (o.const ((2*d)%modulus)) (o.mul p.t q.t)
  let dd := o.mul (o.const 2) (o.mul p.z q.z)
  let e := o.sub b a
  let f := o.sub dd c
  let g := o.add dd c
  let h := o.add b a
  ⟨o.mul e f,o.mul g h,o.mul f g,o.mul e h⟩

def choose (o : X25519.Ops B) (bit : B) (yes no : Point B) : Point B :=
  ⟨X25519.select o bit yes.x no.x,X25519.select o bit yes.y no.y,
    X25519.select o bit yes.z no.z,X25519.select o bit yes.t no.t⟩

def mulBits (o : X25519.Ops B) (p acc : Point B) : List B → Point B
  | [] => acc
  | bit :: rest =>
    let doubled := add o acc acc
    mulBits o p (choose o bit (add o doubled p) doubled) rest

/-- Big-endian list of Boolean field elements, fixed public length. -/
def mul (o : X25519.Ops B) (p : Point B) (bits : List B) : Point B := mulBits o p (identity o) bits

def normalize (o : X25519.Ops B) (p : Point B) : List B :=
  let invZ := X25519.inverse o p.z
  [o.mul p.x invZ,o.mul p.y invZ]

def doubleScalar (o : X25519.Ops B) (x y : B) (h s : List B) : List B :=
  normalize o (add o (mul o (affine o (o.sub (o.const 0) x) y) h) (mul o (base o) s))

def exponent (o : X25519.Ops B) (x : B) (n : Nat) : B :=
  X25519.powBits o x (o.const 1) ((List.range 255).reverse.map n.testBit)
def zero (o : X25519.Ops B) (x : B) : B := o.sub (o.const 1) (exponent o x (modulus-1))

/-- Returns validity1/0, unsigned square-root candidate x, y. The canonical
parity of x must be converted to bits and combined with the signature sign
before supplying A to doubleScalar. Both roots are computed arithmetically.
Noncurve/twist and u=-1 reject; outputs are retained only as internal candidates. -/
def recover (o : X25519.Ops B) (u : B) : List B :=
  let one := o.const 1
  let denom := o.add u one
  let y := o.mul (o.sub u one) (X25519.inverse o denom)
  let yy := o.mul y y
  let v := o.add (o.mul (o.const d) yy) one
  let xx := o.mul (o.sub yy one) (X25519.inverse o v)
  let candidate := exponent o xx ((modulus+3)/8)
  let x := X25519.select o (zero o (o.sub (o.mul candidate candidate) xx))
    candidate (o.mul candidate (o.const sqrtM1))
  let valid := o.mul (o.sub one (zero o denom))
    (o.mul (o.sub one (zero o v)) (zero o (o.sub (o.mul x x) xx)))
  [valid,x,y]

section Refinement
variable {a : X25519.Ops B} {b : X25519.Ops C} {f : B → C} (h : X25519.Hom a b f)
include h

theorem affine_map (x y : B) : (affine a x y).map f = affine b (f x) (f y) := by
  simp only [affine,Point.map,h.const,h.mul]
theorem identity_map : (identity a).map f = identity b := by simp only [identity,Point.map,h.const]
theorem base_map : (base a).map f = base b := by simp only [base,affine_map h,h.const]
theorem add_map (p q : Point B) : (add a p q).map f = add b (p.map f) (q.map f) := by
  simp only [add,Point.map,h.add,h.sub,h.mul,h.const]
theorem choose_map (bit : B) (yes no : Point B) :
    (choose a bit yes no).map f = choose b (f bit) (yes.map f) (no.map f) := by
  simp only [choose,Point.map,X25519.select_map h]
theorem mulBits_map (p acc : Point B) (bits : List B) :
    (mulBits a p acc bits).map f = mulBits b (p.map f) (acc.map f) (bits.map f) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => simp only [mulBits,List.map_cons,ih,choose_map h,add_map h]
theorem mul_map (p : Point B) (bits : List B) :
    (mul a p bits).map f = mul b (p.map f) (bits.map f) := by
  simp only [mul,mulBits_map h,identity_map h]
theorem normalize_map (p : Point B) : (normalize a p).map f = normalize b (p.map f) := by
  simp only [normalize,List.map_cons,List.map_nil,h.mul,X25519.inverse_map h,Point.map]
theorem doubleScalar_map (x y : B) (hh s : List B) :
    (doubleScalar a x y hh s).map f = doubleScalar b (f x) (f y) (hh.map f) (s.map f) := by
  simp only [doubleScalar,normalize_map h,add_map h,mul_map h,affine_map h,h.sub,h.const,base_map h]
theorem exponent_map (x : B) (n : Nat) : f (exponent a x n) = exponent b (f x) n := by
  simp only [exponent,X25519.powBits_map h,h.const]
theorem zero_map (x : B) : f (zero a x) = zero b (f x) := by
  simp only [zero,h.sub,h.const,exponent_map h]
theorem recover_map (u : B) : (recover a u).map f = recover b (f u) := by
  simp only [recover,List.map_cons,List.map_nil,h.mul,h.sub,h.add,h.const,
    zero_map h,exponent_map h,X25519.inverse_map h,X25519.select_map h]
end Refinement

/-- Field artifact family. Each output is individually translation-validated. -/
def run (o : X25519.Ops B) (recovery : Bool) (input : Nat → B) : List B :=
  if recovery then recover o (input 0) else
    doubleScalar o (input 0) (input 1)
      ((List.range 256).reverse.map (fun i => input (2+i)))
      ((List.range 253).reverse.map (fun i => input (258+i)))
theorem run_map {a : X25519.Ops B} {b : X25519.Ops C} {f : B → C}
    (h : X25519.Hom a b f) (recovery : Bool) (input : Nat → B) :
    (run a recovery input).map f = run b recovery (f ∘ input) := by
  cases recovery <;> simp only [run,Bool.false_eq_true,↓reduceIte,doubleScalar_map h,
    recover_map h,List.map_map,Function.comp_def]

def output (recovery : Bool) (index : Nat) : Expr :=
  (run X25519.symbolic recovery Expr.input)[index]?.getD (.const 0)

theorem compiled_output_correct (recovery : Bool) (index : Nat) (input : Nat → F)
    (artifact : FieldDag.Artifact) (hc : FieldDag.compile (output recovery index) = some artifact) :
    FieldDag.result (FieldDag.concrete input) artifact.nodes artifact.output =
      (run X25519.concrete recovery input)[index]?.getD (ofNat 0) := by
  rw [FieldDag.compile_correct _ _ hc]
  have hm := run_map (X25519.evaluationHom input) recovery Expr.input
  have hg := congrArg (fun xs => xs[index]?.getD (ofNat 0)) hm
  simp only [List.getElem?_map,Function.comp_def,Expr.eval] at hg
  unfold output
  cases he : (run X25519.symbolic recovery Expr.input)[index]? with
  | none => simpa only [he,Option.map_none,Option.getD_none,Expr.eval] using hg
  | some e => simpa only [he,Option.map_some,Option.getD_some] using hg

/-- Shared sign correction followed by the Edwards calculation. `flip` must
be a Boolean field element produced by the byte binding stage. -/
def signedRun (o : X25519.Ops B) (input : Nat → B) : List B :=
  let x := X25519.select o (input 2) (o.sub (o.const 0) (input 0)) (input 0)
  doubleScalar o x (input 1)
    ((List.range 256).reverse.map (fun i => input (3+i)))
    ((List.range 253).reverse.map (fun i => input (259+i)))

theorem signedRun_map {a : X25519.Ops B} {b : X25519.Ops C} {f : B → C}
    (h : X25519.Hom a b f) (input : Nat → B) :
    (signedRun a input).map f = signedRun b (f ∘ input) := by
  simp only [signedRun,doubleScalar_map h,X25519.select_map h,h.sub,h.const,
    List.map_map,Function.comp_def]

def signedOutput (index : Nat) : Expr :=
  (signedRun X25519.symbolic Expr.input)[index]?.getD (.const 0)

theorem compiled_signed_output_correct (index : Nat) (input : Nat → F)
    (artifact : FieldDag.Artifact) (hc : FieldDag.compile (signedOutput index) = some artifact) :
    FieldDag.result (FieldDag.concrete input) artifact.nodes artifact.output =
      (signedRun X25519.concrete input)[index]?.getD (ofNat 0) := by
  rw [FieldDag.compile_correct _ _ hc]
  have hm := signedRun_map (X25519.evaluationHom input) Expr.input
  have hg := congrArg (fun xs => xs[index]?.getD (ofNat 0)) hm
  simp only [List.getElem?_map,Function.comp_def,Expr.eval] at hg
  unfold signedOutput
  cases he : (signedRun X25519.symbolic Expr.input)[index]? with
  | none => simpa only [he,Option.map_none,Option.getD_none,Expr.eval] using hg
  | some e => simpa only [he,Option.map_some,Option.getD_some] using hg

end TlsMpc.Signal.XEdDsaField
