import TlsMpc.AigExport

/-! Constant-folding expression constructors. Decisions inspect public syntax,
never input values. Folding public computations avoids enormous equivalent
expression graphs in TLS's fixed no-PSK prefix. Every constructor preserves
the ordinary bit-vector semantics for all variable assignments. -/

namespace TlsMpc.BvConstruct

open Std.Tactic.BVDecide

def bin (lhs : BVExpr w) (op : BVBinOp) (rhs : BVExpr w) : BVExpr w :=
  match lhs, rhs with
  | .const a, .const b => .const (op.eval a b)
  | _, _ => .bin lhs op rhs

def un (op : BVUnOp) (arg : BVExpr w) : BVExpr w :=
  match arg with
  | .const a => .const (op.eval a)
  | _ => .un op arg

def extract (start len : Nat) (arg : BVExpr w) : BVExpr len :=
  match arg with
  | .const a => .const (a.extractLsb' start len)
  | _ => .extract start len arg

def append (lhs : BVExpr l) (rhs : BVExpr r) : BVExpr (l + r) :=
  match lhs, rhs with
  | .const a, .const b => .const (a ++ b)
  | _, _ => .append lhs rhs rfl

@[simp] theorem eval_bin (assign : BVExpr.Assignment)
    (lhs : BVExpr w) (op : BVBinOp) (rhs : BVExpr w) :
    BVExpr.eval assign (bin lhs op rhs) = op.eval (BVExpr.eval assign lhs) (BVExpr.eval assign rhs) := by
  cases lhs <;> cases rhs <;> rfl

@[simp] theorem eval_un (assign : BVExpr.Assignment) (op : BVUnOp) (arg : BVExpr w) :
    BVExpr.eval assign (un op arg) = op.eval (BVExpr.eval assign arg) := by
  cases arg <;> rfl

@[simp] theorem eval_extract (assign : BVExpr.Assignment) (start len : Nat) (arg : BVExpr w) :
    BVExpr.eval assign (extract start len arg) = (BVExpr.eval assign arg).extractLsb' start len := by
  cases arg <;> rfl

@[simp] theorem eval_append (assign : BVExpr.Assignment) (lhs : BVExpr l) (rhs : BVExpr r) :
    BVExpr.eval assign (append lhs rhs) = (BVExpr.eval assign lhs) ++ (BVExpr.eval assign rhs) := by
  cases lhs <;> cases rhs <;> rfl

end TlsMpc.BvConstruct
