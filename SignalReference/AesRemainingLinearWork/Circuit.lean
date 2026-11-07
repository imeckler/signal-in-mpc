import TlsMpc.Signal.AesShift

/-! Actual fixslice MixColumns phase operations and their byte-level conjugates.
The phase is public. All four input blocks and all output bitplanes are secret. -/

namespace TlsMpc.Signal.AesRemainingLinear

open AesLayout AesLinear Std.Tactic.BVDecide

def rotateFirst (phase : Nat) (word : BitVec 64) : BitVec 64 :=
  match phase with
  | 0 => word.rotateRight 16
  | 1 => (word.rotateRight 20 &&& 0x0fff0fff0fff0fff) |||
         (word.rotateRight 4 &&& 0xf000f000f000f000)
  | 2 => (word.rotateRight 24 &&& 0x00ff00ff00ff00ff) |||
         (word.rotateRight 8 &&& 0xff00ff00ff00ff00)
  | _ => (word.rotateRight 28 &&& 0x000f000f000f000f) |||
         (word.rotateRight 12 &&& 0xfff0fff0fff0fff0)

def rotateSecond (phase : Nat) (word : BitVec 64) : BitVec 64 :=
  match phase with
  | 0 | 2 => word.rotateRight 32
  | _ => (word.rotateRight 40 &&& 0x00ff00ff00ff00ff) |||
         (word.rotateRight 24 &&& 0xff00ff00ff00ff00)

def mixWords (phase : Nat) (a : Words (BitVec 64)) : Words (BitVec 64) :=
  let b0 := rotateFirst phase a.w0
  let b1 := rotateFirst phase a.w1
  let b2 := rotateFirst phase a.w2
  let b3 := rotateFirst phase a.w3
  let b4 := rotateFirst phase a.w4
  let b5 := rotateFirst phase a.w5
  let b6 := rotateFirst phase a.w6
  let b7 := rotateFirst phase a.w7
  let c0 := a.w0 ^^^ b0
  let c1 := a.w1 ^^^ b1
  let c2 := a.w2 ^^^ b2
  let c3 := a.w3 ^^^ b3
  let c4 := a.w4 ^^^ b4
  let c5 := a.w5 ^^^ b5
  let c6 := a.w6 ^^^ b6
  let c7 := a.w7 ^^^ b7
  ⟨b0 ^^^ c7 ^^^ rotateSecond phase c0,
   b1 ^^^ c0 ^^^ c7 ^^^ rotateSecond phase c1,
   b2 ^^^ c1 ^^^ rotateSecond phase c2,
   b3 ^^^ c2 ^^^ c7 ^^^ rotateSecond phase c3,
   b4 ^^^ c3 ^^^ c7 ^^^ rotateSecond phase c4,
   b5 ^^^ c4 ^^^ rotateSecond phase c5,
   b6 ^^^ c5 ^^^ rotateSecond phase c6,
   b7 ^^^ c6 ^^^ rotateSecond phase c7⟩

/-- For phase k<4, the actual operation is S^(-k) M S^k, where S is
the existing byte ShiftRows and M is the existing byte MixColumns. -/
def phaseBytes (o : Aes.Ops B) (phase : Nat) (input : Nat → Nat → B) : Nat → Nat → B :=
  shiftBytesN o (4 - phase) (mixBytes o (shiftBytesN o phase input))

def shiftIndex (times index : Nat) : Nat :=
  4 * ((index / 4 + times * (index % 4)) % 4) + index % 4

/-- Public permutations act directly on indices, avoiding repeated construction
of sixteen-byte lists. Equality to phaseBytes on the fixed public shape is
proved in the reference bridge. -/
def phaseFastBytes (o : Aes.Ops B) (phase : Nat) (input : Nat → Nat → B)
    (block index : Nat) : B :=
  mixBytes o (fun block index => input block (shiftIndex phase index))
    block (shiftIndex (4 - phase) index)

def expr (phase : Nat) (input : Nat → Nat → BVExpr 8) : List (BVExpr 8) :=
  AesLayout.expr (phaseFastBytes Aes.symbolic phase input)

theorem phaseBytes_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (phase : Nat) (input : Nat → Nat → B) (block index : Nat) :
    f (phaseBytes a phase input block index) =
      phaseBytes b phase (fun block index => f (input block index)) block index := by
  simp only [phaseBytes, shiftBytesN_map h, mixBytes_map h]

theorem phaseFastBytes_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (phase : Nat) (input : Nat → Nat → B) (block index : Nat) :
    f (phaseFastBytes a phase input block index) =
      phaseFastBytes b phase (fun block index => f (input block index)) block index := by
  simp only [phaseFastBytes, mixBytes_map h]

theorem expr_refines (phase : Nat) (input : Nat → Nat → BVExpr 8)
    (assign : BVExpr.Assignment) :
    (expr phase input).map (BVExpr.eval assign) =
      AesLayout.value (phaseFastBytes Aes.concrete phase
        (fun block index => (input block index).eval assign)) := by
  rw [expr, AesLayout.expr_refines]
  congr 1
  funext block index
  exact phaseFastBytes_map (Aes.evaluationHom assign) phase input block index

theorem compiled_expr_correct (phase : Nat) (input : Nat → Nat → BVExpr 8)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * (expr phase input).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr phase input))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef
        ((AigExport.compile (ByteCircuit.joinExpr (expr phase input))).vec.get index hi)) =
      (ByteCircuit.joinValue (AesLayout.value (phaseFastBytes Aes.concrete phase
        (fun block index => (input block index).eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesRemainingLinear
