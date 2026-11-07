import TlsMpc.Signal.AesKeyScheduleOps

/-! Fixed public control flow for the portable RustCrypto AES256 key schedule.
The accompanying reference package proves links to selected actual Rust
operations; the whole-schedule Rust equivalence is a separate obligation. -/

namespace TlsMpc.Signal.AesKeySchedule

open Std.Tactic.BVDecide

def window (f : List W → List W) (offset : Nat) (words : List W) : List W :=
  words.take offset ++ f ((words.drop offset).take 8) ++ words.drop (offset + 8)

def addConstant (o : Ops W) (offset round : Nat) (words : List W) : List W :=
  words.set (offset + round) (o.xor (words[offset + round]?.getD o.zero) o.rcon)

def expandRound (o : Ops W) (round : Nat) (words : List W) : List W :=
  let offset := 8 + 16 * round
  let words := AesKeyCopy.copyBackward o.zero offset (offset + 8) 8 words
  let words := window o.substitute (offset + 8) words
  let words := window (addConstant o 0 round) (offset + 8) words
  let words := AesKeyColumns.run o.zero (o.column 28) (offset + 8) 16 0 8 words
  if round == 6 then words else
  let words := AesKeyCopy.copyBackward o.zero (offset + 8) (offset + 16) 8 words
  let words := window o.substitute (offset + 16) words
  AesKeyColumns.run o.zero (o.column 12) (offset + 16) 16 0 8 words

def expandRounds (o : Ops W) : Nat → Nat → List W → List W
  | 0, _, words => words
  | count + 1, round, words => expandRounds o count (round + 1) (expandRound o round words)

def phaseGroup (o : Ops W) (offset : Nat) (words : List W) : List W :=
  let words := window (List.map o.inv1) offset words
  let words := window (List.map o.inv2) (offset + 8) words
  window (List.map o.inv3) (offset + 16) words

def restoreNots (o : Ops W) (offset : Nat) (words : List W) : List W :=
  let words := words.set offset (o.not (words[offset]?.getD o.zero))
  let words := words.set (offset + 1) (o.not (words[offset + 1]?.getD o.zero))
  let words := words.set (offset + 5) (o.not (words[offset + 5]?.getD o.zero))
  words.set (offset + 6) (o.not (words[offset + 6]?.getD o.zero))

def restoreRounds (o : Ops W) : Nat → Nat → List W → List W
  | 0, _, words => words
  | count + 1, round, words => restoreRounds o count (round + 1) (window (restoreNots o 0) (round * 8) words)

def finish (o : Ops W) (words : List W) : List W :=
  let words := phaseGroup o 8 words
  let words := phaseGroup o 40 words
  let words := phaseGroup o 72 words
  let words := window (List.map o.inv1) 104 words
  restoreRounds o 14 1 words

/-- The first sixteen words are the repeated-block bit layout of a 32-byte
key. The remaining 104 initial words are zero in the actual Rust entrypoint. -/
def scheduleCore (o : Ops W) (first second : List W) : List W :=
  finish o (expandRounds o 7 0 (first.take 8 ++ second.take 8 ++ List.replicate 104 o.zero))

section Homomorphism

variable {a : Ops W} {b : Ops W'} {f : W → W'} (h : Hom a b f)

theorem window_map (g : List W → List W) (g' : List W' → List W')
    (hg : ∀ words, (g words).map f = g' (words.map f)) (offset : Nat) (words : List W) :
    (window g offset words).map f = window g' offset (words.map f) := by
  simp only [window, List.map_append, hg, List.map_take, List.map_drop]

include h

theorem addConstant_map (offset round : Nat) (words : List W) :
    (addConstant a offset round words).map f = addConstant b offset round (words.map f) := by
  simp only [addConstant, List.map_set, h.xor, h.rcon, ← h.zero, AesSbox.get_map]

theorem expandRound_map (round : Nat) (words : List W) :
    (expandRound a round words).map f = expandRound b round (words.map f) := by
  simp only [expandRound]
  split <;> simp only [AesKeyCopy.copyBackward_map,
    window_map _ _ h.substitute, window_map _ _ (addConstant_map h 0 round),
    AesKeyColumns.run_map f a.zero _ _ (h.column _), h.zero]

theorem expandRounds_map (count round : Nat) (words : List W) :
    (expandRounds a count round words).map f = expandRounds b count round (words.map f) := by
  induction count generalizing round words with
  | zero => rfl
  | succ count ih => simp only [expandRounds, ih, expandRound_map h]

theorem phaseGroup_map (offset : Nat) (words : List W) :
    (phaseGroup a offset words).map f = phaseGroup b offset (words.map f) := by
  have h1 (xs : List W) : (xs.map a.inv1).map f = (xs.map f).map b.inv1 := by
    simp only [List.map_map, Function.comp_def, h.inv1]
  have h2 (xs : List W) : (xs.map a.inv2).map f = (xs.map f).map b.inv2 := by
    simp only [List.map_map, Function.comp_def, h.inv2]
  have h3 (xs : List W) : (xs.map a.inv3).map f = (xs.map f).map b.inv3 := by
    simp only [List.map_map, Function.comp_def, h.inv3]
  simp only [phaseGroup, window_map _ _ h1, window_map _ _ h2, window_map _ _ h3]

theorem restoreNots_map (offset : Nat) (words : List W) :
    (restoreNots a offset words).map f = restoreNots b offset (words.map f) := by
  have get (xs : List W) (i : Nat) :
      f (xs[i]?.getD a.zero) = (xs.map f)[i]?.getD b.zero := by
    simp only [← h.zero, AesSbox.get_map]
  simp only [restoreNots, List.map_set, h.not, get]

theorem restoreRounds_map (count round : Nat) (words : List W) :
    (restoreRounds a count round words).map f = restoreRounds b count round (words.map f) := by
  induction count generalizing round words with
  | zero => rfl
  | succ count ih => simp only [restoreRounds, ih, window_map _ _ (restoreNots_map h 0)]

theorem finish_map (words : List W) : (finish a words).map f = finish b (words.map f) := by
  have h1 (xs : List W) : (xs.map a.inv1).map f = (xs.map f).map b.inv1 := by
    simp only [List.map_map, Function.comp_def, h.inv1]
  simp only [finish, restoreRounds_map h, window_map _ _ h1, phaseGroup_map h]

theorem scheduleCore_map (first second : List W) :
    (scheduleCore a first second).map f = scheduleCore b (first.map f) (second.map f) := by
  simp only [scheduleCore, finish_map h, expandRounds_map h, List.map_append,
    List.map_take, List.map_replicate, h.zero]

end Homomorphism

def expr (first second : List (BVExpr 64)) : List (BVExpr 8) :=
  AesKeyCopy.encodeExpr (scheduleCore symbolic first second)

def value (first second : List (BitVec 64)) : List (BitVec 8) :=
  AesKeyCopy.encode (scheduleCore concrete first second)

theorem expr_refines (first second : List (BVExpr 64)) (assign : BVExpr.Assignment) :
    (expr first second).map (BVExpr.eval assign) =
      value (first.map (BVExpr.eval assign)) (second.map (BVExpr.eval assign)) := by
  simp only [expr, value, AesKeyCopy.encodeExpr_refines, scheduleCore_map (evaluationHom assign)]

theorem compiled_expr_correct (first second : List (BVExpr 64)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (expr first second).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr first second))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expr first second))).vec.get index hi)) =
      (ByteCircuit.joinValue (value (first.map (BVExpr.eval assign))
        (second.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesKeySchedule
