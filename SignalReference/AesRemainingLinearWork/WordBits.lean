import AesRemainingLinearWork.Circuit
import LibSignalReference.Proofs.AesLinearFormula

namespace TlsMpc.Signal.AesRemainingLinear

open AesLayout
set_option maxHeartbeats 4000000

/-- Public coordinate permutation: independent row/column wrap, four blocks. -/
def laneAfter (rows phase lane : Nat) : Nat :=
  ((lane / 16 + rows) % 4) * 16 + ((lane / 4 % 4 + phase * rows) % 4) * 4 + lane % 4

theorem laneAfter_lt (rows phase lane : Nat) : laneAfter rows phase lane < 64 := by
  unfold laneAfter
  omega

theorem rotateFirst_bit_fin (word : BitVec 64) (phase : Fin 4) (lane : Fin 64) :
    (rotateFirst phase.val word).getLsbD lane.val = word.getLsbD (laneAfter 1 phase.val lane.val) := by
  fin_cases phase <;> fin_cases lane <;> simp [rotateFirst, laneAfter]

theorem rotateSecond_bit_fin (word : BitVec 64) (phase : Fin 4) (lane : Fin 64) :
    (rotateSecond phase.val word).getLsbD lane.val = word.getLsbD (laneAfter 2 phase.val lane.val) := by
  fin_cases phase <;> fin_cases lane <;> simp [rotateSecond, laneAfter]

theorem rotateFirst_bit (word : BitVec 64) (phase lane : Nat) (hp : phase < 4) (hl : lane < 64) :
    (rotateFirst phase word).getLsbD lane = word.getLsbD (laneAfter 1 phase lane) :=
  rotateFirst_bit_fin word ⟨phase,hp⟩ ⟨lane,hl⟩

theorem rotateSecond_bit (word : BitVec 64) (phase lane : Nat) (hp : phase < 4) (hl : lane < 64) :
    (rotateSecond phase word).getLsbD lane = word.getLsbD (laneAfter 2 phase lane) :=
  rotateSecond_bit_fin word ⟨phase,hp⟩ ⟨lane,hl⟩

theorem laneAfter_comp (phase : Fin 4) (lane : Fin 64) :
    laneAfter 1 phase.val (laneAfter 2 phase.val lane.val) = laneAfter 3 phase.val lane.val := by
  fin_cases phase <;> fin_cases lane <;> rfl

def mixBit (phase : Nat) (wire : Nat → Nat → Bool) (plane lane : Nat) : Bool :=
  wire plane (laneAfter 1 phase lane) ^^
    (if plane = 0 then false else wire (plane - 1) lane ^^ wire (plane - 1) (laneAfter 1 phase lane)) ^^
    (if AesLinear.feedback plane then wire 7 lane ^^ wire 7 (laneAfter 1 phase lane) else false) ^^
    (wire plane (laneAfter 2 phase lane) ^^ wire plane (laneAfter 3 phase lane))

theorem mixWords_bit (words : Words (BitVec 64)) (phase : Fin 4) (plane : Fin 8) (lane : Fin 64) :
    ((mixWords phase.val words).at plane.val).getLsbD lane.val =
      mixBit phase.val (fun p l => (words.at p).getLsbD l) plane.val lane.val := by
  have hp : phase.val < 4 := phase.isLt
  have hl : lane.val < 64 := lane.isLt
  have hcomp := laneAfter_comp phase lane
  fin_cases plane <;>
    simp (disch := first | assumption | apply laneAfter_lt) only
      [mixWords, Words.at, BitVec.getLsbD_xor, rotateFirst_bit, rotateSecond_bit] <;>
    simp [mixBit, AesLinear.feedback, hcomp]
  simp (disch := first | assumption | apply laneAfter_lt) only
    [← BitVec.getLsbD_eq_getElem, rotateFirst_bit, rotateSecond_bit,
      BitVec.getLsbD_xor, hcomp, Bool.xor_assoc]

end TlsMpc.Signal.AesRemainingLinear
