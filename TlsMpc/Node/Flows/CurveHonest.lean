import TlsMpc.Node.Flows.CurveCommit
import TlsMpc.Node.Flows.RunAgree

/-!
# Two honest parties' curve flows, through `jointRun` (PROOF_GAPS F22, part)

Stage S11. With the S10 tool `JRet` (`Flows/RunAgree.lean`: the joint run returned these values,
with this engine state and these stores):

  * `jret_exchange`, `jret_ensure`: one exchange between two honest parties (each receives the
    other's payload), a passed check;
  * `pointExchange_honest`: the point exchange returns, to BOTH parties, the sums `P_A,j + P_B,j` of
    their decoded points (in party order), when every point decodes, the peer points are valid,
    the sums are valid, and the two commitments differ; the engines and stores are unchanged;
  * `splitBegin_honest`: split ECDH's key generation gives both parties the same key share
    `u(P_A + P_B)` (32 bytes).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Run (JRet jret_bind jret_done jret_step)
open TlsMpc.Node.Local.Edwards (Value decode isValid add montU)

section Honest

variable (E : Env)

theorem jret_exchange (len : Nat) (l : Label) (pA pB : Payload) (σA σB : Store) (I : Ideal)
    (hA : (pA.eval E.hash .a σA).length = len) (hB : (pB.eval E.hash .b σB).length = len) :
    JRet (jointRun E (Script.exchange len l pA) (Script.exchange len l pB) σA σB I)
      (pA.eval E.hash .a σA, pB.eval E.hash .b σB) (pB.eval E.hash .b σB, pA.eval E.hash .a σA) I σA σB := by
  unfold Script.exchange
  simp [JRet, jointRun, fill, hA, hB, idealStep, Wire.part, absorb, InstrP.skel, InstrP.map]

theorem jret_ensure (cA cB : Bool) (r : String) (σA σB : Store) (I : Ideal) (hA : cA = true) (hB : cB = true) :
    JRet (jointRun E (Script.ensure cA r) (Script.ensure cB r) σA σB I) () () I σA σB := by
  subst hA hB
  exact jret_done E () () σA σB I

/-- The honest continuation for one point: both parties' encodings decode, the peer's point is
valid, the sum is valid. -/
theorem pointsOf_one (me : Party) (o o' : Bytes) (P Q : Value) (ho : (o.drop 32).take 32 = (o.drop 32))
    (ho' : (o'.drop 32).take 32 = (o'.drop 32))
    (hP : decode (o.drop 32) = some P) (hQ : decode (o'.drop 32) = some Q) (hvQ : isValid Q = true)
    (hS : isValid (if me = .a then add P Q else add Q P) = true) :
    pointsOf me 1 o o' = .done [if me = .a then add P Q else add Q P] := by
  unfold pointsOf
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, List.drop_zero, ho, ho', hP, hQ,
    List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    List.all_cons, List.all_nil, hvQ, Bool.and_true, if_true, List.zip_cons_cons, List.zip_nil_left]
  simp only [hS, Bool.and_true, if_true]
  rfl

/-- **Two honest parties' point exchange (one point each).** Each party's byte slots hold a
32-byte nonce and its encoded point; both encodings decode (`P_A`, `P_B`); each peer point is valid;
the sum `P_A + P_B` is valid; the commitments differ. Then both parties return `[P_A + P_B]` and
nothing else changes. -/
theorem pointExchange_honest (hh : ∀ m, (E.hash m).length = 32) (tag : Bytes) (σA σB : Store) (I : Ideal)
    (nA sA nB sB : Nat) (PA PB : Value)
    (hnA : (σA.bytes nA).length = 32) (hsA : (σA.bytes sA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hsB : (σB.bytes sB).length = 32)
    (hdA : decode (σA.bytes sA) = some PA) (hdB : decode (σB.bytes sB) = some PB)
    (hvA : isValid PA = true) (hvB : isValid PB = true) (hvS : isValid (add PA PB) = true)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes sA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes sB))) :
    JRet (jointRun E (pointExchange E.hash .a tag nA sA 1) (pointExchange E.hash .b tag nB sB 1) σA σB I)
      [add PA PB] [add PA PB] I σA σB := by
  rw [pointExchange_eq, pointExchange_eq]
  have eA : Payload.eval E.hash .a σA (.opening [nA, sA]) = σA.bytes nA ++ σA.bytes sA := by simp [Payload.eval]
  have eB : Payload.eval E.hash .b σB (.opening [nB, sB]) = σB.bytes nB ++ σB.bytes sB := by simp [Payload.eval]
  refine jret_bind E _ _ _ _ σA σB I _ _ I σA σB _ _ I σA σB
    (jret_exchange E 32 commitLabel _ _ σA σB I (hh _) (hh _)) ?_
  refine jret_bind E _ _ _ _ σA σB I _ _ I σA σB _ _ I σA σB
    (jret_exchange E (32 + 32 * 1) Label.ownPublicPoint _ _ σA σB I
      (by rw [eA, List.length_append, hnA, hsA]) (by rw [eB, List.length_append, hnB, hsB])) ?_
  have dA : (σA.bytes nA ++ σA.bytes sA).drop 32 = σA.bytes sA := List.drop_left' hnA
  have tA : (σA.bytes nA ++ σA.bytes sA).take 32 = σA.bytes nA := List.take_left' hnA
  have dB : (σB.bytes nB ++ σB.bytes sB).drop 32 = σB.bytes sB := List.drop_left' hnB
  have tB : (σB.bytes nB ++ σB.bytes sB).take 32 = σB.bytes nB := List.take_left' hnB
  refine jret_bind E _ _ _ _ σA σB I () () I σA σB _ _ I σA σB
    (jret_ensure E _ _ _ σA σB I ?_ ?_) ?_
  · simp [eA, eB, dA, tA, dB, tB, Payload.eval, Party.other, hc, Ne.symm hc]
  · simp [eA, eB, dA, tA, dB, tB, Payload.eval, Party.other, hc, Ne.symm hc]
  · rw [eA, eB, pointsOf_one .a _ _ PA PB (by rw [dA]; exact List.take_of_length_le (Nat.le_of_eq hsA))
        (by rw [dB]; exact List.take_of_length_le (Nat.le_of_eq hsB)) (by rw [dA]; exact hdA)
        (by rw [dB]; exact hdB) hvB (by simpa using hvS),
      pointsOf_one .b _ _ PB PA (by rw [dB]; exact List.take_of_length_le (Nat.le_of_eq hsB))
        (by rw [dA]; exact List.take_of_length_le (Nat.le_of_eq hsA)) (by rw [dB]; exact hdB)
        (by rw [dA]; exact hdA) hvA (by simpa using hvS)]
    simpa using jret_done E [add PA PB] [add PA PB] σA σB I

/-- **F22, `splitBegin` through `jointRun`**: two honest parties (each with a 32-byte nonce and its
encoded share `k·B`, decoding to `P_A`, `P_B`, both valid, the sum valid, distinct commitments) both
obtain the same client key share `u(P_A + P_B)`, as 32 bytes; nothing else changes. -/
theorem splitBegin_honest (hh : ∀ m, (E.hash m).length = 32) (σA σB : Store) (I : Ideal)
    (nA sA nB sB : Nat) (PA PB : Value)
    (hnA : (σA.bytes nA).length = 32) (hsA : (σA.bytes sA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hsB : (σB.bytes sB).length = 32)
    (hdA : decode (σA.bytes sA) = some PA) (hdB : decode (σB.bytes sB) = some PB)
    (hvA : isValid PA = true) (hvB : isValid PB = true) (hvS : isValid (add PA PB) = true)
    (hc : E.hash (commitFrame splitTag .a (σA.bytes nA) (σA.bytes sA)) ≠
      E.hash (commitFrame splitTag .b (σB.bytes nB) (σB.bytes sB))) :
    JRet (jointRun E (splitBegin E.hash .a nA sA) (splitBegin E.hash .b nB sB) σA σB I)
      (TlsMpc.Node.Local.Field.toBytes (montU (add PA PB))) (TlsMpc.Node.Local.Field.toBytes (montU (add PA PB)))
      I σA σB := by
  unfold splitBegin
  exact jret_bind E _ _ _ _ σA σB I _ _ I σA σB _ _ I σA σB
    (pointExchange_honest E hh splitTag σA σB I nA sA nB sB PA PB hnA hsA hnB hsB hdA hdB hvA hvB hvS hc)
    (jret_done E _ _ σA σB I)

end Honest

end TlsMpc.Node.Flows.Curve
