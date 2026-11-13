import TlsMpc.Node.Flows.CurveProofs

/-!
# `commit_open_sound` for the point exchanges, in the model (PROOF_GAPS F25)

Stage S11. `pointExchange` (split ECDH's `k·B`, the offset agreement's K₀ halves) is a
commit-then-open: the commitment `H(tag ‖ party ‖ nonce ‖ P₁ ‖ … ‖ P_m)`, then the opening. This is
`Random.commit_open_sound` (S10, `Flows/Challenge.lean`) for it, against any adversary of the model
(`Engine/Model.lean` `withAdv`; the adversary is a function of its view and the agreed skeleton):

  (1) if the honest party returns points, then the adversary's commitment `p1` was its choice from
      its prior view and our commitment alone (`adv.act (vD ++ [our commitment])`), its opening `p2`
      hashes under ITS party's frame to `p1`, `p1` differs from ours, and the returned points are
      the honest party's own continuation (`pointsOf`: decode, validity, sums) applied to its own
      opening and `p2`;
  (2) a commitment equal to ours aborts the exchange.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Local.Edwards (Value)

/-- What the honest party computes after the checks (`pointExchange`'s last part): from its opening
`o` and the peer's `o'`. -/
def pointsOf (me : Party) (count : Nat) (o o' : Bytes) : Script (List Value) :=
  let mine := (List.range count).map fun j => TlsMpc.Node.Local.Edwards.decode (((o.drop 32).drop (32 * j)).take 32)
  let peer := (List.range count).map fun j => TlsMpc.Node.Local.Edwards.decode (((o'.drop 32).drop (32 * j)).take 32)
  match mine.mapM id, peer.mapM id with
  | some ms, some ps =>
    if ps.all TlsMpc.Node.Local.Edwards.isValid then
      let sums := (ms.zip ps).map fun e =>
        if me = .a then TlsMpc.Node.Local.Edwards.add e.1 e.2 else TlsMpc.Node.Local.Edwards.add e.2 e.1
      if sums.all TlsMpc.Node.Local.Edwards.isValid then pure sums else .abort "joint point"
    else .abort "peer point"
  | _, _ => .abort "point encoding"

/-- `pointExchange` is the two exchanges, the check, then `pointsOf`. -/
theorem pointExchange_eq (hash : Bytes → Bytes) (me : Party) (tag : Bytes) (nonce points count : Nat) :
    pointExchange hash me tag nonce points count =
      (Script.exchange 32 commitLabel (.commitment tag nonce points)).bind fun x =>
        (Script.exchange (32 + 32 * count) Label.ownPublicPoint (.opening [nonce, points])).bind fun y =>
          (Script.ensure (hash (commitFrame tag me.other (y.2.take 32) (y.2.drop 32)) == x.2 && x.2 != x.1)
            "point commitment").bind fun _ => pointsOf me count y.1 y.2 := rfl

section Adversary

variable (E : Env) (me : Party) (adv : Adversary)

/-- One exchange against the adversary that returned: our payload went out, the adversary's
reply (of the agreed length) came back, nothing else changed. -/
theorem exchange_returned (len : Nat) (l : Label) (p : Payload) (σ : Store) (I : Ideal) (vD : List Release)
    (s r : Bytes) (h : (withAdv E me adv (Script.exchange len l p) σ I vD).result = some (s, r)) :
    ∃ part, adv.act (vD ++ [⟨l, .bytes (p.eval E.hash me σ)⟩]) (InstrP.exchange len l p : Instr).skel = some part ∧
      s = p.eval E.hash me σ ∧ r = part.bytes ∧
      (withAdv E me adv (Script.exchange len l p) σ I vD).store = σ ∧
      (withAdv E me adv (Script.exchange len l p) σ I vD).ideal = I ∧
      (withAdv E me adv (Script.exchange len l p) σ I vD).viewD = [⟨l, .bytes (p.eval E.hash me σ)⟩] := by
  unfold Script.exchange at h ⊢
  by_cases hl : (p.eval E.hash me σ).length = len
  · cases ha : adv.act (vD ++ [⟨l, .bytes (p.eval E.hash me σ)⟩]) (InstrP.exchange len l p : Instr).skel with
    | none => simp_all [withAdv, fill, Wire.early]
    | some part =>
      by_cases hp : part.bytes.length = len
      · simp_all [withAdv, fill, Wire.early, idealStep, absorb]
      · simp_all [withAdv, fill, Wire.early, idealStep]
  · simp_all [withAdv, fill]

theorem ensure_returned (b : Bool) (r : String) (σ : Store) (I : Ideal) (vD : List Release) (u : Unit)
    (h : (withAdv E me adv (Script.ensure b r) σ I vD).result = some u) :
    b = true ∧ (withAdv E me adv (Script.ensure b r) σ I vD).store = σ ∧
      (withAdv E me adv (Script.ensure b r) σ I vD).ideal = I := by
  unfold Script.ensure at h ⊢
  cases b <;> simp_all [withAdv]

/-- Our commitment and our opening, as released. -/
def ourCommitP (σ : Store) (tag : Bytes) (nonce points : Nat) : Bytes :=
  E.hash (commitFrame tag me (σ.bytes nonce) (σ.bytes points))

def ourOpeningP (σ : Store) (nonce points : Nat) : Bytes := σ.bytes nonce ++ σ.bytes points

/-- **F25 (1): `commit_open_sound` for `pointExchange`.** If the honest party returns points `xs`,
then the adversary's commitment `p1` was chosen from its prior view and our commitment only, its
opening `p2` (chosen after our opening) hashes under its own party's frame to `p1`, `p1` differs
from our commitment, and `xs` is the honest party's continuation `pointsOf` on its own opening and
`p2`. -/
theorem pointExchange_sound (tag : Bytes) (nonce points count : Nat) (σ : Store) (I : Ideal) (vD : List Release)
    (xs : List Value)
    (h : (withAdv E me adv (pointExchange E.hash me tag nonce points count) σ I vD).result = some xs) :
    ∃ p1 p2,
      adv.act (vD ++ [⟨commitLabel, .bytes (ourCommitP E me σ tag nonce points)⟩])
          (InstrP.exchange 32 commitLabel (Payload.commitment tag nonce points) : Instr).skel = some p1 ∧
      adv.act (vD ++ [⟨commitLabel, .bytes (ourCommitP E me σ tag nonce points)⟩,
          ⟨Label.ownPublicPoint, .bytes (ourOpeningP σ nonce points)⟩])
          (InstrP.exchange (32 + 32 * count) Label.ownPublicPoint (Payload.opening [nonce, points]) : Instr).skel = some p2 ∧
      E.hash (commitFrame tag me.other (p2.bytes.take 32) (p2.bytes.drop 32)) = p1.bytes ∧
      p1.bytes ≠ ourCommitP E me σ tag nonce points ∧
      (withAdv E me adv (pointsOf me count (ourOpeningP σ nonce points) p2.bytes) σ I
        (vD ++ [⟨commitLabel, .bytes (ourCommitP E me σ tag nonce points)⟩,
          ⟨Label.ownPublicPoint, .bytes (ourOpeningP σ nonce points)⟩])).result = some xs := by
  rw [pointExchange_eq, withAdv_bind] at h
  split at h
  · next x hx =>
    obtain ⟨c, c'⟩ := x
    obtain ⟨p1, a1, a2, a3, a4, a5, a6⟩ := exchange_returned E me adv _ _ _ σ I vD c c' hx
    simp only [Outcome.then] at h
    rw [a4, a5, a6, withAdv_bind] at h
    split at h
    · next y hy =>
      obtain ⟨o, o'⟩ := y
      obtain ⟨p2, b1, b2, b3, b4, b5, b6⟩ := exchange_returned E me adv _ _ _ σ I _ o o' hy
      simp only [Outcome.then] at h
      rw [b4, b5, b6, withAdv_bind] at h
      split at h
      · next u hu =>
        obtain ⟨e1, e2, e3⟩ := ensure_returned E me adv _ _ σ I _ u hu
        simp only [Outcome.then] at h
        rw [e2, e3] at h
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at e1
        refine ⟨p1, p2, a1, by simpa [List.append_assoc, ourCommitP, ourOpeningP, Payload.eval] using b1, ?_, ?_, ?_⟩
        · rw [← a3]; simp only [b3] at e1; exact e1.1
        · rw [← a3]; simpa [a2, ourCommitP, Payload.eval] using e1.2
        · simp only [Payload.eval, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil] at b2
          rw [← b3]
          simp only [ourOpeningP]
          rw [← b2]
          have hv : ∀ vD1 vD2 : List Release, (withAdv E me adv (pointsOf me count o o') σ I vD1).result =
              (withAdv E me adv (pointsOf me count o o') σ I vD2).result := by
            intro vD1 vD2
            unfold pointsOf
            dsimp only
            repeat' split
            all_goals rfl
          rw [hv _ (vD ++ [⟨commitLabel, .bytes (Payload.eval E.hash me σ (Payload.commitment tag nonce points))⟩] ++
            _ ++ _)]
          exact h
      · simp [Outcome.stop] at h
    · simp [Outcome.stop] at h
  · simp [Outcome.stop] at h

/-- **F25 (2): a copied commitment aborts** the point exchange. -/
theorem pointExchange_copy_aborts (tag : Bytes) (nonce points count : Nat) (σ : Store) (I : Ideal)
    (vD : List Release) (p1 : PeerPart)
    (h1 : adv.act (vD ++ [⟨commitLabel, .bytes (ourCommitP E me σ tag nonce points)⟩])
      (InstrP.exchange 32 commitLabel (Payload.commitment tag nonce points) : Instr).skel = some p1)
    (hcopy : p1.bytes = ourCommitP E me σ tag nonce points) :
    (withAdv E me adv (pointExchange E.hash me tag nonce points count) σ I vD).result = none := by
  cases h : (withAdv E me adv (pointExchange E.hash me tag nonce points count) σ I vD).result with
  | none => rfl
  | some xs =>
    obtain ⟨q1, q2, e1, -, -, hne, -⟩ := pointExchange_sound E me adv tag nonce points count σ I vD xs h
    rw [h1] at e1
    cases e1
    exact absurd hcopy hne

/-! ## Value-level disclosure of the point exchange (F24, the commit-then-open of points) -/

theorem exchange_viewD (len : Nat) (l : Label) (p : Payload) (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv (Script.exchange len l p) σ I vD).viewD <+: [⟨l, .bytes (p.eval E.hash me σ)⟩] := by
  unfold Script.exchange
  by_cases hl : (p.eval E.hash me σ).length = len
  · cases ha : adv.act (vD ++ [⟨l, .bytes (p.eval E.hash me σ)⟩]) (InstrP.exchange len l p : Instr).skel with
    | none => simp_all [withAdv, fill, Wire.early]
    | some part =>
      by_cases hp : part.bytes.length = len
      · simp_all [withAdv, fill, Wire.early, idealStep, absorb]
      · simp_all [withAdv, fill, Wire.early, idealStep]
  · simp_all [withAdv, fill]

theorem pointsOf_viewD (count : Nat) (o o' : Bytes) (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv (pointsOf me count o o') σ I vD).viewD = [] := by
  unfold pointsOf
  dsimp only
  repeat' split
  all_goals rfl

theorem ensure_then_viewD (b : Bool) (r : String) (count : Nat) (o o' : Bytes) (σ : Store) (I : Ideal)
    (vD : List Release) :
    (withAdv E me adv ((Script.ensure b r).bind fun _ => pointsOf me count o o') σ I vD).viewD = [] := by
  unfold Script.ensure
  cases b
  · rfl
  · exact pointsOf_viewD E me adv count o o' σ I vD

/-- **F24 for the point exchange: what the honest party releases, with its values.** Against any
adversary the adversary's view of `pointExchange` is a prefix of [our commitment
`H(tag ‖ me ‖ nonce ‖ points)`, our opening `nonce ‖ points`]: nothing else (in particular no
private value) leaves; the decoding, validity checks and sums are local. -/
theorem pointExchange_disclosure (tag : Bytes) (nonce points count : Nat) (σ : Store) (I : Ideal)
    (vD : List Release) :
    (withAdv E me adv (pointExchange E.hash me tag nonce points count) σ I vD).viewD <+:
      [⟨commitLabel, .bytes (ourCommitP E me σ tag nonce points)⟩,
       ⟨Label.ownPublicPoint, .bytes (ourOpeningP σ nonce points)⟩] := by
  have eO : Payload.eval E.hash me σ (.opening [nonce, points]) = ourOpeningP σ nonce points := by
    simp [Payload.eval, ourOpeningP]
  have eC : Payload.eval E.hash me σ (.commitment tag nonce points) = ourCommitP E me σ tag nonce points := rfl
  rw [pointExchange_eq, viewD_bind]
  have h1 := exchange_viewD E me adv 32 commitLabel (.commitment tag nonce points) σ I vD
  rw [eC] at h1
  split
  · next x hx =>
    obtain ⟨c, c'⟩ := x
    obtain ⟨p1, a1, a2, a3, a4, a5, a6⟩ := exchange_returned E me adv _ _ _ σ I vD c c' hx
    rw [a6, a4, a5, viewD_bind]
    have h2 := exchange_viewD E me adv (32 + 32 * count) Label.ownPublicPoint (.opening [nonce, points]) σ I
      (vD ++ [⟨commitLabel, .bytes (ourCommitP E me σ tag nonce points)⟩])
    rw [eO] at h2
    rw [eC]
    refine (List.prefix_append_right_inj _).mpr ?_
    split
    · next y hy =>
      obtain ⟨o, o'⟩ := y
      obtain ⟨p2, b1, b2, b3, b4, b5, b6⟩ := exchange_returned E me adv _ _ _ σ I _ o o' hy
      rw [b6, b4, b5, ensure_then_viewD, eO]
      simp
    · simpa using h2
  · simpa using h1.trans (List.prefix_append _ _)

end Adversary

end TlsMpc.Node.Flows.Curve
