import TlsMpc.Node.Flows.CurveHonest

/-!
# The point exchange with m points per party, through `jointRun` (PROOF_GAPS F22, part)

Stage S11. `pointExchange_honest` (`CurveHonest.lean`) is for one point per party; the K₀
exchange of `prepareSecond` carries one point per prepared contact. `pointExchange_many_honest`:
each party's byte slot holds its `m` encoded points (32 bytes each) after a 32-byte nonce; every
chunk decodes, every peer point is valid, every sum is valid, the commitments differ. Then both
parties return `[P_A,j + P_B,j]` (party order) and nothing else changes.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Run (JRet jret_bind jret_done jret_step)
open TlsMpc.Node.Local.Edwards (Value decode isValid add montU)

theorem mapM_some_map {α β : Type} (g : α → Option β) (P : α → β) :
    ∀ (l : List α), (∀ j ∈ l, g j = some (P j)) → (l.map g).mapM id = some (l.map P)
  | [], _ => rfl
  | j :: l, h => by
    have ih := mapM_some_map g P l (fun k hk => h k (by simp [hk]))
    simp only [List.map_cons, List.mapM_cons, id, h j (by simp), ih, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]

theorem zip_map_map {α β γ : Type} (l : List γ) (f : γ → α) (g : γ → β) :
    (l.map f).zip (l.map g) = l.map (fun x => (f x, g x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem all_map_range {α : Type} (m : Nat) (f : Nat → α) (p : α → Bool) (h : ∀ j, j < m → p (f j) = true) :
    ((List.range m).map f).all p = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact h j hj

/-- The honest continuation for `m` points. -/
theorem pointsOf_many (me : Party) (m : Nat) (o o' : Bytes) (P Q : Nat → Value)
    (hP : ∀ j, j < m → decode (((o.drop 32).drop (32 * j)).take 32) = some (P j))
    (hQ : ∀ j, j < m → decode (((o'.drop 32).drop (32 * j)).take 32) = some (Q j))
    (hvQ : ∀ j, j < m → isValid (Q j) = true)
    (hS : ∀ j, j < m → isValid (if me = .a then add (P j) (Q j) else add (Q j) (P j)) = true) :
    pointsOf me m o o' = .done ((List.range m).map fun j => if me = .a then add (P j) (Q j) else add (Q j) (P j)) := by
  unfold pointsOf
  dsimp only
  rw [mapM_some_map _ P _ (fun j hj => hP j (List.mem_range.mp hj)),
    mapM_some_map _ Q _ (fun j hj => hQ j (List.mem_range.mp hj))]
  simp only []
  rw [if_pos (all_map_range m Q isValid hvQ), zip_map_map, List.map_map]
  simp only [Function.comp_def]
  rw [if_pos (all_map_range m _ isValid hS)]
  rfl

section Honest

variable (E : Env)

/-- **Two honest parties' point exchange, `m` points each.** Each party's byte slots hold a 32-byte
nonce and its `m` encoded points (`32m` bytes); every chunk decodes (`P_A,j`, `P_B,j`); every point
is valid; every sum `P_A,j + P_B,j` is valid; the commitments differ. Then both parties return the
`m` sums and nothing else changes. -/
theorem pointExchange_many_honest (hh : ∀ m, (E.hash m).length = 32) (tag : Bytes) (σA σB : Store) (I : Ideal)
    (nA sA nB sB m : Nat) (PA PB : Nat → Value)
    (hnA : (σA.bytes nA).length = 32) (hsA : (σA.bytes sA).length = 32 * m)
    (hnB : (σB.bytes nB).length = 32) (hsB : (σB.bytes sB).length = 32 * m)
    (hdA : ∀ j, j < m → decode (((σA.bytes sA).drop (32 * j)).take 32) = some (PA j))
    (hdB : ∀ j, j < m → decode (((σB.bytes sB).drop (32 * j)).take 32) = some (PB j))
    (hvA : ∀ j, j < m → isValid (PA j) = true) (hvB : ∀ j, j < m → isValid (PB j) = true)
    (hvS : ∀ j, j < m → isValid (add (PA j) (PB j)) = true)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes sA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes sB))) :
    JRet (jointRun E (pointExchange E.hash .a tag nA sA m) (pointExchange E.hash .b tag nB sB m) σA σB I)
      ((List.range m).map fun j => add (PA j) (PB j)) ((List.range m).map fun j => add (PA j) (PB j)) I σA σB := by
  rw [pointExchange_eq, pointExchange_eq]
  have eA : Payload.eval E.hash .a σA (.opening [nA, sA]) = σA.bytes nA ++ σA.bytes sA := by simp [Payload.eval]
  have eB : Payload.eval E.hash .b σB (.opening [nB, sB]) = σB.bytes nB ++ σB.bytes sB := by simp [Payload.eval]
  refine jret_bind E _ _ _ _ σA σB I _ _ I σA σB _ _ I σA σB
    (jret_exchange E 32 commitLabel _ _ σA σB I (hh _) (hh _)) ?_
  refine jret_bind E _ _ _ _ σA σB I _ _ I σA σB _ _ I σA σB
    (jret_exchange E (32 + 32 * m) Label.ownPublicPoint _ _ σA σB I
      (by rw [eA, List.length_append, hnA, hsA]) (by rw [eB, List.length_append, hnB, hsB])) ?_
  have dA : (σA.bytes nA ++ σA.bytes sA).drop 32 = σA.bytes sA := List.drop_left' hnA
  have tA : (σA.bytes nA ++ σA.bytes sA).take 32 = σA.bytes nA := List.take_left' hnA
  have dB : (σB.bytes nB ++ σB.bytes sB).drop 32 = σB.bytes sB := List.drop_left' hnB
  have tB : (σB.bytes nB ++ σB.bytes sB).take 32 = σB.bytes nB := List.take_left' hnB
  refine jret_bind E _ _ _ _ σA σB I () () I σA σB _ _ I σA σB
    (jret_ensure E _ _ _ σA σB I ?_ ?_) ?_
  · simp [eA, eB, dA, tA, dB, tB, Payload.eval, Party.other, hc, Ne.symm hc]
  · simp [eA, eB, dA, tA, dB, tB, Payload.eval, Party.other, hc, Ne.symm hc]
  · rw [eA, eB, pointsOf_many .a m _ _ PA PB (by rw [dA]; exact hdA) (by rw [dB]; exact hdB) hvB
        (fun j hj => by simpa using hvS j hj),
      pointsOf_many .b m _ _ PB PA (by rw [dB]; exact hdB) (by rw [dA]; exact hdA) hvA
        (fun j hj => by simpa using hvS j hj)]
    simpa using jret_done E ((List.range m).map fun j => add (PA j) (PB j))
      ((List.range m).map fun j => add (PA j) (PB j)) σA σB I

end Honest

end TlsMpc.Node.Flows.Curve
