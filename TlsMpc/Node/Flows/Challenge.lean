import TlsMpc.Node.Flows.Random
import TlsMpc.Node.Flows.ContactsBase

/-!
# `Random.challenge`: the public cut-and-choose challenge (P-CHAL)

REORGANIZATION_PLAN.md 7.1 P-CHAL and "Commit-then-open sites, unified"; stage S10. Replaces
`dabit_generator.h` `Challenge::permutation` (lines 36-56) for the Lean mask pools (the legacy
library keeps its own `Challenge` for its own pools until S11–S16 delete its callers).

THE FLOW, for party `me` with a 32-byte nonce and a 32-byte value in its byte store:
  1. `Random.joint`: commit, exchange, open, exchange, check (P-RAND): the seed s = r_A ⊕ r_B;
  2. the permutation `permOf hash domain s n`, computed by both parties from the public seed:
     a Fisher–Yates selection driven by the words of SHA-256(domain ‖ s ‖ counter) (counter u64
     little-endian, 8 little-endian u32 words per block), each index drawn below `i` by rejection
     (`x < ⌊2³²/i⌋·i`, then `x mod i`), at most `tries` = 64 draws per index (a run of 64
     rejections, probability below 2⁻⁶⁴⁰ for n ≤ 2²⁰, aborts both parties alike).

DEVIATIONS FROM THE C++ (both parties change together; the legacy pools keep theirs):
  * the seed is `Random.joint`'s r_A ⊕ r_B (commitment frame with tag, party and nonce,
    copy check) instead of the concatenation r_A ‖ r_B under SHA-256(r ‖ domain hash ‖ phase);
    the domain enters the expansion instead of the commitment. With `IdealCommit` both are an
    injective function of the honest half (P-CHAL (c));
  * Fisher–Yates by SELECTION (emit the j-th remaining index) rather than by in-place swaps:
    the same distribution (uniform permutations for uniform draws), simpler to prove a
    permutation;
  * a fixed domain per call (plan R18: the C++ domain string grew on every generation);
  * bounded rejection (the C++ loops until a draw is accepted).

PROVED (in the ideal model of Engine/Model.lean; the hash is `Env.hash`):
  * `permOf_perm` (P-CHAL (b)): whenever the expansion succeeds its result is a permutation of
    `[0, n)` (`List.Perm` of `List.range n`): so it has length n, no repeats, all entries below n.
  * `challenge_honest` (P-CHAL (a)): two honest parties compute the same permutation, the one of
    the seed r_A ⊕ r_B (or both abort, when the expansion runs out of draws).
  * `challenge_seed_injective` (P-CHAL (c)): under `IdealCommit` every accepted challenge is
    `permOf (r ⊕ v)` for one adversary value v, and r ↦ r ⊕ v is injective on 32-byte strings.
  * `commit_open_sound`: for every commit-then-open site of the S10 flows (they all use
    `Random.joint`: `challenge`, so the two challenges of `Masks.generate`): an accepted run means the
    adversary's opening matches the commitment it sent BEFORE it saw ours, and differs from ours;
    a commitment equal to ours aborts.
  * `challenge_disclosure` (T3): the adversary's view is a prefix of [commitment, opening].
  * `challenge_wf`, `challenge_reveals` (`jointKinds`), `challenge_bounded`.
-/

namespace TlsMpc.Node.Flows.Random

open TlsMpc.Node.Engine

/-! ## The expansion -/

/-- Little-endian u32 words of a byte string (8 of a 32-byte block). -/
def wordsOf : Bytes → List Nat
  | b0 :: b1 :: b2 :: b3 :: rest =>
    (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat) :: wordsOf rest
  | _ => []

/-- Block `counter` of the expansion: SHA-256(domain ‖ seed ‖ counter as u64 little-endian). -/
def block (hash : Bytes → Bytes) (domain seed : Bytes) (counter : Nat) : Bytes :=
  hash (domain ++ seed ++ le 8 counter)

/-- The expansion's position: the next block's counter, and the words left of the current one. -/
structure Stream where
  counter : Nat := 0
  pending : List Nat := []

/-- The next word. (A hash whose output has no whole word gives 0; only `Env.hash` that is not
SHA-256 can do that.) -/
def Stream.next (hash : Bytes → Bytes) (domain seed : Bytes) (st : Stream) : Nat × Stream :=
  match st.pending with
  | w :: ws => (w, { st with pending := ws })
  | [] =>
    match wordsOf (block hash domain seed st.counter) with
    | w :: ws => (w, ⟨st.counter + 1, ws⟩)
    | [] => (0, ⟨st.counter + 1, []⟩)

/-- Draws per index before giving up. -/
def tries : Nat := 64

/-- An index below `i` (`i ≥ 1`) by rejection sampling, at most `t` draws. -/
def draw (hash : Bytes → Bytes) (domain seed : Bytes) (i : Nat) : Nat → Stream → Option (Nat × Stream)
  | 0, _ => none
  | t + 1, st =>
    let (x, st') := st.next hash domain seed
    if x < 2 ^ 32 / i * i then some (x % i, st') else draw hash domain seed i t st'

theorem draw_lt (hash : Bytes → Bytes) (domain seed : Bytes) (i : Nat) (hi : 0 < i) :
    ∀ (t : Nat) (st st' : Stream) (j : Nat), draw hash domain seed i t st = some (j, st') → j < i
  | 0, _, _, _, h => by simp [draw] at h
  | t + 1, st, st', j, h => by
    simp only [draw] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact Nat.mod_lt _ hi
    · exact draw_lt hash domain seed i hi t _ st' j h

/-- Selection Fisher–Yates: from the remaining indices `pool` (of length `i`), emit the one at a
drawn position, `i` times. -/
def select (hash : Bytes → Bytes) (domain seed : Bytes) : Nat → List Nat → Stream → Option (List Nat)
  | 0, _, _ => some []
  | i + 1, pool, st =>
    match draw hash domain seed (i + 1) tries st with
    | none => none
    | some (j, st') =>
      let x := pool.getD j 0
      match select hash domain seed i (pool.erase x) st' with
      | some rest => some (x :: rest)
      | none => none

/-- **The challenge permutation of `[0, n)`** from a public seed. -/
def permOf (hash : Bytes → Bytes) (domain seed : Bytes) (n : Nat) : Option (List Nat) :=
  select hash domain seed n (List.range n) {}

/-! ## P-CHAL (b): the result is a permutation of `[0, n)` -/

theorem select_perm (hash : Bytes → Bytes) (domain seed : Bytes) :
    ∀ (i : Nat) (pool : List Nat) (st : Stream) (out : List Nat), pool.length = i →
      select hash domain seed i pool st = some out → out.Perm pool
  | 0, pool, st, out, hl, h => by
    simp only [select, Option.some.injEq] at h
    subst h
    rw [List.length_eq_zero_iff] at hl
    subst hl
    exact List.Perm.refl _
  | i + 1, pool, st, out, hl, h => by
    simp only [select] at h
    split at h
    · cases h
    · next j st' hd =>
      have hj : j < i + 1 := draw_lt hash domain seed (i + 1) (by omega) tries st st' j hd
      split at h
      · next rest hr =>
        simp only [Option.some.injEq] at h
        subst h
        have hmem : pool.getD j 0 ∈ pool := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          exact List.getElem_mem _
        have hlen : (pool.erase (pool.getD j 0)).length = i := by
          rw [List.length_erase_of_mem hmem]
          omega
        have ih := select_perm hash domain seed i _ st' rest hlen hr
        exact (ih.cons _).trans (List.perm_cons_erase hmem).symm
      · cases h

/-- **P-CHAL (b).** Whenever the expansion succeeds, its result is a permutation of `[0, n)`. -/
theorem permOf_perm (hash : Bytes → Bytes) (domain seed : Bytes) (n : Nat) (π : List Nat)
    (h : permOf hash domain seed n = some π) : π.Perm (List.range n) :=
  select_perm hash domain seed n _ {} π (List.length_range) h

/-- The consequences used by the mask flow: length `n`, no repeats, every entry below `n`. -/
theorem permOf_spec (hash : Bytes → Bytes) (domain seed : Bytes) (n : Nat) (π : List Nat)
    (h : permOf hash domain seed n = some π) : π.length = n ∧ π.Nodup ∧ ∀ x ∈ π, x < n := by
  have hp := permOf_perm hash domain seed n π h
  refine ⟨by rw [hp.length_eq, List.length_range], hp.nodup_iff.mpr List.nodup_range, fun x hx => ?_⟩
  exact List.mem_range.mp (hp.subset hx)

/-! ## The script -/

/-- After the seed: the permutation, or an abort (both parties alike). -/
def finish (hash : Bytes → Bytes) (domain : Bytes) (n : Nat) (seed : Bytes) : Script (List Nat) :=
  match permOf hash domain seed n with
  | some π => .done π
  | none => .abort "challenge draws"

/-- **`Random.challenge`.** `nonce` and `value` are slots of this party's byte store; `domain`
names the use (public, fixed per call). -/
def challenge (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) (domain : Bytes) (n : Nat) :
    Script (List Nat) :=
  (joint hash me nonce value).bind (finish hash domain n)

/-- The continuation after the seed: silent. -/
theorem finish_silent (hash : Bytes → Bytes) (domain : Bytes) (n : Nat) (seed : Bytes) :
    Contacts.Silent (finish hash domain n seed) := by
  unfold finish
  split
  · exact .done _
  · exact .abort _

theorem finish_wfp (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (domain : Bytes) (n : Nat) (seed : Bytes)
    (Q : Ctx → List Nat → Prop) (c : Ctx) (hq : ∀ π, Q c π) : WFP sigs Q c (finish hash domain n seed) := by
  unfold finish
  split
  · exact WFP.done _ _ (hq _)
  · exact WFP.abort _ _

/-- `challenge` is well formed and leaves the shell's context as it found it. -/
theorem challenge_wfp (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (domain : Bytes) (n : Nat) (c : Ctx) :
    WFP sigs (fun c' _ => c' = c) c (challenge hash me nonce value domain n) :=
  WFP.bind (joint_wfp sigs hash me nonce value c) (fun c' seed hc =>
    finish_wfp sigs hash domain n seed _ c' (fun _ => hc))

theorem challenge_wf (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (domain : Bytes) (n : Nat) (c : Ctx) : WF sigs c (challenge hash me nonce value domain n) :=
  (challenge_wfp sigs hash me nonce value domain n c).wf

theorem challenge_reveals (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) (domain : Bytes) (n : Nat) :
    Reveals jointKinds (challenge hash me nonce value domain n) := by
  have h := Reveals.bind (joint_reveals hash me nonce value)
    (fun seed => (finish_silent hash domain n seed).reveals ([] : List TlsMpc.Node.RevealKind))
  rw [List.append_nil] at h
  exact h

theorem challenge_bounded (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) (domain : Bytes) (n : Nat) :
    Every Instr.Bounded (challenge hash me nonce value domain n) :=
  Every.bind (joint_bounded hash me nonce value) (fun seed => by
    unfold finish
    split
    · exact Every.done _
    · exact Every.abort _)

/-! ## P-CHAL (a): two honest parties agree -/

/-- **P-CHAL (a).** Two honest parties compute the same permutation: the one of the seed
r_A ⊕ r_B, or both abort. (Hypotheses as P-RAND (a): 32-byte hash outputs, nonces and values, and
the two commitments differ.) -/
theorem challenge_honest (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat) (domain : Bytes) (n : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (challenge E.hash .a nA vA domain n) (challenge E.hash .b nB vB domain n) σA σB I).result =
      (permOf E.hash domain (xorBytes (σA.bytes vA) (σB.bytes vB)) n).map fun π => (π, π) := by
  have hj := prand_a_honest E σA σB I nA vA nB vB hh hnA hvA hnB hvB hc
  unfold challenge
  rw [jointRun_bind E _ _ _ _ σA σB I _ _ hj]
  simp only [Outcome2.then, finish]
  cases permOf E.hash domain (xorBytes (σA.bytes vA) (σB.bytes vB)) n with
  | none => rfl
  | some π => rfl

/-! ## Against any adversary -/

section Adversary

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
  (nonce value : Nat) (domain : Bytes) (n : Nat)

/-- The continuation after the seed releases nothing. -/
theorem after_view (seed : Bytes) (σ' : Store) (I' : Ideal) (vD' : List Release) :
    (withAdv E me adv (finish E.hash domain n seed) σ' I' vD').viewD = [] :=
  (Contacts.silent_view E me adv _ (finish_silent E.hash domain n seed) σ' I' vD').1

/-- **T3 for `Random.challenge`.** The adversary's view is a prefix of [our commitment, our
opening] (`Random.e1`, `Random.e2`). -/
theorem challenge_disclosure (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD).viewD <+:
      [e1 E me σ nonce value, e2 σ nonce value] := by
  unfold challenge
  rw [viewD_bind]
  have hj := prand_disclosure E me adv σ I vD nonce value hh hn hv
  split
  · rw [after_view, List.append_nil]
    exact hj
  · rw [List.append_nil]
    exact hj

/-- The run of `challenge` against any adversary is the run of `joint`, then (if it accepted the
seed) the permutation or an abort, with nothing more released. -/
theorem challenge_viewD :
    (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD).viewD =
      (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD := by
  unfold challenge
  rw [viewD_bind]
  split
  · rw [after_view, List.append_nil]
  · rw [List.append_nil]

/-- An accepted challenge is the permutation of the seed `joint` accepted. -/
theorem challenge_result (π : List Nat)
    (h : (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD).result = some π) :
    ∃ seed, (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = some seed ∧
      permOf E.hash domain seed n = some π := by
  unfold challenge at h
  rw [withAdv_bind] at h
  revert h
  cases hj : (withAdv E me adv (joint E.hash me nonce value) σ I vD).result with
  | none => simp [Outcome.stop]
  | some seed =>
    simp only [Outcome.then]
    intro h
    refine ⟨seed, rfl, ?_⟩
    revert h
    unfold finish
    cases hp : permOf E.hash domain seed n with
    | none => simp [withAdv]
    | some π' => simp [withAdv]

/-- **P-CHAL (c).** Under `IdealCommit` (the adversary's opened value is one `v`, whatever the
honest party's randomness in `S`), every accepted challenge is the permutation of r ⊕ v, and the
map from the honest half r to the seed r ⊕ v is injective on 32-byte strings. (Mirroring is
harmless: a copied commitment aborts, `commit_open_sound`.) -/
theorem challenge_seed_injective (hh : ∀ m, (E.hash m).length = 32) (S : Store → Prop)
    (hS : ∀ σ', S σ' → (σ'.bytes nonce).length = 32 ∧ (σ'.bytes value).length = 32)
    (v : Bytes) (hic : IdealCommit E me adv I vD nonce value S v) :
    (∀ σ', S σ' → ∀ π, (withAdv E me adv (challenge E.hash me nonce value domain n) σ' I vD).result = some π →
        permOf E.hash domain (xorBytes (σ'.bytes value) v) n = some π) ∧
      ∀ r r' : Bytes, r.length = 32 → r'.length = 32 → v.length = 32 → xorBytes r v = xorBytes r' v → r = r' := by
  obtain ⟨h1, h2⟩ := prand_b_ideal E me adv I vD nonce value hh S hS v hic
  refine ⟨fun σ' hσ π hπ => ?_, fun r r' hr hr' hv e => ?_⟩
  · obtain ⟨seed, hs, hp⟩ := challenge_result E me adv σ' I vD nonce value domain n π hπ
    obtain ⟨rfl, -⟩ := h1 σ' hσ seed hs
    exact hp
  · rw [← (h2 r hr hv).2, ← (h2 r' hr' hv).2, e]

/-- **`commit_open_sound`, for every commit-then-open site of the S10 flows** (each is a
`Random.joint` run: `challenge` and the two challenges of `Masks.generate`). (1) If the honest party
accepts, the adversary's opening (nonce ‖ value) hashes, under its party's frame, to the commitment
it sent BEFORE our opening reached it (its choice from its prior view and our commitment alone),
that commitment differs from ours, and the accepted value is r ⊕ (its value). (2) A commitment
equal to ours aborts. -/
theorem commit_open_sound (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    (∀ x, (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = some x →
      ∃ p1 p2, adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1 ∧
        adv.act (vD ++ [e1 E me σ nonce value, e2 σ nonce value]) skel2 = some p2 ∧
        E.hash (commitFrame tag me.other (p2.bytes.take 32) (p2.bytes.drop 32)) = p1.bytes ∧
        p1.bytes ≠ ourCommit E me σ nonce value ∧ x = xorBytes (σ.bytes value) (p2.bytes.drop 32)) ∧
    (∀ p1, adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1 →
      p1.bytes = ourCommit E me σ nonce value →
      (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = none) := by
  refine ⟨fun x hx => ?_, fun p1 h1 hcopy => prand_c_copy_aborts E me adv σ I vD nonce value hh hn hv p1 h1 hcopy⟩
  obtain ⟨p1, p2, h1, h2, -, -, hh', hne, -, hx'⟩ := prand_accepted E me adv σ I vD nonce value hh hn hv x hx
  exact ⟨p1, p2, h1, h2, hh', hne, hx'⟩

/-- The same for a challenge: a copied commitment aborts it. -/
theorem challenge_copy_aborts (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) (p1 : PeerPart)
    (h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1)
    (hcopy : p1.bytes = ourCommit E me σ nonce value) :
    (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD).result = none := by
  cases h : (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD).result with
  | none => rfl
  | some π =>
    obtain ⟨seed, hs, -⟩ := challenge_result E me adv σ I vD nonce value domain n π h
    rw [prand_c_copy_aborts E me adv σ I vD nonce value hh hn hv p1 h1 hcopy] at hs
    cases hs

end Adversary

end TlsMpc.Node.Flows.Random
