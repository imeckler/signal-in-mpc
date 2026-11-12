import TlsMpc.Node.Engine.Model
import TlsMpc.Node.Engine.Labels
import TlsMpc.Node.Engine.Reveal

/-!
# `Random.joint`: joint public randomness by commit-then-open (op 33)

REORGANIZATION_PLAN.md section 7.1, P-RAND; stage S9 (Lean side, advance work in a new file).
Replaces `tls_worker_v3.cpp` `joint_random` (lines 148-154) for operation 33.

The flow, for party `me` with 32 random bytes `n` (nonce) and 32 random bytes `r` (value) in its
byte store (drawn by `Channels.random` before the script runs, rule 5):
  1. exchange the commitment c = H("joint-random" ‖ me ‖ n ‖ r), receive the peer's c';
  2. exchange the opening n ‖ r, receive the peer's n' ‖ r';
  3. accept iff H("joint-random" ‖ peer ‖ n' ‖ r') = c' and c' ≠ c;
  4. return r ⊕ r'.
The two exchanges are two batches (Engine.lean decision D8): our opening leaves only after the
peer's commitment has arrived. The C++ committed to SHA-256(r) without tag, party or nonce; the
plan's default framing is used here (both parties change together when op 33 moves).

The result is public (`Reveal.jointRandom`); the commitment and the opening are own-secret
reveals (`Reveal.commitment`, `Reveal.commitOpening`), declared in the script as `Payload`s.
In the reveal list's vocabulary (Engine/Reveal.lean): the script declares the kinds
`jointKinds = [.commitment, .commitOpening]` (`joint_reveals`); its two releases carry the labels
`Label.ofKind .commitment` (code 100) and `Label.ofKind .commitOpening` (code 101). The kind
`jointRandom` (code 20) is never a label on the wire: it is the controller's name for the result,
r_A ⊕ r_B, computed from those two releases.

PROVED (in the ideal model of Engine/Model.lean; `H` is `Env.hash`):
  joint_wf: the script is well formed in every context (labels, exchange sizes).
  prand_a_honest (P-RAND (a)): two honest parties both return r_A ⊕ r_B, provided H has
    32-byte outputs, the stores hold 32-byte nonces and values, and the two commitments differ
    (they are hashes of frames that differ in the party byte, so equality is a collision of H).
  withAdv_joint: against ANY adversary, the honest party's whole run, computed: its views, trace,
    replies and result, as a function of the adversary's two choices.
  prand_disclosure (T3 for this flow): the adversary's view is a prefix of
    [commitment c, opening n ‖ r]; nothing else of the honest party's store is released.
  prand_commit_before_open: whenever the opening reaches the adversary, its commitment c' was
    already fixed, as a function of its prior view and c alone.
  prand_c_copy_aborts (P-RAND (c)): a commitment equal to ours aborts.
  prand_accepted: an accepted result is r ⊕ v where v is the value the adversary opened and that
    opening matches the commitment it sent before seeing our opening.
  prand_b_ideal (P-RAND (b)): under `IdealCommit` (the adversary's accepted value does not depend
    on the honest party's randomness: plan 7.0, "the adversary's committed value is a function of
    what it saw before the commitment exchange"), every accepted result is r ⊕ v for one fixed v,
    and r ↦ r ⊕ v is a bijection of 32-byte strings (its own inverse).
  joint_reveals, joint_viewD_kinds (T3 in the reveal list's vocabulary): every release of any run,
    against any adversary, is labelled `ofKind .commitment` or `ofKind .commitOpening`; with no
    hypothesis (not even on the hash). joint_bounded: the sender's wires fit the pipe.
-/

namespace TlsMpc.Node.Flows.Random

open TlsMpc.Node.Engine

/-- The commitment tag. -/
def tag : Bytes := ascii "joint-random"

def xorBytes (x y : Bytes) : Bytes := List.zipWith (· ^^^ ·) x y

/-- Whether party `me` accepts the peer's opening `o'` of its commitment `c'` (ours: `c`). -/
def accepts (hash : Bytes → Bytes) (me : Party) (c c' o' : Bytes) : Bool :=
  hash (commitFrame tag me.other (o'.take 32) (o'.drop 32)) == c' && c' != c

/-- **Op 33.** `nonce` and `value` are slots of this party's byte store. -/
def joint (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) : Script Bytes := do
  let (c, c') ← Script.exchange 32 Label.jointRandomCommitment (.commitment tag nonce value)
  let (o, o') ← Script.exchange 64 Label.jointRandomOpening (.opening [nonce, value])
  Script.ensure (accepts hash me c c' o') "random commitment"
  pure (xorBytes (o.drop 32) (o'.drop 32))

/-! ## XOR -/

theorem xorBytes_comm (x y : Bytes) : xorBytes x y = xorBytes y x := by
  unfold xorBytes
  rw [List.zipWith_comm]
  congr
  funext a b
  exact UInt8.xor_comm b a

theorem xorBytes_xorBytes (x v : Bytes) (h : x.length = v.length) : xorBytes (xorBytes x v) v = x := by
  induction x generalizing v with
  | nil => rfl
  | cons a x ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      simp only [xorBytes, List.zipWith_cons_cons] at ih ⊢
      rw [ih v (by simpa using h), UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

theorem xorBytes_length (x y : Bytes) : (xorBytes x y).length = min x.length y.length := by
  simp [xorBytes]

/-- `r ↦ r ⊕ v` is its own inverse on strings of `v`'s length, so a bijection of them. -/
theorem xor_bijective (v : Bytes) :
    ∀ r, r.length = v.length → (xorBytes r v).length = v.length ∧ xorBytes (xorBytes r v) v = r := by
  intro r h
  exact ⟨by simp [xorBytes_length, h], xorBytes_xorBytes r v h⟩

/-! ## Well-formedness -/

theorem joint_wf (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (c : Ctx) : WF sigs c (joint hash me nonce value) := by
  have hc : maxExchange = 65536 := rfl
  simp only [joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
  refine WF.step c c (.bytes 32) _ _
    (by simp [check, InstrP.skel, InstrP.map, Label.jointRandomCommitment, hc, guard]) ?_
  intro r _
  cases r with
  | exchanged s x =>
    simp only [Script.bind_done]
    refine WF.step c c (.bytes 64) _ _
      (by simp [check, InstrP.skel, InstrP.map, Label.jointRandomOpening, hc, guard]) ?_
    intro r _
    cases r with
    | exchanged o o' =>
      simp only [Script.bind_done]
      split
      · exact WF.done _ _
      · exact WF.abort _ _
    | _ => exact WF.abort _ _
  | _ => exact WF.abort _ _

/-- `joint` is well formed and leaves the shell's context as it found it (it only exchanges). -/
theorem joint_wfp (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (c : Ctx) : WFP sigs (fun c' _ => c' = c) c (joint hash me nonce value) := by
  have hc : maxExchange = 65536 := rfl
  simp only [joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
  refine WFP.step c c (.bytes 32) _ _
    (by simp [check, InstrP.skel, InstrP.map, Label.jointRandomCommitment, hc, guard]) ?_
  intro r _
  cases r with
  | exchanged s x =>
    simp only [Script.bind_done]
    refine WFP.step c c (.bytes 64) _ _
      (by simp [check, InstrP.skel, InstrP.map, Label.jointRandomOpening, hc, guard]) ?_
    intro r _
    cases r with
    | exchanged o o' =>
      simp only [Script.bind_done]
      split
      · exact WFP.done _ _ rfl
      · exact WFP.abort _ _
    | _ => exact WFP.abort _ _
  | _ => exact WFP.abort _ _

/-! ## The reveal list: the kinds `joint` releases under -/

/-- The kinds `Random.joint` declares: its commitment and its opening. -/
def jointKinds : List TlsMpc.Node.RevealKind := [.commitment, .commitOpening]

/-- Every instruction of `joint`, on every branch, satisfies `P`, given its two exchanges do. -/
theorem joint_every (P : Instr → Prop) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (h1 : P (.exchange 32 Label.jointRandomCommitment (.commitment tag nonce value)))
    (h2 : P (.exchange 64 Label.jointRandomOpening (.opening [nonce, value]))) :
    Every P (joint hash me nonce value) := by
  simp only [joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
  refine Every.step _ _ h1 (fun r => ?_)
  cases r with
  | exchanged s x =>
    simp only [Script.bind_done]
    refine Every.step _ _ h2 (fun r => ?_)
    cases r with
    | exchanged o o' =>
      simp only [Script.bind_done]
      split
      · exact Every.done _
      · exact Every.abort _
    | _ => exact Every.abort _
  | _ => exact Every.abort _

/-- **`joint` declares `jointKinds`**: its releases are labelled `ofKind .commitment` and
`ofKind .commitOpening`, on every branch. -/
theorem joint_reveals (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) :
    Reveals jointKinds (joint hash me nonce value) :=
  joint_every _ hash me nonce value
    (LabelIn.of_mem (k := .commitment) (by simp [jointKinds]) rfl)
    (LabelIn.of_mem (k := .commitOpening) (by simp [jointKinds]) rfl)

/-- **T3 for `Random.joint` in the reveal list's vocabulary.** Against any adversary, from any
store and engine state, every release the adversary receives is labelled `ofKind k`, `k` the
commitment or the opening kind. -/
theorem joint_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonce value : Nat) :
    ∀ r ∈ (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD,
      ∃ k ∈ jointKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (joint_reveals E.hash me nonce value) σ I vD

/-- **The sender's wires of `joint` fit the pipe** (`Wire.Bounded`). -/
theorem joint_bounded (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) :
    Every Instr.Bounded (joint hash me nonce value) :=
  joint_every _ hash me nonce value
    ⟨by decide, Label.ofKind_code_lt _, show (0 : Nat) < B64 by decide⟩
    ⟨by decide, Label.ofKind_code_lt _, show (0 : Nat) < B64 by decide⟩

/-! ## Two honest parties: P-RAND (a) -/

/-- **P-RAND (a).** Both honest parties return r_A ⊕ r_B. -/
theorem prand_a_honest (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (joint E.hash .a nA vA) (joint E.hash .b nB vB) σA σB I).result =
      some (xorBytes (σA.bytes vA) (σB.bytes vB), xorBytes (σA.bytes vA) (σB.bytes vB)) := by
  have dA : (σA.bytes nA ++ σA.bytes vA).drop 32 = σA.bytes vA := List.drop_left' hnA
  have tA : (σA.bytes nA ++ σA.bytes vA).take 32 = σA.bytes nA := List.take_left' hnA
  have dB : (σB.bytes nB ++ σB.bytes vB).drop 32 = σB.bytes vB := List.drop_left' hnB
  have tB : (σB.bytes nB ++ σB.bytes vB).take 32 = σB.bytes nB := List.take_left' hnB
  have hc' := Ne.symm hc
  simp only [joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
  simp [jointRun, fill, Payload.eval, InstrP.skel, InstrP.map, idealStep, Wire.part, absorb, hh, hnA, hvA,
    hnB, hvB, accepts, dA, tA, dB, tB, hc, hc', Party.other, xorBytes_comm (σB.bytes vB)]

/-- The honest run of `joint` leaves the engines' state as it was (it only exchanges bytes). -/
theorem prand_a_honest_ideal (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (joint E.hash .a nA vA) (joint E.hash .b nB vB) σA σB I).ideal = I := by
  have dA : (σA.bytes nA ++ σA.bytes vA).drop 32 = σA.bytes vA := List.drop_left' hnA
  have tA : (σA.bytes nA ++ σA.bytes vA).take 32 = σA.bytes nA := List.take_left' hnA
  have dB : (σB.bytes nB ++ σB.bytes vB).drop 32 = σB.bytes vB := List.drop_left' hnB
  have tB : (σB.bytes nB ++ σB.bytes vB).take 32 = σB.bytes nB := List.take_left' hnB
  have hc' := Ne.symm hc
  simp only [joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
  simp [jointRun, fill, Payload.eval, InstrP.skel, InstrP.map, idealStep, Wire.part, absorb, hh, hnA, hvA,
    hnB, hvB, accepts, dA, tA, dB, tB, hc, hc', Party.other, xorBytes_comm (σB.bytes vB)]

/-! ## Against any adversary -/

section Adversary

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
  (nonce value : Nat)

/-- Our commitment. -/
def ourCommit : Bytes := E.hash (commitFrame tag me (σ.bytes nonce) (σ.bytes value))
/-- What our first exchange releases. -/
def e1 : Release := ⟨Label.jointRandomCommitment, .bytes (ourCommit E me σ nonce value)⟩
/-- What our second exchange releases. -/
def e2 : Release := ⟨Label.jointRandomOpening, .bytes (σ.bytes nonce ++ σ.bytes value)⟩
def skel1 : Skel := .exchange 32 Label.jointRandomCommitment ()
def skel2 : Skel := .exchange 64 Label.jointRandomOpening ()

/-- The run, computed: everything is determined by the adversary's two choices, the first made
from its prior view and our commitment, the second from those and our opening. -/
theorem withAdv_joint (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    withAdv E me adv (joint E.hash me nonce value) σ I vD =
      match adv.act (vD ++ [e1 E me σ nonce value]) skel1 with
      | none => ⟨none, σ, I, [], [e1 E me σ nonce value], [skel1], []⟩
      | some p1 =>
        if p1.bytes.length = 32 then
          match adv.act (vD ++ [e1 E me σ nonce value, e2 σ nonce value]) skel2 with
          | none =>
            ⟨none, σ, I, [⟨Label.jointRandomCommitment, .bytes p1.bytes⟩],
              [e1 E me σ nonce value, e2 σ nonce value], [skel1, skel2],
              [.exchanged (ourCommit E me σ nonce value) p1.bytes]⟩
          | some p2 =>
            if p2.bytes.length = 64 then
              ⟨if accepts E.hash me (ourCommit E me σ nonce value) p1.bytes p2.bytes then
                  some (xorBytes (σ.bytes value) (p2.bytes.drop 32)) else none,
                σ, I,
                [⟨Label.jointRandomCommitment, .bytes p1.bytes⟩, ⟨Label.jointRandomOpening, .bytes p2.bytes⟩],
                [e1 E me σ nonce value, e2 σ nonce value], [skel1, skel2],
                [.exchanged (ourCommit E me σ nonce value) p1.bytes,
                  .exchanged (σ.bytes nonce ++ σ.bytes value) p2.bytes]⟩
            else
              ⟨none, σ, I, [⟨Label.jointRandomCommitment, .bytes p1.bytes⟩],
                [e1 E me σ nonce value, e2 σ nonce value], [skel1, skel2],
                [.exchanged (ourCommit E me σ nonce value) p1.bytes]⟩
        else ⟨none, σ, I, [], [e1 E me σ nonce value], [skel1], []⟩ := by
  have hd : (σ.bytes nonce ++ σ.bytes value).drop 32 = σ.bytes value := List.drop_left' hn
  simp only [joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
  cases h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 with
  | none =>
    simp_all [withAdv, fill, Payload.eval, InstrP.skel, InstrP.map, Wire.early, e1, ourCommit, skel1]
  | some p1 =>
    by_cases hl1 : p1.bytes.length = 32
    · cases h2 : adv.act (vD ++ [e1 E me σ nonce value, e2 σ nonce value]) skel2 with
      | none =>
        simp_all [withAdv, fill, Payload.eval, InstrP.skel, InstrP.map, Wire.early, idealStep, absorb,
          e1, e2, ourCommit, skel1, skel2]
      | some p2 =>
        by_cases hl2 : p2.bytes.length = 64
        · cases ha : accepts E.hash me (ourCommit E me σ nonce value) p1.bytes p2.bytes <;>
            simp_all [withAdv, fill, Payload.eval, InstrP.skel, InstrP.map, Wire.early, idealStep, absorb,
              e1, e2, ourCommit, skel1, skel2]
        · simp_all [withAdv, fill, Payload.eval, InstrP.skel, InstrP.map, Wire.early, idealStep, absorb,
            e1, e2, ourCommit, skel1, skel2]
    · simp_all [withAdv, fill, Payload.eval, InstrP.skel, InstrP.map, Wire.early, idealStep,
        e1, ourCommit, skel1]

/-- Against any adversary, `joint` leaves the engines' state as it was. -/
theorem joint_ideal (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    (withAdv E me adv (joint E.hash me nonce value) σ I vD).ideal = I ∧
      (withAdv E me adv (joint E.hash me nonce value) σ I vD).store = σ := by
  rw [withAdv_joint E me adv σ I vD nonce value hh hn hv]
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- When `joint` returns, the adversary saw exactly our commitment and our opening. -/
theorem joint_viewD_of_result (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) (x : Bytes)
    (h : (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = some x) :
    (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD = [e1 E me σ nonce value, e2 σ nonce value] := by
  rw [withAdv_joint E me adv σ I vD nonce value hh hn hv] at h ⊢
  revert h
  repeat' split
  all_goals simp

/-- **T3 for `Random.joint` (disclosure).** What the honest party releases to the adversary is a
prefix of [its commitment, its opening]. -/
theorem prand_disclosure (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD <+:
      [e1 E me σ nonce value, e2 σ nonce value] := by
  rw [withAdv_joint E me adv σ I vD nonce value hh hn hv]
  repeat' split
  all_goals simp

/-- **Commit before open.** If our opening reached the adversary, then the adversary had already
committed: its commitment `p1.bytes` is its choice from its prior view and our commitment alone,
and it is what the honest party received first. -/
theorem prand_commit_before_open (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32)
    (h : e2 σ nonce value ∈ (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD) :
    ∃ p1, adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1 ∧ p1.bytes.length = 32 ∧
      (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewH.head? =
        some ⟨Label.jointRandomCommitment, .bytes p1.bytes⟩ := by
  rw [withAdv_joint E me adv σ I vD nonce value hh hn hv] at h ⊢
  have hne : e2 σ nonce value ≠ e1 E me σ nonce value := by
    simp [e1, e2, Label.jointRandomCommitment, Label.jointRandomOpening]
  revert h
  cases h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 with
  | none => simp [hne]
  | some p1 =>
    by_cases hl1 : p1.bytes.length = 32
    · intro _
      refine ⟨p1, rfl, hl1, ?_⟩
      simp only [hl1, if_true]
      repeat' split
      all_goals rfl
    · simp [hl1, hne]

/-- **P-RAND (c).** A commitment equal to ours aborts. -/
theorem prand_c_copy_aborts (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) (p1 : PeerPart)
    (h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1)
    (hcopy : p1.bytes = ourCommit E me σ nonce value) :
    (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = none := by
  rw [withAdv_joint E me adv σ I vD nonce value hh hn hv, h1]
  simp only
  repeat' split
  all_goals simp_all [accepts]

/-- **Accepted results.** If the honest party accepts, its result is r ⊕ v, where the adversary
opened (·, v) against the commitment c' it sent before our opening, c' ≠ c. -/
theorem prand_accepted (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) (x : Bytes)
    (h : (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = some x) :
    ∃ p1 p2, adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1 ∧
      adv.act (vD ++ [e1 E me σ nonce value, e2 σ nonce value]) skel2 = some p2 ∧
      p1.bytes.length = 32 ∧ p2.bytes.length = 64 ∧
      E.hash (commitFrame tag me.other (p2.bytes.take 32) (p2.bytes.drop 32)) = p1.bytes ∧
      p1.bytes ≠ ourCommit E me σ nonce value ∧
      (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewH =
        [⟨Label.jointRandomCommitment, .bytes p1.bytes⟩, ⟨Label.jointRandomOpening, .bytes p2.bytes⟩] ∧
      x = xorBytes (σ.bytes value) (p2.bytes.drop 32) := by
  rw [withAdv_joint E me adv σ I vD nonce value hh hn hv] at h ⊢
  revert h
  cases h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 with
  | none => simp
  | some p1 =>
    by_cases hl1 : p1.bytes.length = 32
    · cases h2 : adv.act (vD ++ [e1 E me σ nonce value, e2 σ nonce value]) skel2 with
      | none => simp [hl1]
      | some p2 =>
        by_cases hl2 : p2.bytes.length = 64
        · cases ha : accepts E.hash me (ourCommit E me σ nonce value) p1.bytes p2.bytes
          · simp [hl1, hl2, ha]
          · intro h
            simp only [hl1, hl2, ha, if_true, Option.some.injEq] at h
            simp only [accepts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ha
            exact ⟨p1, p2, rfl, rfl, hl1, hl2, ha.1, ha.2, by simp [hl1, hl2], h.symm⟩
        · simp [hl1, hl2]
    · simp [hl1]

/-- The value the adversary opened, read from the honest party's view (the second half of its
opening), when the run got that far. -/
def advValue (o : Outcome Bytes) : Option Bytes :=
  match o.viewH with
  | [_, ⟨_, .bytes o'⟩] => some (o'.drop 32)
  | _ => none

/-- **idealCommit** (plan 7.0) for this flow and a family `S` of honest stores (the honest
party's randomness ranges over `S`): the value the adversary opens, whenever the honest party
accepts, is one fixed `v`, independent of the honest party's randomness. With an ideal
commitment the adversary's committed value is a function of what it saw before the commitment
exchange, and its opening must match it; this hypothesis states exactly that consequence. -/
def IdealCommit (S : Store → Prop) (v : Bytes) : Prop :=
  ∀ σ', S σ' → ∀ x, (withAdv E me adv (joint E.hash me nonce value) σ' I vD).result = some x →
    advValue (withAdv E me adv (joint E.hash me nonce value) σ' I vD) = some v

/-- **P-RAND (b).** Under `IdealCommit`, every accepted result is r ⊕ v for the one value `v`
(32 bytes), and r ↦ r ⊕ v is a bijection of 32-byte strings (its own inverse): with r uniform,
the result is uniform. -/
theorem prand_b_ideal (hh : ∀ m, (E.hash m).length = 32) (S : Store → Prop)
    (hS : ∀ σ', S σ' → (σ'.bytes nonce).length = 32 ∧ (σ'.bytes value).length = 32)
    (v : Bytes) (hic : IdealCommit E me adv I vD nonce value S v) :
    (∀ σ', S σ' → ∀ x, (withAdv E me adv (joint E.hash me nonce value) σ' I vD).result = some x →
        x = xorBytes (σ'.bytes value) v ∧ v.length = 32) ∧
      ∀ r : Bytes, r.length = 32 → v.length = 32 →
        (xorBytes r v).length = 32 ∧ xorBytes (xorBytes r v) v = r := by
  refine ⟨fun σ' hσ x hx => ?_, fun r hr hv => ?_⟩
  · obtain ⟨hn, hv'⟩ := hS σ' hσ
    have hval := hic σ' hσ x hx
    obtain ⟨p1, p2, _, _, _, hl2, _, _, hview, hxe⟩ :=
      prand_accepted E me adv σ' I vD nonce value hh hn hv' x hx
    simp only [advValue, hview, Option.some.injEq] at hval
    subst hval
    exact ⟨hxe, by simp [hl2]⟩
  · obtain ⟨h1, h2⟩ := xor_bijective v r (by rw [hr, hv])
    exact ⟨by rw [h1, hv], h2⟩

end Adversary

end TlsMpc.Node.Flows.Random
