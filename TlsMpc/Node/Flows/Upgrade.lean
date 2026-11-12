import TlsMpc.Node.Flows.Random
import TlsMpc.Node.Local.WebSocketAccept

/-!
# `Upgrade.publicUpgrade`: the unauthenticated WebSocket upgrade's nonce and accept value (op 45)

REORGANIZATION_PLAN.md stage S9, flow `Upgrade.public` (named `publicUpgrade`: `public` is a
keyword). Advance work in a new file; uses `TlsMpc/Node/Local/WebSocketAccept.lean` (read-only).

Today's op 45 (`tls_worker_v3.cpp:267`, `service_kernels.h` `upgrade_public`): a joint random
nonce (the first 16 bytes of `joint_random`), then, in the clear, `nonce ‖ accept` with
accept = base64(SHA-1(base64(nonce) ‖ GUID)). Here: `Random.joint`, then
`WebSocketAccept.upgradePublic` on public values. The script releases nothing beyond
`Random.joint`'s commitment and opening; the accept value is computed locally from public data.

NOT MOVED BY THIS FILE (for the S9 integration): op 45 also sets the legacy service's state
(`started`, `public_receive`, `accept_bytes`, used by the later public receive and the
authenticated upgrade's reply). When the controller switches op 45 to this flow, the legacy
library must be told the nonce and accept value (a legacy entry point, or the state moves with
S16). Until then the C++ op 45 stays in use.

PROVED: `upgrade_honest` (T4-UPGRADE, honest parties, ideal model): both parties return
nonce ‖ acceptOf (keyOf nonce) (RFC 6455 section 4.2.2, `WebSocketAccept.accept_spec`) with
nonce the first 16 bytes of r_A ⊕ r_B (P-RAND (a)). `publicUpgrade_wf`: the script is well formed.
`publicUpgrade_reveals`, `publicUpgrade_viewD_kinds`: it releases only under `Random.jointKinds`.
-/

namespace TlsMpc.Node.Flows.Upgrade

open TlsMpc.Node.Engine
open TlsMpc.Local.WebSocketAccept (upgradePublic acceptOf keyOf acceptFast acceptFast_spec)

def toBV (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat
def toU8 (b : BitVec 8) : UInt8 := UInt8.ofNat b.toNat

/-- **Op 45.** `nonce` and `value` are the byte-store slots `Random.joint` uses. Returns the
44 public bytes nonce ‖ accept. -/
def publicUpgrade (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) : Script Bytes := do
  let j ← Random.joint hash me nonce value
  match upgradePublic ((j.take 16).map toBV) with
  | .ok reply => pure (reply.map toU8)
  | .error e => Script.abort e

theorem publicUpgrade_wf (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party)
    (nonce value : Nat) (c : Ctx) : WF sigs c (publicUpgrade hash me nonce value) := by
  have hc : maxExchange = 65536 := rfl
  simp only [publicUpgrade, Random.joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq,
    Script.bind_step]
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
      · simp only [Script.bind_done]
        split
        · exact WF.done _ _
        · exact WF.abort _ _
      · exact WF.abort _ _
    | _ => exact WF.abort _ _
  | _ => exact WF.abort _ _

/-- **The reveal list:** the upgrade releases exactly what `Random.joint` does (`jointKinds`: the
commitment and its opening); the nonce and accept value are computed from those. The kind
`upgradeNonce` (code 22) is the controller's name for the result, never a label on the wire. -/
theorem publicUpgrade_reveals (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) :
    Reveals Random.jointKinds (publicUpgrade hash me nonce value) :=
  Every.bind (Random.joint_reveals hash me nonce value) (fun j => by
    split
    · exact Every.done _
    · exact Every.abort _)

/-- **T3 for the upgrade in the reveal list's vocabulary**, against any adversary. -/
theorem publicUpgrade_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonce value : Nat) :
    ∀ r ∈ (withAdv E me adv (publicUpgrade E.hash me nonce value) σ I vD).viewD,
      ∃ k ∈ Random.jointKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (publicUpgrade_reveals E.hash me nonce value) σ I vD

/-- The sender's wires of the upgrade fit the pipe. -/
theorem publicUpgrade_bounded (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) :
    Every Instr.Bounded (publicUpgrade hash me nonce value) :=
  Every.bind (Random.joint_bounded hash me nonce value) (fun j => by
    split
    · exact Every.done _
    · exact Every.abort _)

/-- **T4-UPGRADE (honest parties).** Both return nonce ‖ acceptOf (keyOf nonce), the RFC 6455
accept value for the key base64(nonce), with nonce the first 16 bytes of r_A ⊕ r_B. Hypotheses
as `Random.prand_a_honest`. -/
theorem upgrade_honest (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame Random.tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (publicUpgrade E.hash .a nA vA) (publicUpgrade E.hash .b nB vB) σA σB I).result =
      some ((((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV ++
              acceptOf (keyOf (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV))).map toU8,
            (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV ++
              acceptOf (keyOf (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV))).map toU8) := by
  have dA : (σA.bytes nA ++ σA.bytes vA).drop 32 = σA.bytes vA := List.drop_left' hnA
  have tA : (σA.bytes nA ++ σA.bytes vA).take 32 = σA.bytes nA := List.take_left' hnA
  have dB : (σB.bytes nB ++ σB.bytes vB).drop 32 = σB.bytes vB := List.drop_left' hnB
  have tB : (σB.bytes nB ++ σB.bytes vB).take 32 = σB.bytes nB := List.take_left' hnB
  have hc' := Ne.symm hc
  have hlen : (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV).length = 16 := by
    simp [Random.xorBytes_length, hvA, hvB]
  have hup : upgradePublic (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV) =
      .ok (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV ++
        acceptOf (keyOf (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV))) :=
    TlsMpc.Local.WebSocketAccept.accept_spec _ hlen
  simp only [List.map_take] at hup
  simp only [publicUpgrade, Random.joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq,
    Script.bind_step]
  simp [jointRun, fill, Payload.eval, InstrP.skel, InstrP.map, idealStep, Wire.part, absorb, hh, hnA, hvA,
    hnB, hvB, Random.accepts, dA, tA, dB, tB, hc, hc', Party.other, Random.xorBytes_comm (σB.bytes vB), hup]

end TlsMpc.Node.Flows.Upgrade
