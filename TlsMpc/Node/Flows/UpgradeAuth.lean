import TlsMpc.Node.Flows.Upgrade
import TlsMpc.Node.Flows.Account
import TlsMpc.KernelSpecs.SignalKernels

/-!
# `Upgrade.authenticated`: the authenticated WebSocket upgrade on the script account state (op 32)

REORGANIZATION_PLAN.md stage S16 (STACK_NOTES J11). Replaces `tls_worker_v3.cpp` op 32 (line 308)
and `service_kernels.h` `upgrade` (474-494): a joint random nonce (the first 16 bytes of
`joint_random`), then the request with the account's credentials inside the kernel:

  * credentials combined (op 55 opened them from the account record: `Account.State.credentials`):
    `signal-upgrade 22` on credentials ‖ nonce;
  * credentials as the two parties' XOR shares (op 47: `Account.State.shares`):
    `signal-upgrade-shared 22` on shareA ‖ shareB ‖ nonce (neither party alone can open the socket).

The request's `content` stays in the engines (a private output, `priv "content"`); its size is
public (a function of the password length only, `requestBytes`). The expected `Sec-WebSocket-Accept`
is a public function of the public nonce, computed locally (`WebSocketAccept.upgradePublic`, as for
op 45). What the C++ also did and is NOT done here (as for op 45, `Upgrade.lean`): `public_receive`,
`accept_bytes` and the `ws-initial` parser states of the legacy service: with the record layer in
Lean (`tls`) nothing reads them (the controllers parse server records in the clear).

The legacy TEST FIXTURE branch (credentials entered in the clear by A when neither is held) is not
kept: no credentials, no upgrade (`credsOf` = `none`: the script aborts).

PROVED:
  * `requestScript_wf`, `authenticated_wf`: well formed from any context in which the credential
    handles are live with the credentials' marks (304 private bits, not once) and below the block,
    the kernel's signature has the concatenation's width.
  * `authenticated_reveals`: releases only `Random.jointKinds` (the commitment and opening of the
    nonce); the request is never opened. Kind `upgradeAccept` (code 23) is the controller's name for
    the returned accept value, computed from public data, never a label on the wire
    (`authenticated_kinds_registered`).
  * `requestShared_value`, `requestPlain_value` (function level, composed with the kernel specs
    `signalUpgradeShared_spec` / `signalUpgrade_spec`): the kernel's output on the bundle the
    script concatenates is `RelayUpgrade.request` on the credentials (the XOR of the shares) ‖
    nonce.
  * `accept_value`: the accept value returned is RFC 6455's `acceptOf (keyOf nonce)` of the nonce in
    the request (`WebSocketAccept.accept_spec`).
-/

namespace TlsMpc.Node.Flows.UpgradeAuth

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Local.WebSocketAccept (upgradePublic acceptOf keyOf)

/-- The password's byte length (`service_kernels.h` `PASSWORD`). -/
def passwordBytes : Nat := 22

def plainName : Bytes := ascii ("signal-upgrade " ++ toString passwordBytes)
def sharedName : Bytes := ascii ("signal-upgrade-shared " ++ toString passwordBytes)

/-- The account's credentials as the engines hold them. -/
inductive Creds where
  | combined (c : BoolH)
  | shares (a b : BoolH)

def Creds.parts : Creds → List BoolH
  | .combined c => [c]
  | .shares a b => [a, b]

def Creds.name : Creds → Bytes
  | .combined _ => plainName
  | .shares _ _ => sharedName

/-- Which credentials the account state holds (combined first, as the C++). -/
def credsOf (a : Account.State) : Option Creds :=
  match a.credentials, a.shares with
  | some c, _ => some (.combined c)
  | none, some (x, y) => some (.shares x y)
  | none, none => none

/-- The request's public byte length (the kernel's one output; the same for both kernels). -/
def requestBytes : Nat :=
  match (HybridKernel.signalUpgradeShared passwordBytes).outputs with
  | [o] => o.value.length
  | _ => 0

/-- The instructions of the request (handles `n … n + 2`): the nonce as public bits, the bundle
credentials ‖ nonce, the kernel, the temporaries freed. -/
def requestBlock (n : Nat) (cr : Creds) (nonce : B8) : List Instr :=
  [.boolPublic ⟨n⟩ (bitsOf nonce), .concat ⟨n + 1⟩ (cr.parts ++ [⟨n⟩]), .run ⟨n + 2⟩ cr.name 1 ⟨n + 1⟩,
   .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]

/-- **The request in the engines**: its handle (`n + 2`, private, not once). -/
def requestScript (n : Nat) (cr : Creds) (nonce : B8) : Script BoolH :=
  if nonce.length = 16 then seqs (requestBlock n cr nonce) (.done ⟨n + 2⟩) else .abort "upgrade nonce"

/-- **Op 32.** `nonceSlot`, `valueSlot`: `Random.joint`'s byte slots; Boolean ids `n … n + 2`.
Returns the request's handle and the expected accept value (28 public bytes). -/
def authenticated (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot n : Nat) (cr : Creds) :
    Script (BoolH × Bytes) :=
  (Random.joint hash me nonceSlot valueSlot).bind fun j =>
    match upgradePublic ((j.take 16).map Upgrade.toBV) with
    | .ok reply =>
      (requestScript n cr ((j.take 16).map Upgrade.toBV)).bind fun h => .done (h, (reply.drop 16).map Upgrade.toU8)
    | .error e => .abort e

/-! ## The reveal list -/

theorem requestScript_silent (n : Nat) (cr : Creds) (nonce : B8) : Reveals [] (requestScript n cr nonce) := by
  unfold requestScript
  split
  · refine every_seqs (Every.done _) _ (fun i hi => ?_)
    simp only [requestBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact LabelIn.of_none rfl
  · exact Every.abort _

/-- **T3 for op 32 in the reveal list's vocabulary**: only `Random.joint`'s commitment and opening;
the credentials and the request are never opened. -/
theorem authenticated_reveals (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot n : Nat) (cr : Creds) :
    Reveals Random.jointKinds (authenticated hash me nonceSlot valueSlot n cr) := by
  unfold authenticated
  refine Every.bind (Random.joint_reveals hash me nonceSlot valueSlot) fun j => ?_
  split
  · exact Every.bind ((requestScript_silent n cr _).mono (by simp)) fun _ => Every.done _
  · exact Every.abort _

theorem authenticated_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonceSlot valueSlot n : Nat) (cr : Creds) :
    ∀ r ∈ (withAdv E me adv (authenticated E.hash me nonceSlot valueSlot n cr) σ I vD).viewD,
      ∃ k ∈ Random.jointKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (authenticated_reveals E.hash me nonceSlot valueSlot n cr) σ I vD

/-- Every kind op 32 releases under, and the result's kind, are registered. -/
theorem authenticated_kinds_registered : ∀ k ∈ TlsMpc.Node.RevealKind.upgradeAccept :: Random.jointKinds,
    k ∈ Label.kinds ∨ k = .upgradeAccept := by
  intro k hk
  simp only [List.mem_cons] at hk
  rcases hk with rfl | hk
  · exact Or.inr rfl
  · exact Or.inl (by revert hk; revert k; decide)

/-! ## Well-formedness -/

/-- The credentials' marks: 304 private bits (op 47's inputs; op 55's slice of the opened content). -/
def credInfo : BoolInfo := ⟨List.replicate (8 * Account.credentialBytes) .never, false⟩

theorem credLen : ∀ l : List BoolH,
    ((l.map (fun _ => credInfo)).map BoolInfo.marks).flatten.length = 8 * Account.credentialBytes * l.length
  | [] => rfl
  | _ :: l => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, credLen l, List.length_cons]
    simp only [credInfo, List.length_replicate, Account.credentialBytes]
    omega

theorem useBools_keepAll (c : Ctx) (f : BoolH → BoolInfo) :
    ∀ hs : List BoolH, (∀ h ∈ hs, c.bool? h = some (f h) ∧ (f h).once = false) →
      c.useBools hs = some (hs.map f, c)
  | [], _ => useBools_nil c
  | h :: hs, hh => by
    have h0 := hh h (by simp)
    exact useBools_cons (useBool_keep h0.1 h0.2) (useBools_keepAll c f hs fun g hg => hh g (by simp [hg]))

/-- **The request is well formed** from a context in which the credential handles are live with the
credentials' marks and below `n`, no id from `n` on was defined, and the kernel's signature reads
the bundle credentials ‖ nonce. -/
theorem requestScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (cr : Creds) (nonce : B8)
    (outM : List Mark) (hf : Fresh c n) (hp : ∀ p ∈ cr.parts, p.id < n ∧ c.bool? p = some credInfo)
    (hsig : sigs cr.name = some ⟨8 * (Account.credentialBytes * cr.parts.length + 16), outM⟩)
    (hout : outM.length ≤ maxWidth) : WF sigs c (requestScript n cr nonce) := by
  unfold requestScript
  split
  · next hn =>
    simp only [requestBlock, seqs_cons, seqs_nil]
    let ni : BoolInfo := ⟨List.replicate (bitsOf nonce).length .pub, false⟩
    have hbl : (bitsOf nonce).length = 128 := by simp [hn]
    have hf1 := hf.push n (Nat.le_refl n) ni
    refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp [hbl, maxWidth])) ?_
    let nh : BoolH := ⟨n⟩
    let f : BoolH → BoolInfo := fun h => if h.id = n then ni else credInfo
    have hall : ∀ h ∈ cr.parts ++ [nh], (push c n ni).bool? h = some (f h) ∧ (f h).once = false := by
      intro h hh
      simp only [List.mem_append, List.mem_singleton] at hh
      rcases hh with hh | hh
      · have hne : h.id ≠ n := by have := (hp h hh).1; omega
        refine ⟨?_, by simp [f, hne, credInfo]⟩
        rw [bool?_push_of_ne _ _ _ _ hne, (hp h hh).2]
        simp [f, hne]
      · subst hh
        exact ⟨by rw [bool?_push_self]; simp [f, nh], by simp [f, ni, nh]⟩
    have hmap : (cr.parts ++ [nh]).map f = cr.parts.map (fun _ => credInfo) ++ [ni] := by
      rw [List.map_append]
      congr 1
      · apply List.map_congr_left
        intro h hh
        have hne : h.id ≠ n := by have := (hp h hh).1; omega
        simp [f, hne]
      · simp [f, nh]
    have hlen : (((cr.parts ++ [nh]).map f).map BoolInfo.marks).flatten.length =
        8 * Account.credentialBytes * cr.parts.length + 128 := by
      rw [hmap, List.map_append, List.flatten_append, List.length_append, credLen]
      simp [ni, hbl]
    refine WF_seq sigs _ _ _ _ (check_concat sigs (useBools_keepAll _ f _ hall) hf1
      (by rw [hlen]; cases cr <;> simp [Creds.parts, Account.credentialBytes, maxWidth])) ?_
    have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨(((cr.parts ++ [nh]).map f).map BoolInfo.marks).flatten,
      ((cr.parts ++ [nh]).map f).any BoolInfo.once⟩
    have honce : ((cr.parts ++ [nh]).map f).any BoolInfo.once = false := by
      rw [hmap]; simp [credInfo, ni]
    refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos
      (useBool_keep (bool?_push_self _ _ _) honce) (by rw [hlen]; simp [Nat.mul_add, Nat.mul_assoc]) hf2 (by decide)
      (by simpa using hout)) ?_
    refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push])) ?_
    refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
    exact WF.done _ _
  · exact WF.abort _ _

/-- `Random.joint` defines no handle: it leaves the context as it was. -/
theorem joint_wfp (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) (c : Ctx) :
    WFP sigs (fun c' _ => c' = c) c (Random.joint hash me nonce value) := by
  have hc : maxExchange = 65536 := rfl
  simp only [Random.joint, Script.exchange, Script.ensure, Script.bind_eq, Script.pure_eq, Script.bind_step]
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
      · simp only [Script.bind_done]
        exact WFP.done _ _ rfl
      · exact WFP.abort _ _
    | _ => exact WFP.abort _ _
  | _ => exact WFP.abort _ _

/-- **Op 32 is well formed** (the request's conditions, `requestScript_wf`). -/
theorem authenticated_wf (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot n : Nat)
    (cr : Creds) (c : Ctx) (outM : List Mark) (hf : Fresh c n)
    (hp : ∀ p ∈ cr.parts, p.id < n ∧ c.bool? p = some credInfo)
    (hsig : sigs cr.name = some ⟨8 * (Account.credentialBytes * cr.parts.length + 16), outM⟩)
    (hout : outM.length ≤ maxWidth) : WF sigs c (authenticated hash me nonceSlot valueSlot n cr) := by
  unfold authenticated
  refine (WFP.bind (joint_wfp sigs hash me nonceSlot valueSlot c) fun c' j hc' => ?_).wf (Q := fun _ _ => True)
  subst hc'
  split
  · exact WFP.bind (requestScript_wf sigs c' n cr _ outM hf hp hsig hout).wfp fun _ _ _ => WFP.done _ _ trivial
  · exact WFP.abort _ _

/-! ## Values (function level, composed with the kernel specifications) -/

open Std.Tactic.BVDecide
open Signal

theorem lookup_assignOf (x : B8) (start count : Nat) (h : start + count ≤ x.length) :
    (ByteCircuit.inputBytes start count).map (BVExpr.eval (assignOf x)) = (x.drop start).take count :=
  inputValue_assignOf x start count h

/-- **The shared kernel on the bundle the script concatenates** (shareA ‖ shareB ‖ nonce) is
`RelayUpgrade.request` on (shareA ⊕ shareB) ‖ nonce (`signalUpgradeShared_spec`). -/
theorem requestShared_value (a b nonce : B8) (ha : a.length = 16 + passwordBytes) (hb : b.length = 16 + passwordBytes)
    (hn : nonce.length = 16) :
    kernelOut (HybridKernel.signalUpgradeShared passwordBytes) (a ++ b ++ nonce) =
      RelayUpgrade.request ByteAuth.concrete passwordBytes (List.zipWith (· ^^^ ·) a b ++ nonce) := by
  have h := TlsMpc.KernelSpecs.SignalKernels.signalUpgradeShared_spec passwordBytes (assignOf (a ++ b ++ nonce))
  unfold kernelOut
  rw [h]
  have hx : (a ++ b ++ nonce).length = 92 := by simp [ha, hb, hn, passwordBytes]
  have gA := lookup_assignOf (a ++ b ++ nonce) 0 38 (by omega)
  have gB := lookup_assignOf (a ++ b ++ nonce) 38 38 (by omega)
  have gN := lookup_assignOf (a ++ b ++ nonce) 76 16 (by omega)
  have ea : ((a ++ b ++ nonce).drop 0).take 38 = a := by
    simp only [List.drop_zero, List.append_assoc]
    rw [List.take_left' (by simp [ha, passwordBytes])]
  have eb : ((a ++ b ++ nonce).drop 38).take 38 = b := by
    simp only [List.append_assoc]
    rw [List.drop_left' (by simp [ha, passwordBytes]), List.take_left' (by simp [hb, passwordBytes])]
  have en : ((a ++ b ++ nonce).drop 76).take 16 = nonce := by
    have e76 : (76 : Nat) = (a ++ b).length := by simp [ha, hb, passwordBytes]
    rw [e76, List.drop_left' rfl, List.take_of_length_le (by simp [hn])]
  rw [ea] at gA; rw [eb] at gB; rw [en] at gN
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, HybridKernel.lookup, HybridKernel.lookupFrom,
    TlsMpc.KernelSpecs.SignalKernels.sharedInputs, passwordBytes] at gA gB gN ⊢
  simp only [List.append_assoc] at gA gB gN
  simp [gA, gB, gN, HybridKernel.Shape.variables]

/-- **The plain kernel on credentials ‖ nonce** is `RelayUpgrade.request` on them
(`signalUpgrade_spec`). -/
theorem requestPlain_value (cred nonce : B8) (hc : cred.length = 16 + passwordBytes) (hn : nonce.length = 16) :
    kernelOut (HybridKernel.signalUpgrade passwordBytes) (cred ++ nonce) =
      RelayUpgrade.request ByteAuth.concrete passwordBytes (cred ++ nonce) := by
  have h := TlsMpc.KernelSpecs.SignalKernels.signalUpgrade_spec passwordBytes (assignOf (cred ++ nonce))
  unfold kernelOut
  rw [h]
  have gC := lookup_assignOf (cred ++ nonce) 0 38 (by simp [hc, hn, passwordBytes])
  have gN := lookup_assignOf (cred ++ nonce) 38 16 (by simp [hc, hn, passwordBytes])
  have ec : ((cred ++ nonce).drop 0).take 38 = cred := by
    simp only [List.drop_zero]
    rw [List.take_left' (by simp [hc, passwordBytes])]
  have en : ((cred ++ nonce).drop 38).take 16 = nonce := by
    rw [List.drop_left' (by simp [hc, passwordBytes]), List.take_of_length_le (by simp [hn])]
  rw [ec] at gC; rw [en] at gN
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, HybridKernel.lookup, HybridKernel.lookupFrom,
    TlsMpc.KernelSpecs.SignalKernels.upgradeInputs, passwordBytes] at gC gN ⊢
  simp [gC, gN, HybridKernel.Shape.variables]

/-- **The accept value op 32 returns** for a joint randomness `j` (at least 16 bytes): RFC 6455's
accept value of the request's nonce (the first 16 bytes), `acceptOf (keyOf nonce)`. -/
theorem accept_value (j : Bytes) (hj : 16 ≤ j.length) :
    upgradePublic ((j.take 16).map Upgrade.toBV) =
      .ok ((j.take 16).map Upgrade.toBV ++ acceptOf (keyOf ((j.take 16).map Upgrade.toBV))) :=
  TlsMpc.Local.WebSocketAccept.accept_spec _ (by simp; omega)

end TlsMpc.Node.Flows.UpgradeAuth
