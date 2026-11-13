import TlsMpc.Node.Flows.Registry
import TlsMpc.Node.Flows.SendProofs
import TlsMpc.Node.Flows.RefreshFirstProofs

/-!
# The joins: S11's curve flows as the parameters of S12–S15 (scripts and their kinds)

Written when the stages were joined on `scripts-stack` (STACK_NOTES.md). No branch definition or
theorem statement changes; this file only INSTANTIATES the parameters the branches left open, with
the thinnest adapters that make the types fit, and states the composed `Reveals` facts. The IO
side (the runner, store slots, the mask pool) is in `Flows/JoinBackend.lean`. No I/O here; no
emitter imports this module.

  * S12 `TlsBackend.KeyAgreement.agree`'s engine part: `splitAgreeWord` = S11 `Curve.splitAgree`,
    abort on the zero flag (RFC 8446 7.4.2), S10 `Convert.fieldToWord` (P-F2W), the field handle
    freed. Kinds `keyAgreementKinds` = P-SPLIT's ∪ P-F2W's. (`begin` is S11 `Curve.splitBegin`
    unchanged: `Curve.splitKinds`.)
  * S13 `SendBackend.Curve.ephemeral`'s engine part: `ephemeralWord` = S11 `Curve.offsetStep`, then
    `fieldToWord` of the agreement. Kinds `ephemeralKinds` = P-OFFSET's ∪ P-F2W's (plus
    `Random.jointKinds` for the joint public offset τ, run by the IO side).
  * S14 `Receive.Curve`: `receiveCurve` = S14's own `Curve.withPrograms` (signature and base check
    through the `program` instruction) with `agree := receiveAgree`: per job the swap bits by S10's
    `Convert.sharedBits` (P-BITS) from a store slot of this party's swap-bit shares, the point
    (a handle, or the public 9), S11's ladder `Curve.agree` (all jobs in one program instruction
    and one masked-quotient round), abort on a zero flag, S14's `toWord` per result. ADAPTER: the
    store slots (`AgreeSlots`) are parameters — see the mismatch note on `AgreeSlots`.
  * S15 `Refresh.CurveOps`: `refreshOps`, from the same pieces run on the session counters the
    caller allocates (`runAt`: S14's `Gen` on a table holding just those counters and a pool of
    masks taken for this call): `lift` = W2F, `xeddsa-recover`, F2W ×3; `check` = W2F ×2,
    B2F ×2, `xeddsa-check` ×2, F2W ×4; `agree` = W2F of the points, then `receiveAgree` on the seven
    jobs of `service_kernels.h` line 850 (dh1, dh2, dh3, ratchetAgreement, basePublic,
    ratchetPublic, dh4). `refreshOps_reveals` DISCHARGES S15's hypothesis `CurveOps.Reveals`.
  * S15's send parameter, S13's `bundle-seal`: `join_first_wired` derives `first_wired`'s two
    binding hypotheses (`hconv`, `hpend`) from S13's `bundleSeal_get` and S15's `stored_record`,
    for the bundle S13's `devicesScript` builds (certificate ‖ stored record, pending block, ...).
    What stays assumed is stated as the theorem's hypotheses `hcert`, `hpend`: that the BYTES in
    the handles S13's script concatenates are the session's certificate input and outputs (a
    run-level fact about handle contents, S13-1 / F35-style).
-/

namespace TlsMpc.Node.Flows.Join

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs every_seq every_seqs bitsOf B8)
open TlsMpc.FieldDag (F ofNat)
open TlsMpc.Node (RevealKind)
open TlsMpc.Node.Flows.Receive (Gen RevealsG Job Scalar Point)

/-! ## S12: the X25519 agreement of the TLS handshake -/

/-- **The TLS agreement as a word**: S11's split agreement (handles `f0 … f0 + 12`), abort on the
zero flag, S10's field to word (bools `n0 … n0 + 2`, field `f1`, word mask `m`); the field handle
is freed. The result: a fresh 255-bit handle (never, not once), `deriveScript`'s input. -/
def splitAgreeWord (f0 tSlot maskSlot n0 f1 : Nat) (m : Conv.WordMask) : Script BoolH :=
  (Curve.splitAgree f0 tSlot maskSlot).bind fun r =>
    if r.2 then .abort "X25519 agreement: zero"
    else (Convert.fieldToWord n0 f1 r.1 m).bind fun w => seq (.freeField r.1) (.done w)

def keyAgreementKinds : List RevealKind := Curve.splitKinds ++ Convert.f2wKinds

theorem splitAgreeWord_reveals (f0 tSlot maskSlot n0 f1 : Nat) (m : Conv.WordMask) :
    Reveals keyAgreementKinds (splitAgreeWord f0 tSlot maskSlot n0 f1 m) := by
  unfold splitAgreeWord
  refine Every.bind ((Curve.splitAgree_reveals f0 tSlot maskSlot).mono fun k hk => List.mem_append_left _ hk)
    fun r => ?_
  split
  · exact Every.abort _
  · exact Every.bind ((Convert.f2w_reveals n0 f1 r.1 m).mono fun k hk => List.mem_append_right _ hk)
      fun _ => every_seq (LabelIn.of_none rfl) (Every.done _)

/-! ## S13: the ephemeral pair of a send -/

/-- **A message's ephemeral pair**: S11's offset step on the contact's prepared offset agreement
(`edwards-offset-sum`, handles `f0 … f0 + 387`, its 128 masks from `maskSlot`), then field to word of
the agreement (bools `n0 … n0 + 2`, field `f1`); the field handle is freed. The result: the public
u-coordinate of K₀ + τ·B and the agreement word. -/
def ephemeralWord (f0 maskSlot n0 f1 : Nat) (st : Curve.OffsetState) (τ : Nat) (m : Conv.WordMask) :
    Script (F × BoolH) :=
  (Curve.offsetStep f0 maskSlot st τ).bind fun r =>
    (Convert.fieldToWord n0 f1 r.2 m).bind fun w => seq (.freeField r.2) (.done (r.1, w))

def ephemeralKinds : List RevealKind := Curve.offsetKinds ++ Convert.f2wKinds

theorem ephemeralWord_reveals (f0 maskSlot n0 f1 : Nat) (st : Curve.OffsetState) (τ : Nat) (m : Conv.WordMask) :
    Reveals ephemeralKinds (ephemeralWord f0 maskSlot n0 f1 st τ m) := by
  unfold ephemeralWord
  exact Every.bind ((Curve.offsetStep_reveals f0 maskSlot st τ).mono fun k hk => List.mem_append_left _ hk)
    fun r => Every.bind ((Convert.f2w_reveals n0 f1 r.2 m).mono fun k hk => List.mem_append_right _ hk)
      fun _ => every_seq (LabelIn.of_none rfl) (Every.done _)

/-! ## S14: the receive agreements -/

/-- **The store slots the ladder agreements read** (THE ADAPTER'S PARAMETER). `coins s`: this
party's 252 swap-bit shares of scalar `s` as coins (bits 2 … 253 of the clamped scalar's
`swap_bit`, party A's with the top bit; `X25519SwapBits.swapBit_shares`); `masks`: this party's
fresh quotient-mask contributions, one element per job.

MISMATCH (STACK_NOTES.md, join table): S14's `Job` names a scalar by the BYTE slot holding it
(`own slot`, `fresh slot`) and `Gen` has no local step, but S11's ladder needs the scalar as
XOR-shared swap bits in a COINS slot (a local computation on the party's own bytes, decision D1)
and a FRESH mask slot per quotient round. Nothing in S14's `Gen` state supplies per-call slots, so
`ReceiveBackend` (which stashes the byte slots and calls `curve` once per message) would have to
stash these too and hand them in; reusing `masks` across two calls in one message would reuse
mask contributions (the quotients' openings `z·m` would then reveal a ratio). -/
structure AgreeSlots where
  coins : Scalar → Nat
  masks : Nat

/-- One job's swap bits as field bits (P-BITS; handles `f … f + 5·252 − 1`, the inputs and checks
freed). -/
def jobBits (sl : AgreeSlots) (j : Job) : Gen (List FieldH) := do
  let f ← Receive.Gen.allocF (5 * 252)
  let bs ← Receive.Gen.lift (Convert.sharedBits f 252 (sl.coins j.scalar))
  Receive.Gen.freeFields (Convert.bitsA f 252 ++ Convert.bitsB f 252 ++ Convert.bitsChk f 252)
  pure bs

/-- The point of a job, and the handles made for it (the public 9 for `.base`). -/
def jobPoint : Point → Gen (FieldH × List FieldH)
  | .handle h => pure (h, [])
  | .base => do
    let p ← Receive.publicField (ofNat 9)
    pure (p, [p])

/-- The ladder inputs of the jobs, and the handles made for them. -/
def jobsIn (sl : AgreeSlots) : List Job → Gen (List (List FieldH × FieldH) × List FieldH)
  | [] => pure ([], [])
  | j :: js => do
    let b ← jobBits sl j
    let p ← jobPoint j.point
    let rest ← jobsIn sl js
    pure ((b, p.1) :: rest.1, b ++ p.2 ++ rest.2)

/-- The agreements as words (S14's `toWord`: masks from the pool). -/
def wordsOf : List (FieldH × Bool) → Gen (List BoolH)
  | [] => pure []
  | r :: rs => do
    let w ← Receive.toWord r.1
    let ws ← wordsOf rs
    pure (w :: ws)

/-- **S14's `Curve.agree` from S11's ladder**: the jobs' swap bits and points, `x25519-fast` on all
of them in one instruction and one masked-quotient round (handles `f … f + 7n`), abort on a zero
flag, the results as fresh words; everything this function made is freed, its inputs are not. -/
def receiveAgree (sl : AgreeSlots) (jobs : List Job) : Gen (List BoolH) := do
  let ins ← jobsIn sl jobs
  let f ← Receive.Gen.allocF (7 * jobs.length + 1)
  let rs ← Receive.Gen.lift (Curve.agree f sl.masks ins.1)
  if rs.any (·.2) then Receive.Gen.fail "X25519 agreement: zero" else do
  let ws ← wordsOf rs
  Receive.Gen.freeFields (ins.2 ++ Curve.hs (f + 1) (2 * jobs.length) ++ rs.map (·.1))
  pure ws

def receiveAgreeKinds : List RevealKind := Curve.agreeKinds ++ Convert.bitsKinds ++ Convert.f2wKinds

theorem jobBits_reveals (sl : AgreeSlots) (j : Job) : RevealsG receiveAgreeKinds (jobBits sl j) := by
  unfold jobBits
  refine RevealsG.bind (RevealsG.allocF _) fun f => ?_
  refine RevealsG.bind (RevealsG.lift ((Convert.bits_reveals f 252 _).mono (by decide))) fun bs => ?_
  exact RevealsG.bind (Receive.RevealsG.freeFields _) fun _ => RevealsG.pure _

theorem jobPoint_reveals (p : Point) : RevealsG receiveAgreeKinds (jobPoint p) := by
  cases p with
  | handle h => exact RevealsG.pure _
  | base => exact RevealsG.bind (Receive.publicField_reveals _) fun _ => RevealsG.pure _

theorem jobsIn_reveals (sl : AgreeSlots) : ∀ jobs, RevealsG receiveAgreeKinds (jobsIn sl jobs)
  | [] => RevealsG.pure _
  | j :: js => by
    unfold jobsIn
    exact RevealsG.bind (jobBits_reveals sl j) fun _ => RevealsG.bind (jobPoint_reveals _) fun _ =>
      RevealsG.bind (jobsIn_reveals sl js) fun _ => RevealsG.pure _

theorem wordsOf_reveals : ∀ rs, RevealsG receiveAgreeKinds (wordsOf rs)
  | [] => RevealsG.pure _
  | r :: rs => by
    unfold wordsOf
    exact RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ =>
      RevealsG.bind (wordsOf_reveals rs) fun _ => RevealsG.pure _

/-- **The joined receive agreements declare their kinds** (from every state, every job list). -/
theorem receiveAgree_reveals (sl : AgreeSlots) (jobs : List Job) (st : Receive.St) :
    Reveals receiveAgreeKinds (receiveAgree sl jobs st) := by
  unfold receiveAgree
  refine RevealsG.bind (jobsIn_reveals sl jobs) (fun ins => ?_) st
  refine RevealsG.bind (RevealsG.allocF _) fun f => ?_
  refine RevealsG.bind (RevealsG.lift ((Curve.agree_reveals f sl.masks ins.1).mono (by decide))) fun rs => ?_
  refine RevealsG.ite (RevealsG.fail _) ?_
  exact RevealsG.bind (wordsOf_reveals rs) fun _ =>
    RevealsG.bind (Receive.RevealsG.freeFields _) fun _ => RevealsG.pure _

/-- **S14's curve parameter, joined**: S14's program-based signature and base check, S11's ladder
agreements. -/
def receiveCurve (sl : AgreeSlots) (pm : Receive.ProgramMasks) : Receive.Curve :=
  Receive.Curve.withPrograms (receiveAgree sl) receiveAgreeKinds (receiveAgree_reveals sl) pm

theorem receiveCurve_kinds (sl : AgreeSlots) (pm : Receive.ProgramMasks) :
    (receiveCurve sl pm).kinds = .maskedDenominator :: receiveAgreeKinds := rfl

/-- **T3 for the joined receive flows** (S14's `openFirst_reveals` / `session_reveals` with the
curve parameter instantiated: its `Reveals` fields are proved, not assumed): every release of op 50
and op 51 carries a kind of `firstKinds` / `sessionKinds` or of the joined curve, all registered. -/
theorem receive_joined_reveals (sl : AgreeSlots) (pm : Receive.ProgramMasks) (loaded : Bytes → Bool) :
    (∀ fi env size, RevealsG (Receive.firstKinds ++ .maskedDenominator :: receiveAgreeKinds)
      (Receive.openFirst (receiveCurve sl pm) loaded fi env size)) ∧
    (∀ a sp ss, RevealsG (Receive.sessionKinds ++ .maskedDenominator :: receiveAgreeKinds)
      (Receive.session (receiveCurve sl pm) loaded a sp ss)) ∧
    (∀ k ∈ Receive.firstKinds ++ Receive.sessionKinds ++ .maskedDenominator :: receiveAgreeKinds,
      k ∈ Label.kinds) :=
  ⟨fun fi env size => Receive.openFirst_reveals (receiveCurve sl pm) loaded fi env size,
   fun a sp ss => Receive.session_reveals (receiveCurve sl pm) loaded a sp ss, by decide⟩

/-! ## S15: the establishment's curve operations -/

/-- Run a state-threaded script from the counters the caller allocated, with the masks taken for
this call. -/
def runAt {α : Type} (c : Counters) (pool : Conv.MaskPool) (g : Gen α) : Script α :=
  (g { table := { ctr := c }, pool := pool }).bind fun p => .done p.1

theorem runAt_reveals {α : Type} {ks : List RevealKind} {g : Gen α} (h : RevealsG ks g) (c : Counters)
    (pool : Conv.MaskPool) : Reveals ks (runAt c pool g) :=
  Every.bind (h _) fun _ => Every.done _

/-- `xeddsa-recover` of the identity point (non-hinted path, as S14's base check): W2F, the
program (3 outputs), F2W of each; the field handles freed. -/
def liftG (pm : Receive.ProgramMasks) (point : BoolH) : Gen (BoolH × BoolH × BoolH) := do
  let u ← Receive.toField point
  let r ← Receive.programStep Receive.xeddsaRecoverName [u] 3 pm.recover pm.recoverSlot Label.maskedDenominator
  let v ← Receive.toWord (Receive.atF r 0)
  let x ← Receive.toWord (Receive.atF r 1)
  let y ← Receive.toWord (Receive.atF r 2)
  Receive.Gen.freeFields (u :: r)
  pure (v, x, y)

/-- `xeddsa-check` of both signatures (`ec`, `pq`: flip ‖ challenge ‖ scalar, 510 bits each) on the
lifted point; each check its own masks (`pm1`, `pm2`); F2W of the four coordinates. -/
def checkG (pm1 pm2 : Receive.ProgramMasks) (x y ec pq : BoolH) : Gen (BoolH × BoolH × BoolH × BoolH) := do
  let xf ← Receive.toField x
  let yf ← Receive.toField y
  let eb ← Receive.toFieldBits ec 510
  let pb ← Receive.toFieldBits pq 510
  let e ← Receive.programSignature pm1 xf yf eb
  let p ← Receive.programSignature pm2 xf yf pb
  let a ← Receive.toWord e.1
  let b ← Receive.toWord e.2
  let c ← Receive.toWord p.1
  let d ← Receive.toWord p.2
  Receive.Gen.freeFields ([xf, yf, e.1, e.2, p.1, p.2] ++ eb ++ pb)
  pure (a, b, c, d)

/-- The scalars of the establishment's agreements: the account's identity scalar, two fresh shared
scalars (base `fresh 0`, ratchet `fresh 1`; `service_kernels.h` lines 846-848). -/
def baseScalar : Scalar := .fresh 0
def ratchetScalar : Scalar := .fresh 1

/-- The seven jobs of `service_kernels.h` line 850 (`EstablishKernels.lean` step 6 order): dh1 =
identity·signed, dh2 = base·identity, dh3 = base·signed, ratchetAgreement = ratchet·signed,
basePublic = base·9, ratchetPublic = ratchet·9, and dh4 = base·oneTime. -/
def establishJobs (ip sp : FieldH) (op : Option FieldH) : List Job :=
  [⟨.identity, .handle sp⟩, ⟨baseScalar, .handle ip⟩, ⟨baseScalar, .handle sp⟩, ⟨ratchetScalar, .handle sp⟩,
    ⟨baseScalar, .base⟩, ⟨ratchetScalar, .base⟩] ++ (op.map fun o => (⟨baseScalar, .handle o⟩ : Job)).toList

def optField : Option BoolH → Gen (Option FieldH)
  | none => pure none
  | some o => do
    let f ← Receive.toField o
    pure (some f)

def agreeG (sl : AgreeSlots) (identityPoint signedPoint : BoolH) (oneTime : Option BoolH) : Gen (List BoolH) := do
  let ip ← Receive.toField identityPoint
  let sp ← Receive.toField signedPoint
  let op ← optField oneTime
  let ws ← receiveAgree sl (establishJobs ip sp op)
  Receive.Gen.freeFields ([ip, sp] ++ op.toList)
  pure ws

/-- What the joined operations release under. -/
def refreshCurveKinds : List RevealKind :=
  [.maskedWord, .maskedFieldValue, .maskedBit, .maskedDenominator, .curveChecks, .scalarBitChecks]

theorem liftG_reveals (pm : Receive.ProgramMasks) (point : BoolH) : RevealsG refreshCurveKinds (liftG pm point) := by
  unfold liftG
  refine RevealsG.bind (Receive.toField_reveals (by decide) _) fun u => ?_
  refine RevealsG.bind (Receive.programStep_reveals .maskedDenominator (by decide) _ _ _ _ _) fun r => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  exact RevealsG.bind (Receive.RevealsG.freeFields _) fun _ => RevealsG.pure _

theorem programSignature_reveals (pm : Receive.ProgramMasks) (x y : FieldH) (bits : List FieldH) :
    RevealsG refreshCurveKinds (Receive.programSignature pm x y bits) := by
  unfold Receive.programSignature
  exact RevealsG.bind (Receive.programStep_reveals .maskedDenominator (by decide) _ _ _ _ _) fun _ => RevealsG.pure _

theorem checkG_reveals (pm1 pm2 : Receive.ProgramMasks) (x y ec pq : BoolH) :
    RevealsG refreshCurveKinds (checkG pm1 pm2 x y ec pq) := by
  unfold checkG
  refine RevealsG.bind (Receive.toField_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toField_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toFieldBits_reveals (by decide) _ _) fun _ => ?_
  refine RevealsG.bind (Receive.toFieldBits_reveals (by decide) _ _) fun _ => ?_
  refine RevealsG.bind (programSignature_reveals _ _ _ _) fun _ => ?_
  refine RevealsG.bind (programSignature_reveals _ _ _ _) fun _ => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toWord_reveals (by decide) _) fun _ => ?_
  exact RevealsG.bind (Receive.RevealsG.freeFields _) fun _ => RevealsG.pure _

theorem optField_reveals (o : Option BoolH) : RevealsG refreshCurveKinds (optField o) := by
  cases o with
  | none => exact RevealsG.pure _
  | some o => exact RevealsG.bind (Receive.toField_reveals (by decide) _) fun _ => RevealsG.pure _

theorem agreeG_reveals (sl : AgreeSlots) (ip sp : BoolH) (o : Option BoolH) :
    RevealsG refreshCurveKinds (agreeG sl ip sp o) := by
  unfold agreeG
  refine RevealsG.bind (Receive.toField_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (Receive.toField_reveals (by decide) _) fun _ => ?_
  refine RevealsG.bind (optField_reveals _) fun _ => ?_
  refine RevealsG.bind (fun st => (receiveAgree_reveals sl _ st).mono (by decide)) fun _ => ?_
  exact RevealsG.bind (Receive.RevealsG.freeFields _) fun _ => RevealsG.pure _

/-- What one establishment step's curve calls are given for this call (prepared by the IO layer:
masks taken from the session pool, this party's fresh contributions in store slots). -/
structure RefreshCurve where
  pool : Conv.MaskPool
  recover : Receive.ProgramMasks
  check1 : Receive.ProgramMasks
  check2 : Receive.ProgramMasks
  agree : AgreeSlots

/-- Id blocks (Boolean, field) each call takes from the session counters: upper bounds of what
`liftG`, `checkG` and `agreeG` allocate (`toField` 2+2, `toWord` 3+1, `toFieldBits` 4+(2+k), a
program step 3·masks+outs, a job's swap bits 5·252, the ladder and quotients 7n+1, the public 9). -/
def liftIdsOf (rc : RefreshCurve) : Nat × Nat := (11, 3 * rc.recover.recover + 8)
def checkIdsOf (rc : RefreshCurve) : Nat × Nat := (24, 1036 + 3 * rc.check1.check + 3 * rc.check2.check)
def agreeIdsOf : Nat × Nat := (27, 6 + 7 * (5 * 252) + 2 + (7 * 7 + 1) + 7)

/-- **S15's `CurveOps`, joined.** -/
def refreshOps (rc : RefreshCurve) : Refresh.CurveOps where
  liftIds := liftIdsOf rc
  checkIds := checkIdsOf rc
  agreeIds := agreeIdsOf
  lift c point := runAt c rc.pool (liftG rc.recover point)
  check c x y ec pq := runAt c rc.pool (checkG rc.check1 rc.check2 x y ec pq)
  agree c ip sp o := runAt c rc.pool (agreeG rc.agree ip sp o)
  kinds := refreshCurveKinds

/-- **S15's hypothesis `CurveOps.Reveals`, DISCHARGED for the joined operations.** -/
theorem refreshOps_reveals (rc : RefreshCurve) : (refreshOps rc).Reveals where
  lift c h := runAt_reveals (liftG_reveals rc.recover h) c rc.pool
  check c x y e p := runAt_reveals (checkG_reveals rc.check1 rc.check2 x y e p) c rc.pool
  agree c a b o := runAt_reveals (agreeG_reveals rc.agree a b o) c rc.pool

/-- **T3 for the joined establishment, with no hypothesis on the curve operations**: every release
of every refresh step (`opEstablish`) carries a refresh kind or one of the joined curve kinds, and
all of them are registered labels. -/
theorem refresh_joined_reveals (rc : RefreshCurve) (acct : Refresh.Account) (t : Contacts.Table) (st : Refresh.RState)
    (id registration index count step start : Nat) (w : TlsMpc.Signal.BundleResponse.Widths) (slot : Nat) :
    Reveals (Refresh.refreshKinds refreshCurveKinds)
      (Refresh.opEstablish (refreshOps rc) acct t st id registration index count step start w slot).script ∧
    ∀ k ∈ Refresh.refreshKinds refreshCurveKinds, k ∈ Label.kinds :=
  ⟨Refresh.opEstablish_reveals (refreshOps rc) (refreshOps_reveals rc) acct t st id registration index count step
    start w slot, by decide⟩

/-! ## S15's send parameter: S13's `bundle-seal` reads the records the refresh kept -/

open TlsMpc.KernelSpecs.EstablishDevices (DeviceSession DeviceSeal wired) in
/-- **`first_wired`'s binding hypotheses, discharged for S13's bundle.** S13's `devicesScript` feeds
`bundle-seal` the bundle certificate ‖ stored record, pending block, our address, the built text,
then four words (`Send.bundleSeal_get`: the kernel reads exactly these); S15's commit stores record
‖ pending, and an accepted session's conversation is its certificate input followed by that record
(`Refresh.stored_record`). So when the certificate bytes are the session's certificate input
(`hcert`: the same account certificate handle) and the pending block is the session's (`hpend`),
`wired` holds: the opened envelope is the reference first message (`first_envelopes`). Remaining
assumptions: `hcert`, `hpend` and that the record S13 slices from the stored state is
`(out₁).drop cert` (here: built in) — facts about the bytes in handles across scripts, not proved
through `jointRun`. -/
theorem join_first_wired (cert content : Nat) (s : DeviceSession) (oneTime : Bool) (cw pw ew iw : Nat)
    (certBytes pending address text : B8) (w : Bits)
    (hW : Refresh.SessionWidths cert oneTime)
    (established : (s.outputs cert oneTime).getD 0 [] = [255])
    (hcert : certBytes = s.input cert oneTime "certificate")
    (hpend : pending = (s.outputs cert oneTime).getD 2 [])
    (hc : (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert).length = Send.convBytes cert)
    (hp : pending.length = TlsMpc.EstablishKernel.pendingBytes) (ha : address.length = 17)
    (ht : text.length = content + 10)
    (d : DeviceSeal)
    (hd : d = ⟨oneTime, cw, pw, ew, iw, Send.shapedAssign (TlsMpc.BundleKernel.sealInputs cert content)
      (bitsOf (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert) ++
        (bitsOf pending ++ (bitsOf address ++ (bitsOf text ++ w))))⟩)
    (opened : (d.outputs cert content).getD 0 [] = [255]) :
    wired cert content (s, d) := by
  subst hd
  have g := Send.bundleSeal_get cert content (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert) pending
    address text w hc hp ha ht oneTime cw pw ew iw
  have hrec := Refresh.stored_record cert oneTime s established
  have k := Refresh.kept_outputs cert oneTime hW s.assign
  refine Refresh.first_wired cert content s _ hW established ?_ ?_ opened
  · have h1 : DeviceSeal.input cert content ⟨oneTime, cw, pw, ew, iw, Send.shapedAssign
        (TlsMpc.BundleKernel.sealInputs cert content) (bitsOf (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert) ++
          (bitsOf pending ++ (bitsOf address ++ (bitsOf text ++ w))))⟩ "conversation" =
        certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert := g.2.1
    rw [h1, hcert, ← hrec]
    exact k.1.symm
  · have h2 : DeviceSeal.input cert content ⟨oneTime, cw, pw, ew, iw, Send.shapedAssign
        (TlsMpc.BundleKernel.sealInputs cert content) (bitsOf (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert) ++
          (bitsOf pending ++ (bitsOf address ++ (bitsOf text ++ w))))⟩ "pending" = pending := g.2.2.1
    rw [h2, hpend]
    exact k.2.symm

/-! ## Every joined kind is a registered label -/

theorem join_kinds_registered :
    ∀ k ∈ keyAgreementKinds ++ Curve.splitKinds ++ ephemeralKinds ++ Random.jointKinds ++ receiveAgreeKinds ++
      refreshCurveKinds, k ∈ Label.kinds := by decide

end TlsMpc.Node.Flows.Join
