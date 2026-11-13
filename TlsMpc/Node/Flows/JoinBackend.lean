import TlsMpc.Node.Flows.Join
import TlsMpc.Node.Flows.SendBackend

/-!
# The joins, IO side: S12's `KeyAgreement` and S13's `SendBackend.Curve` from S11's flows

Written when the stages were joined on `scripts-stack` (STACK_NOTES.md). UNVERIFIED IO GLUE, like
`TlsBackend.lean` / `SendBackend.lean` / `ReceiveBackend.lean` whose parameters it fills; nothing
selects it yet (the controller-side runner, op 93, does not exist). Every script it runs is one of
the branches' or `Join.lean`'s, with its `Reveals` theorem:

  * `keyAgreement`: `begin` runs S11 `Curve.splitBegin` (`Curve.splitBegin_reveals`:
    `Curve.splitKinds`); `agree` runs `Join.splitAgreeWord` (`Join.keyAgreementKinds`).
  * `sendCurve`: `ephemeral` runs S9 `Random.joint` for the joint public offset τ
    (`Random.jointKinds`) and `Join.ephemeralWord` (`Join.ephemeralKinds`), and returns the key
    through `Reveal.ephemeralPublic` (added to `Reveal.lean` by the join, a pure addition);
    `staticAgreement`, `senderPublic` are the contact's / account's cached words (op 66's
    `Curve.prepareContacts` result and the account state), passed in.

THE ADAPTER: S12's and S13's `Runner` (`TlsBackend.Runner`) allocates Boolean ids only and has no
field-element slots and no mask pool; S11's flows need field ids, a store slot of this party's field
elements, and S10 word masks. `FieldRunner` is that missing part. The script runner supplies it
(`Flows/Runner.lean`, `Runner.field`: `allocF` from the same counters as `allocB`, `takeWord` from
the session's one pool, each mask once: P-CUT (h)). Both functions here stash a NEW mask slot per
call (`fr.stashElems (← elems r k)`), so no quotient or offset sum shares its masks (checked for J1).
-/

namespace TlsMpc.Node.Flows.JoinBackend

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist)
open TlsMpc.Node.Flows.TlsBackend (Runner)
open TlsMpc.FieldDag (F)

/-- What S11's flows need of the runner beyond `TlsBackend.Runner` (see the module doc). -/
structure FieldRunner where
  /-- A fresh block of `k` field handle ids (the session's `Counters.allocF`). -/
  allocF : Nat → M Nat
  /-- A fresh store slot holding this party's private field elements. -/
  stashElems : Secret (List F) → M Nat
  /-- A word mask from the session's pool (S10 `Masks.generate`), each handed out once. -/
  takeWord : M Conv.WordMask

/-- `k` fresh field elements of this party (64 random bytes each, reduced mod p), as
`ReceiveBackend.elems`. -/
def elems (r : Runner) (k : Nat) : M (Secret (List F)) := do
  let bytes ← r.random (64 * k)
  return bytes.map fun b => (Engine.byteBlocks 64 k b).map fun c => TlsMpc.FieldDag.ofNat (Engine.fromLEFast c)

/-! ## S12: the TLS key agreement -/

/-- The per-connection state between `begin` and `agree`: this party's scalar summand. -/
structure SplitState where
  scalar : Secret Nat

/-- The summand as `split_ecdh.h` `begin` draws it: 32 random bytes, `scalar[0] &= 248`,
`scalar[31] &= 31` (a multiple of 8 below 2^253). -/
def summandOf (b : Bytes) : Nat :=
  Engine.fromLE (((b.getD 0 0) &&& 248) :: ((b.drop 1).take 30 ++ [(b.getD 31 0) &&& 31]))

/-- The server's key share as a field element: top bit cleared, reduced mod p (`tls_kernels.h`
`derive`, lines 116-117). -/
def peerU (peer : Bytes) : F := TlsMpc.FieldDag.ofNat (Engine.fromLE (peer.take 31 ++ [(peer.getD 31 0) &&& 127]))

/-- **S12's `TlsBackend.KeyAgreement`, from S11's split ECDH.** `begin`: the summand, its share k·B
(LOCAL, `Curve.splitShare`), commit-then-open (`Curve.splitBegin`), the client's key share.
`agree`: the peer share rejected PUBLICLY when it does not lift to a valid point
(`split_ecdh.h`: off the curve, small order, outside the subgroup); T = k·S LOCALLY
(`Curve.splitAgreeInputs`), one mask contribution, `Join.splitAgreeWord`. `erase`: the scalar
lives only in the state (nothing in the engines). -/
def keyAgreement (r : Runner) (fr : FieldRunner) : TlsBackend.KeyAgreement SplitState where
  begin := do
    let raw ← r.random 32
    let k := raw.map summandOf
    let nonce ← r.random 32
    let ns ← r.stashBytes nonce
    let ss ← r.stashBytes (k.map fun k => (Curve.splitShare k).getD [])
    let share ← r.run (Curve.splitBegin r.hash r.me ns ss)
    insist (share.length == 32) "joint key share"
    return (⟨k⟩, share)
  agree st peer := do
    insist (peer.length == 32) "peer key share"
    let u := peerU peer
    match Local.Edwards.liftU u with
    | none => throw "peer key share rejected"
    | some p =>
      insist (Local.Edwards.isValid p) "peer key share rejected"
      let tSlot ← fr.stashElems (st.scalar.map fun k => (Curve.splitAgreeInputs k u).getD [])
      let maskSlot ← fr.stashElems (← elems r 1)
      let m ← fr.takeWord
      let n0 ← r.allocB 3
      let f ← fr.allocF 14
      r.run (Join.splitAgreeWord f tSlot maskSlot n0 (f + 13) m)
  erase _ := pure ()

/-! ## S13: the send's curve half -/

/-- Where the send's cached curve values come from (op 66 `Curve.prepareContacts` / `offsetPrepare`
per contact; the account state for the sender key). -/
structure SendSources where
  /-- The contact's prepared offset agreement (`none`: not prepared). -/
  offsets : ContactId → M (Option Curve.OffsetState)
  /-- The contact's static agreement word (`none`: its key is not a curve point). -/
  statics : ContactId → M (Option BoolH)
  senderPublic : M BoolH

/-- **S13's `SendBackend.Curve`, from S11's offset agreement.** `ephemeral`: the joint public
offset τ (`Random.joint`, then `Curve.offsetOf`: 252 bits), 128 fresh mask contributions for the
offset sum's `D` rows, `Join.ephemeralWord`; the public key `toBytes u` through
`Reveal.ephemeralPublic`. -/
def sendCurve (r : Runner) (fr : FieldRunner) (src : SendSources) : SendBackend.Curve where
  ephemeral id := do
    let some st ← src.offsets id | throw "contact not prepared"
    let nonce ← r.random 32
    let value ← r.random 32
    let ns ← r.stashBytes nonce
    let vs ← r.stashBytes value
    let joint ← r.run (Random.joint r.hash r.me ns vs)
    let τ := Curve.offsetOf joint
    let maskSlot ← fr.stashElems (← elems r 128)
    let m ← fr.takeWord
    let n0 ← r.allocB 3
    let f ← fr.allocF 389
    let (u, w) ← r.run (Join.ephemeralWord f maskSlot n0 (f + 388) st τ m)
    return (Reveal.ephemeralPublic (Local.Field.toBytes u), w)
  staticAgreement := src.statics
  senderPublic := src.senderPublic

end TlsMpc.Node.Flows.JoinBackend
