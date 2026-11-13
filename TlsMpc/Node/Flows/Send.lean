import TlsMpc.Node.Flows.Tls
import TlsMpc.KernelSpecs.SealFrame
import TlsMpc.KernelSpecs.EstablishRequest

/-!
# `Send.*`: a sealed-sender send as scripts (ops 41, 42, 61, 62)

REORGANIZATION_PLAN.md stage S13. Replaces `handshake_backend/EmpHybridWork/service_kernels.h`
`seal_open` (lines 526-572), `request` (575-586), `seal_devices` (931-968), `request_devices`
(971-981), the widths opening and the status gate, and the request sealer of `tls_kernels.h`
`seal_application` (`PrivateBuffer::sealer`, lines 200-207) for these requests. Advance work in a new
file; the C++ stays in use until the controller switches (`Flows/SendBackend.lean` is selectable,
not selected). The ephemeral pairs, the contact's static agreement and the account's sender key are
S11's (`Flows/Curve.lean`): parameters of the backend (`SendBackend.Curve`, S13_NOTES.md), here
plain handle and byte arguments.

THE SCRIPTS (Boolean handles; `n` the session's next free handle id; bits of bytes least
significant first; every kernel by its cache name; every opening labelled by its reveal kind):

  `sealScript n a` (op 41, `seal_open` for a built text): the contact's state is one record
    (kinds `[0]`, 319 bytes). concat conversation := certificate ‖ record; run `signal-widths CERT`
    on it and OPEN its 21 flag bytes (counterWidths: the varint widths of counter, previous, SPQR
    epoch and SPQR index); abort unless every flag is 0 or 255; the kernel by name
    `signal-seal-official|built CERT CLASS W1 W2 W3 W4` (the class and the official padding from the
    public text's length); public text ‖ ephemeral public key (255 bits); concat conversation ‖ that
    ‖ sender key ‖ ephemeral agreement ‖ static agreement; run; slice status, new record (the
    conversation output without the certificate) and timestamp ‖ envelope; free the inputs (the
    ephemeral agreement is consumed); OPEN the status (sealedEnvelope). THE STATUS GATE: not 255:
    free the new record and the timestamp ‖ envelope and return `none` (the stored state is kept;
    nothing else is released, `seal_refused_silent`). 255: OPEN timestamp ‖ envelope
    (sealedEnvelope), free the old state, return the timestamp, the envelope and the new state.
  `devicesScript n a` (op 61, `seal_devices`): one device after the other inside one script, the
    same per device (records and pending blocks are slices of the state at `Contacts.deviceSpans`;
    kind 0: `signal-seal-official|built`, kinds 1, 2: `bundle-seal CERT ONETIME CONTENT W1..W4` with
    the pending block and our own address), but ONE opening for all devices' width flags, ONE for all
    statuses (the gate: every device 255, or `none` and nothing kept), and ONE for all timestamps ‖
    envelopes; the new state is the new records with the old pending blocks, in order.
  `requestScript n cert state` (op 42, `request`): the request's conversation := certificate ‖ the
    first device's record (a copy, owned by the request). Nothing released.
  `requestDevicesScript n state kinds` (op 62, `request_devices`): the devices' records,
    concatenated (a copy). Nothing released.
  `requestCtrScript n traffic conv seq frame mask name` (the record seal's first phase for a request,
    `seal_application` with a sealer): public sequence and frame ‖ mask (the frame is built in the
    clear, `PublicRequest.build` / `buildDevices`, zero at its slots); concat traffic ‖ sequence ‖
    conversation ‖ frame ‖ mask; run `signal-request-ctr CERT SIZE U K D R` or `bundle-request-ctr
    SIZE PAYLOAD U K (D R)*`; keep the pad; OPEN accepted ‖ header ‖ ciphertext (sealedRecord, one
    opening); abort unless accepted is 255 ("private request rejected"); free the request's
    conversation (a request is sealed once). The tag is S12's `Tls.tagScript` (`TlsBackend.sealPhases`).

DEVIATIONS FROM THE C++ (both parties change together; the legacy library keeps its own):
  * One opening per group: the four width fields in one opening (the C++ opens them one by one);
    timestamp ‖ envelope in one; for op 61 one opening of all devices' flags, one of all statuses,
    one of all timestamps ‖ envelopes (the C++: 7 openings per device).
  * Op 61 opens the envelopes only after EVERY device's status is 255 (the C++ opened device k's
    envelope before device k + 1's status; a later refusal left an opened envelope never sent).
  * A refused send frees the new record and keeps the old state handle (the C++ kept the old wires).
  * The request's sealer runs as its own phase with one opening (accepted ‖ header ‖ ciphertext).
  * The C++'s refusal on a kernel name Lean refuses (`shaped` throwing `Rejected`) cannot happen:
    the widths read from 0/255 flags are always in `find`'s ranges (`widths_in_range`).

The kernels' output layout: status 1 byte (public), conversation `cert + 319` (private), timestamp
8, envelope `E` (public), `E` a function of the public parameters only: `sealEnvBytes` /
`bundleEnvBytes` compute it by evaluating the kernels' value functions (`SealSend.sealValue`,
`EstablishSeal.sealMessageValue`) on the all-zero assignment, which `SendProofs` shows is the
kernel's own output length.
-/

namespace TlsMpc.Node.Flows.Send

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide

/-! ## Names -/

/-- A kernel's cache name: its words separated by single spaces. -/
def joinName (parts : List String) : Bytes := ascii (" ".intercalate parts)

def widthsName (cert : Nat) : Bytes := joinName ["signal-widths", toString cert]

/-- `signal-seal-official` (official padding, `80k − 1` content bytes) or `signal-seal-built`. -/
def sealName (official : Bool) (cert classes cw pw ew iw : Nat) : Bytes :=
  joinName [if official then "signal-seal-official" else "signal-seal-built", toString cert, toString classes,
    toString cw, toString pw, toString ew, toString iw]

def bundleSealName (cert oneTime content cw pw ew iw : Nat) : Bytes :=
  joinName ["bundle-seal", toString cert, toString oneTime, toString content, toString cw, toString pw,
    toString ew, toString iw]

def requestName (cert size uuidAt keyAt deviceAt registrationAt : Nat) : Bytes :=
  joinName ["signal-request-ctr", toString cert, toString size, toString uuidAt, toString keyAt,
    toString deviceAt, toString registrationAt]

def bundleRequestName (size payloadAt uuidAt keyAt : Nat) (devices : List (Nat × Nat)) : Bytes :=
  joinName (["bundle-request-ctr", toString size, toString payloadAt, toString uuidAt, toString keyAt] ++
    devices.flatMap fun d => [toString d.1, toString d.2])

/-! ## Public parameters -/

/-- A record's byte length (`service_kernels.h` CONTACT). -/
def recordBytes : Nat := 319

/-- The conversation input: certificate ‖ record (`HybridKernel.conversationBytes cert 80`). -/
def convBytes (cert : Nat) : Nat := cert + recordBytes

/-- The size class of a built text (`seal_open`'s name choice): `(official, classes)`; `none` when the
text has no class (the C++'s "send unavailable"). Built: `10 + 80c` bytes; official: `9 + 80c`. -/
def textClass (t : Nat) : Option (Bool × Nat) :=
  if 90 ≤ t ∧ t ≤ 330 ∧ (t - 10) % 80 = 0 then some (false, (t - 10) / 80)
  else if 89 ≤ t ∧ t ≤ 329 ∧ (t - 9) % 80 = 0 then some (true, (t - 9) / 80)
  else none

/-- A varint width from its flags (`value ≥ 2^(7k)` as 0/255 bytes): one plus the set flags. -/
def widthOf (flags : B8) : Option Nat :=
  if flags.all (fun f => f == 0 || f == 255) then some (1 + (flags.filter (· == 255)).length) else none

/-- The four widths from `signal-widths`' 21 flag bytes (counter 4, previous 4, epoch 9, index 4). -/
def widthsOf (flags : B8) : Option (Nat × Nat × Nat × Nat) :=
  if flags.length = 21 then
    match widthOf (flags.take 4), widthOf ((flags.drop 4).take 4), widthOf ((flags.drop 8).take 9),
      widthOf ((flags.drop 17).take 4) with
    | some c, some p, some e, some i => some (c, p, e, i)
    | _, _, _, _ => none
  else none

/-- The all-zero input assignment (every variable 0). -/
def zeroA : BVExpr.Assignment := .leaf ⟨(0 : BitVec 8)⟩

/-- The envelope length of `signal-seal-official|built` with these public parameters: its value
function `SealSend.sealValue` on the all-zero assignment's inputs (equal to the kernel's own output
length, `SendProofs.sealEnvBytes_eq`). -/
def sealEnvBytes (cert classes : Nat) (official : Bool) (cw pw ew iw : Nat) : Nat :=
  let get := fun name => (HybridKernel.lookup (KernelSpecs.SealFixed.sealInputs cert classes official) name).map
    (BVExpr.eval zeroA)
  ((KernelSpecs.SealSend.sealValue cert cw pw ew iw (KernelSpecs.SealFixed.contentBytes classes official)
    (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
    (get "staticAgreement")).getD 3 []).length

/-- The padded content of a `bundle-seal` (`80c − 1` official, `80c` otherwise). -/
def bundleContent (classes : Nat) (official : Bool) : Nat := if official then 80 * classes - 1 else 80 * classes

/-- The envelope length of `bundle-seal` (`EstablishSeal.sealMessageValue` on the all-zero inputs). -/
def bundleEnvBytes (cert : Nat) (oneTime : Bool) (content cw pw ew iw : Nat) : Nat :=
  let get := fun name => (HybridKernel.lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval zeroA)
  let record := get "conversation"
  ((KernelSpecs.EstablishSeal.sealMessageValue oneTime ⟨cw, pw, true⟩ ⟨ew, iw, 0, false⟩ content
    ((record.drop cert).take 262) ((record.drop (cert + 262)).take 57) (get "pending") ((record.drop 0).take cert)
    (get "localAddress") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
    (get "staticAgreement")).getD 2 []).length

/-- A 32-byte public key as the 255-bit word a `.word` input takes (`s.public_bits`: bit `i` of byte
`i / 8`, the top bit dropped). -/
def wordBits (pk : B8) : Bits := (bitsOf pk).take 255

/-- Bit offsets of a seal kernel's outputs: status 8, conversation, timestamp ‖ envelope. -/
def statusEnd : Nat := 8
def recordFrom (cert : Nat) : Nat := 8 + 8 * cert
def recordEnd (cert : Nat) : Nat := 8 + 8 * convBytes cert
def envelopeEnd (cert env : Nat) : Nat := recordEnd cert + 64 + 8 * env

/-! ## Labels (Engine/Labels.lean, plan 4.3 "Send") -/

def widthsLabel : Label := Label.counterWidths
def envelopeLabel : Label := Label.sealedEnvelope

/-! ## Op 41: one envelope to a contact with one record -/

/-- What a seal needs, all public or handles. `cert`: the account's certificate (handle and byte
length); `sender`: the account's sender key word (255 bits); `static`: the contact's static
agreement word (255 bits, S11's `prepare`); `state`: the contact's state handle; `text`: the built
text; `eph`: this message's ephemeral public key (32 bytes, opened by S11) and the agreement word
(255 private bits, consumed). -/
structure SealArgs where
  cert : BoolH
  certLen : Nat
  sender : BoolH
  static : BoolH
  state : BoolH
  text : B8
  ephPublic : B8
  ephAgreement : BoolH

/-- What an accepted seal returns: the timestamp (8 bytes), the envelope, the new state handle. -/
structure Sealed where
  timestamp : B8
  envelopes : List B8
  state : BoolH

/-- The first block (handles `n`, `n + 1`): the conversation and the widths kernel. -/
def widthsBlock (n : Nat) (cert record : BoolH) (certLen : Nat) : List Instr :=
  [.concat ⟨n⟩ [cert, record], .run ⟨n + 1⟩ (widthsName certLen) 1 ⟨n⟩]

/-- The seal kernel's block (handles `n + 2 … n + 7`). -/
def sealBlock (n : Nat) (a : SealArgs) (name : Bytes) (env : Nat) : List Instr :=
  [.boolPublic ⟨n + 2⟩ (bitsOf a.text ++ wordBits a.ephPublic),
   .concat ⟨n + 3⟩ [⟨n⟩, ⟨n + 2⟩, a.sender, a.ephAgreement, a.static],
   .run ⟨n + 4⟩ name 1 ⟨n + 3⟩,
   .slice ⟨n + 5⟩ ⟨n + 4⟩ 0 statusEnd,
   .slice ⟨n + 6⟩ ⟨n + 4⟩ (recordFrom a.certLen) (recordEnd a.certLen),
   .slice ⟨n + 7⟩ ⟨n + 4⟩ (recordEnd a.certLen) (envelopeEnd a.certLen env),
   .freeBool ⟨n + 2⟩, .freeBool ⟨n + 3⟩, .freeBool ⟨n + 4⟩, .freeBool a.ephAgreement, .freeBool ⟨n⟩]

/-- After the status: the gate. -/
def afterStatus (n : Nat) (a : SealArgs) (st : Bits) : Script (Option Sealed) :=
  if st = bitsOf [255] then
    seqs [.freeBool ⟨n + 5⟩]
      (openThen ⟨n + 7⟩ envelopeLabel fun te =>
        seqs [.freeBool ⟨n + 7⟩, .freeBool a.state]
          (.done (some ⟨(bytesOf te).take 8, [(bytesOf te).drop 8], ⟨n + 6⟩⟩)))
  else seqs [.freeBool ⟨n + 5⟩, .freeBool ⟨n + 6⟩, .freeBool ⟨n + 7⟩] (.done none)

/-- After the widths: the kernel by name, its run, the status opening. -/
def afterWidths (n : Nat) (a : SealArgs) (official : Bool) (classes : Nat) (flags : Bits) : Script (Option Sealed) :=
  match widthsOf (bytesOf flags) with
  | some (cw, pw, ew, iw) =>
    seqs (sealBlock n a (sealName official a.certLen classes cw pw ew iw)
        (sealEnvBytes a.certLen classes official cw pw ew iw))
      (openThen ⟨n + 5⟩ envelopeLabel (afterStatus n a))
  | none => .abort "width flag"

/-- **Op 41** (`seal_open` with a built text): `none` when the contact's state cannot produce a
message (the gated status is not 255; the state is kept), else the timestamp, the one envelope and
the advanced state. Uses ids `n … n+7`. -/
def sealScript (n : Nat) (a : SealArgs) : Script (Option Sealed) :=
  match textClass a.text.length with
  | some (official, classes) =>
    if a.certLen ≤ 1024 then
      seqs (widthsBlock n a.cert a.state a.certLen)
        (openThen ⟨n + 1⟩ widthsLabel fun flags =>
          seqs [.freeBool ⟨n + 1⟩] (afterWidths n a official classes flags))
    else .abort "send unavailable"
  | none => .abort "send unavailable"

/-! ## Op 61: one envelope per device -/

/-- One device of a device list (public: from the stored kinds): its kind, the byte offset of its
record in the state, the ephemeral public key and agreement word of its message. -/
structure DeviceArgs where
  kind : Nat
  at_ : Nat
  ephPublic : B8
  ephAgreement : BoolH

/-- The arguments of op 61: as `SealArgs` (its `ephPublic` / `ephAgreement` unused) with the devices
and our own account's address (17 bytes, public). -/
structure DevicesArgs where
  cert : BoolH
  certLen : Nat
  sender : BoolH
  static : BoolH
  state : BoolH
  text : B8
  address : B8
  devices : List DeviceArgs

/-- Per device the handles `b … b+3` of the first phase, `b = n + 4i`. -/
def devBase (n i : Nat) : Nat := n + 4 * i

/-- The first phase of device `i`: its record (and pending block) out of the state, its
conversation, its widths kernel. -/
def deviceWidthsBlock (n : Nat) (a : DevicesArgs) (i : Nat) (d : DeviceArgs) : List Instr :=
  let b := devBase n i
  [.slice ⟨b⟩ a.state (8 * d.at_) (8 * (d.at_ + recordBytes)),
   .concat ⟨b + 1⟩ [a.cert, ⟨b⟩],
   .run ⟨b + 2⟩ (widthsName a.certLen) 1 ⟨b + 1⟩] ++
  (if d.kind = 0 then [] else
    [.slice ⟨b + 3⟩ a.state (8 * (d.at_ + recordBytes)) (8 * (d.at_ + recordBytes + EstablishKernel.pendingBytes))])

/-- The handle that collects every device's width flags. -/
def flagsId (n m : Nat) : Nat := n + 4 * m

/-- Per device the handles `c … c+5` of the second phase. -/
def sealBase (n m i : Nat) : Nat := n + 4 * m + 1 + 6 * i

/-- Device `i`'s kernel name and envelope length, from its widths. -/
def deviceKernel (a : DevicesArgs) (official : Bool) (classes : Nat) (d : DeviceArgs) (w : Nat × Nat × Nat × Nat) :
    Bytes × Nat :=
  let (cw, pw, ew, iw) := w
  if d.kind = 0 then (sealName official a.certLen classes cw pw ew iw, sealEnvBytes a.certLen classes official cw pw ew iw)
  else
    let oneTime := if d.kind = 2 then 1 else 0
    let content := bundleContent classes official
    (bundleSealName a.certLen oneTime content cw pw ew iw, bundleEnvBytes a.certLen (d.kind == 2) content cw pw ew iw)

/-- The second phase of device `i`: public inputs, the kernel's input bundle (declaration order),
the run, the three slices, and the frees. -/
def deviceSealBlock (n m : Nat) (a : DevicesArgs) (i : Nat) (d : DeviceArgs) (name : Bytes) (env : Nat) : List Instr :=
  let b := devBase n i
  let c := sealBase n m i
  (if d.kind = 0 then
    [.boolPublic ⟨c⟩ (bitsOf a.text ++ wordBits d.ephPublic),
     .concat ⟨c + 1⟩ [⟨b + 1⟩, ⟨c⟩, a.sender, d.ephAgreement, a.static]]
  else
    [.boolPublic ⟨c⟩ (bitsOf a.address ++ bitsOf a.text ++ wordBits d.ephPublic),
     .concat ⟨c + 1⟩ [⟨b + 1⟩, ⟨b + 3⟩, ⟨c⟩, a.sender, d.ephAgreement, a.static]]) ++
  [.run ⟨c + 2⟩ name 1 ⟨c + 1⟩,
   .slice ⟨c + 3⟩ ⟨c + 2⟩ 0 statusEnd,
   .slice ⟨c + 4⟩ ⟨c + 2⟩ (recordFrom a.certLen) (recordEnd a.certLen),
   .slice ⟨c + 5⟩ ⟨c + 2⟩ (recordEnd a.certLen) (envelopeEnd a.certLen env),
   .freeBool ⟨c⟩, .freeBool ⟨c + 1⟩, .freeBool ⟨c + 2⟩, .freeBool d.ephAgreement, .freeBool ⟨b + 1⟩,
   .freeBool ⟨b⟩]

/-- The handle that collects the statuses, then timestamps ‖ envelopes, then the new state. -/
def statusId (n m : Nat) : Nat := n + 10 * m + 1

/-- Indexed devices. -/
def indexed (ds : List DeviceArgs) : List (Nat × DeviceArgs) := (List.range ds.length).zip ds

/-- The pending blocks' handles (kinds 1, 2). -/
def pendings (n : Nat) (ds : List DeviceArgs) : List BoolH :=
  (indexed ds).filterMap fun (i, d) => if d.kind = 0 then none else some ⟨devBase n i + 3⟩

/-- The new state: per device its new record, then its (old) pending block. -/
def newParts (n m : Nat) (ds : List DeviceArgs) : List BoolH :=
  (indexed ds).flatMap fun (i, d) =>
    [⟨sealBase n m i + 4⟩] ++ (if d.kind = 0 then [] else [⟨devBase n i + 3⟩])

/-- Split the opened timestamps ‖ envelopes (per device 8 + `E_i` bytes). -/
def splitEnvelopes : List Nat → B8 → List (B8 × B8)
  | [], _ => []
  | e :: es, b => ((b.take 8), (b.drop 8).take e) :: splitEnvelopes es (b.drop (8 + e))

/-- After the statuses: the gate for all devices. -/
def afterStatuses (n m : Nat) (a : DevicesArgs) (envs : List Nat) (st : Bits) : Script (Option Sealed) :=
  let s := statusId n m
  let idx := indexed a.devices
  if st = bitsOf (List.replicate m 255) then
    seqs [.freeBool ⟨s⟩, .concat ⟨s + 1⟩ (idx.map fun (i, _) => ⟨sealBase n m i + 5⟩)]
      (openThen ⟨s + 1⟩ envelopeLabel fun te =>
        let parts := splitEnvelopes envs (bytesOf te)
        seqs ([.concat ⟨s + 2⟩ (newParts n m a.devices), .freeBool ⟨s + 1⟩, .freeBool a.state] ++
            frees (idx.map fun (i, _) => ⟨sealBase n m i + 5⟩) ++
            frees (idx.map fun (i, _) => ⟨sealBase n m i + 4⟩) ++ frees (pendings n a.devices))
          (.done (some ⟨(parts.headD ([], [])).1, parts.map (·.2), ⟨s + 2⟩⟩)))
  else
    seqs ([.freeBool ⟨s⟩] ++ frees (idx.map fun (i, _) => ⟨sealBase n m i + 4⟩) ++
        frees (idx.map fun (i, _) => ⟨sealBase n m i + 5⟩) ++ frees (pendings n a.devices))
      (.done none)

/-- The widths of every device from the opened flags (21 bytes each). -/
def allWidths (m : Nat) (flags : B8) : Option (List (Nat × Nat × Nat × Nat)) :=
  if flags.length = 21 * m then (List.range m).mapM fun i => widthsOf ((flags.drop (21 * i)).take 21) else none

/-- After all flags: every device's kernel, one status opening. -/
def afterFlags (n : Nat) (a : DevicesArgs) (official : Bool) (classes : Nat) (flags : Bits) : Script (Option Sealed) :=
  let m := a.devices.length
  match allWidths m (bytesOf flags) with
  | some ws =>
    let ks := (a.devices.zip ws).map fun (d, w) => deviceKernel a official classes d w
    let blocks := ((indexed a.devices).zip ks).flatMap fun ((i, d), k) => deviceSealBlock n m a i d k.1 k.2
    seqs (blocks ++ [.concat ⟨statusId n m⟩ ((indexed a.devices).map fun (i, _) => ⟨sealBase n m i + 3⟩)] ++
        frees ((indexed a.devices).map fun (i, _) => ⟨sealBase n m i + 3⟩))
      (openThen ⟨statusId n m⟩ envelopeLabel (afterStatuses n m a (ks.map (·.2))))
  | none => .abort "width flag"

/-- **Op 61** (`seal_devices`): every device's message from the same built text, gated as one:
`none` unless every device's status is 255 (the state is kept), else the timestamp, the envelopes in
device order and the new state. Uses ids `n … n + 10m + 3`. -/
def devicesScript (n : Nat) (a : DevicesArgs) : Script (Option Sealed) :=
  let m := a.devices.length
  match textClass a.text.length with
  | some (official, classes) =>
    if a.certLen ≤ 1024 ∧ a.address.length = 17 ∧ 0 < m ∧ m ≤ 16 then
      seqs (((indexed a.devices).flatMap fun (i, d) => deviceWidthsBlock n a i d) ++
          [.concat ⟨flagsId n m⟩ ((indexed a.devices).map fun (i, _) => ⟨devBase n i + 2⟩)] ++
          frees ((indexed a.devices).map fun (i, _) => ⟨devBase n i + 2⟩))
        (openThen ⟨flagsId n m⟩ widthsLabel fun flags =>
          seqs [.freeBool ⟨flagsId n m⟩] (afterFlags n a official classes flags))
    else .abort "send unavailable"
  | none => .abort "send unavailable"

/-! ## Ops 42 and 62: the request's private part -/

/-- **Op 42** (`request`): the request's conversation, certificate ‖ the first record (a copy).
Uses ids `n, n+1`. -/
def requestScript (n : Nat) (cert state : BoolH) : Script BoolH :=
  seqs [.slice ⟨n⟩ state 0 (8 * recordBytes), .concat ⟨n + 1⟩ [cert, ⟨n⟩], .freeBool ⟨n⟩] (.done ⟨n + 1⟩)

/-- **Op 62** (`request_devices`): the devices' records, concatenated (a copy). Uses ids `n … n+m`. -/
def requestDevicesScript (n : Nat) (state : BoolH) (ats : List Nat) : Script BoolH :=
  let m := ats.length
  let hs : List BoolH := (List.range m).map fun i => ⟨n + i⟩
  seqs (((List.range m).zip ats).map (fun (i, at_) => .slice ⟨n + i⟩ state (8 * at_) (8 * (at_ + recordBytes))) ++
      [.concat ⟨n + m⟩ hs] ++ frees hs)
    (.done ⟨n + m⟩)

/-- The inner plaintext's length of a request frame (`TlsRecord.inner _ frame 23 0`). -/
def innerOf (size : Nat) : Nat := size + 1

/-- **The request's record, first phase** (`seal_application` with a sealer): the CTR kernel on
traffic ‖ sequence ‖ conversation ‖ frame ‖ mask; OPENS accepted ‖ header ‖ ciphertext (sealedRecord);
aborts unless accepted is 255; returns header ‖ ciphertext and the pad `n + 4`. Frees the request's
conversation. Uses ids `n … n+5`. -/
def requestCtrScript (n : Nat) (traffic conv : BoolH) (seq frame mask : B8) (name : Bytes) : Script (B8 × BoolH) :=
  let hc := 8 * (1 + 5 + innerOf frame.length)
  seqs [.boolPublic ⟨n⟩ (bitsOf seq),
        .boolPublic ⟨n + 1⟩ (bitsOf frame ++ bitsOf mask),
        .concat ⟨n + 2⟩ [traffic, ⟨n⟩, conv, ⟨n + 1⟩],
        .run ⟨n + 3⟩ name 1 ⟨n + 2⟩,
        .slice ⟨n + 4⟩ ⟨n + 3⟩ hc (hc + 128),
        .slice ⟨n + 5⟩ ⟨n + 3⟩ 0 hc,
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩, .freeBool ⟨n + 3⟩, .freeBool conv]
    (openThen ⟨n + 5⟩ Label.sealedRecord fun out =>
      seqs [.freeBool ⟨n + 5⟩]
        (if (bytesOf out).take 1 = [255] then .done ((bytesOf out).drop 1, ⟨n + 4⟩)
         else .abort "private request rejected"))

/-! ## The request frame on the script path -/

/-- A big-endian number (the opened timestamp, as the legacy reply's `number`). -/
def beNat (b : B8) : Nat := b.foldl (fun acc x => 256 * acc + x.toNat) 0

/-- **The request frame of a send, built in the clear from the script's own openings** (the opened
envelope and timestamp; `PublicRequest.build`, the controller's builder): the frame and slot offsets
`requestCtrScript` then names its kernel by and feeds. No worker passes them on (E2's `built`). -/
def frameFor (envelope timestamp : B8) (id : Nat) (mask : B8) (official : Bool) :
    Except String (B8 × List Nat) :=
  PublicRequest.build envelope (beNat timestamp) id mask official

/-- The kernel `requestCtrScript` runs for a single-device request built by `frameFor`. -/
def requestNameOf (cert : Nat) (frame : B8) (offsets : List Nat) : Bytes :=
  requestName cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0) (offsets.getD 3 0)

/-- The devices' slot pairs as `bundle-request-ctr`'s name lists them (`BundleKernel.pairs`): the
script path pairs the offsets `PublicRequest.buildDevices` returned itself (E2's `paired`). -/
def devicesNameOf (frame : B8) (payloadAt : Nat) (offsets : List Nat) : Option Bytes :=
  (BundleKernel.pairs (offsets.drop 2)).map fun ds =>
    bundleRequestName frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) ds

/-! ## The reveal list -/

def sealKinds : List TlsMpc.Node.RevealKind := [.counterWidths, .sealedEnvelope]
def requestSealKinds : List TlsMpc.Node.RevealKind := [.sealedRecord]

/-- Instructions without a release (public bits, plumbing, runs, frees). -/
theorem plain_label (i : Instr) (h : plain i = true) : i.label? = none := by
  cases i <;> simp_all [plain, InstrP.label?]

theorem frees_plain' (hs : List BoolH) : ∀ i ∈ frees hs, plain i = true := by
  intro i hi
  simp only [frees, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem labelIn_plain {ks : List TlsMpc.Node.RevealKind} {is : List Instr} (h : ∀ i ∈ is, plain i = true) :
    ∀ i ∈ is, LabelIn ks i :=
  fun i hi => LabelIn.of_none (plain_label i (h i hi))

theorem widthsBlock_plain (n : Nat) (cert record : BoolH) (certLen : Nat) :
    ∀ i ∈ widthsBlock n cert record certLen, plain i = true := by
  intro i hi
  simp only [widthsBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem sealBlock_plain (n : Nat) (a : SealArgs) (name : Bytes) (env : Nat) :
    ∀ i ∈ sealBlock n a name env, plain i = true := by
  intro i hi
  simp only [sealBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem afterStatus_reveals (n : Nat) (a : SealArgs) (st : Bits) : Reveals sealKinds (afterStatus n a st) := by
  unfold afterStatus
  split
  · exact every_seqs (every_openThen (LabelIn.of_mem (k := .sealedEnvelope) (by simp [sealKinds]) rfl)
      (fun _ => every_seqs (Every.done _) _ (labelIn_plain (by simp [plain])))) _ (labelIn_plain (by simp [plain]))
  · exact every_seqs (Every.done _) _ (labelIn_plain (by simp [plain]))

theorem afterWidths_reveals (n : Nat) (a : SealArgs) (official : Bool) (classes : Nat) (flags : Bits) :
    Reveals sealKinds (afterWidths n a official classes flags) := by
  unfold afterWidths
  split
  · exact every_seqs (every_openThen (LabelIn.of_mem (k := .sealedEnvelope) (by simp [sealKinds]) rfl)
      (afterStatus_reveals n a)) _ (labelIn_plain (sealBlock_plain _ _ _ _))
  · exact Every.abort _

/-- **T3 for op 41**: every release is labelled counterWidths or sealedEnvelope. -/
theorem seal_reveals (n : Nat) (a : SealArgs) : Reveals sealKinds (sealScript n a) := by
  unfold sealScript
  split
  · split
    · exact every_seqs (every_openThen (LabelIn.of_mem (k := .counterWidths) (by simp [sealKinds]) rfl)
        (fun flags => every_seqs (afterWidths_reveals n a _ _ flags) _ (labelIn_plain (by simp [plain]))))
        _ (labelIn_plain (widthsBlock_plain _ _ _ _))
    · exact Every.abort _
  · exact Every.abort _

/-- **The status gate**: after a status other than 255 the script releases nothing more (and returns
`none`): the timestamp and the envelope are never opened, the stored state is kept. -/
theorem seal_refused_silent (n : Nat) (a : SealArgs) (st : Bits) (h : st ≠ bitsOf [255]) :
    Silent (afterStatus n a st) ∧ afterStatus n a st =
      seqs [.freeBool ⟨n + 5⟩, .freeBool ⟨n + 6⟩, .freeBool ⟨n + 7⟩] (.done none) := by
  unfold afterStatus
  rw [if_neg h]
  exact ⟨Silent.seqs (Silent.done _) _ (fun i hi => plain_label i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl)), rfl⟩

theorem plain_of_all {is : List Instr} (h : is.all plain = true) : ∀ i ∈ is, plain i = true :=
  fun i hi => List.all_eq_true.mp h i hi

theorem deviceWidthsBlock_plain (n : Nat) (a : DevicesArgs) (i : Nat) (d : DeviceArgs) :
    ∀ x ∈ deviceWidthsBlock n a i d, plain x = true := by
  apply plain_of_all
  unfold deviceWidthsBlock
  split <;> rfl

theorem deviceSealBlock_plain (n m : Nat) (a : DevicesArgs) (i : Nat) (d : DeviceArgs) (name : Bytes) (env : Nat) :
    ∀ x ∈ deviceSealBlock n m a i d name env, plain x = true := by
  apply plain_of_all
  unfold deviceSealBlock
  split <;> rfl

theorem afterStatuses_reveals (n m : Nat) (a : DevicesArgs) (envs : List Nat) (st : Bits) :
    Reveals sealKinds (afterStatuses n m a envs st) := by
  unfold afterStatuses
  dsimp only
  split
  · refine every_seqs (every_openThen (LabelIn.of_mem (k := .sealedEnvelope) (by simp [sealKinds]) rfl)
      (fun _ => every_seqs (Every.done _) _ (labelIn_plain ?_))) _ (labelIn_plain (by simp [plain]))
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (((rfl | rfl | rfl) | hx) | hx) | hx <;> first | rfl | exact frees_plain' _ _ hx
  · refine every_seqs (Every.done _) _ (labelIn_plain ?_)
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | hx) | hx) | hx <;> first | rfl | exact frees_plain' _ _ hx

theorem afterFlags_reveals (n : Nat) (a : DevicesArgs) (official : Bool) (classes : Nat) (flags : Bits) :
    Reveals sealKinds (afterFlags n a official classes flags) := by
  unfold afterFlags
  dsimp only
  split
  · refine every_seqs (every_openThen (LabelIn.of_mem (k := .sealedEnvelope) (by simp [sealKinds]) rfl)
      (afterStatuses_reveals _ _ _ _)) _ (labelIn_plain ?_)
    intro x hx
    simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (⟨p, _, hx⟩ | rfl) | hx
    · exact deviceSealBlock_plain _ _ _ _ _ _ _ _ hx
    · rfl
    · exact frees_plain' _ _ hx
  · exact Every.abort _

/-- **T3 for op 61**: every release is labelled counterWidths or sealedEnvelope. -/
theorem devices_reveals (n : Nat) (a : DevicesArgs) : Reveals sealKinds (devicesScript n a) := by
  unfold devicesScript
  dsimp only
  split
  · split
    · refine every_seqs (every_openThen (LabelIn.of_mem (k := .counterWidths) (by simp [sealKinds]) rfl)
        (fun flags => every_seqs (afterFlags_reveals n a _ _ flags) _ (labelIn_plain (by simp [plain]))))
        _ (labelIn_plain ?_)
      intro x hx
      simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (⟨p, _, hx⟩ | rfl) | hx
      · exact deviceWidthsBlock_plain _ _ _ _ _ hx
      · rfl
      · exact frees_plain' _ _ hx
    · exact Every.abort _
  · exact Every.abort _

/-- **T3 for op 42**: nothing released. -/
theorem request_reveals (n : Nat) (cert state : BoolH) : Reveals [] (requestScript n cert state) :=
  every_seqs (Every.done _) _ (labelIn_plain (by simp [plain]))

/-- **T3 for op 62**: nothing released. -/
theorem requestDevices_reveals (n : Nat) (state : BoolH) (ats : List Nat) :
    Reveals [] (requestDevicesScript n state ats) := by
  refine every_seqs (Every.done _) _ (labelIn_plain ?_)
  intro x hx
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (⟨p, _, rfl⟩ | rfl) | hx
  · rfl
  · rfl
  · exact frees_plain' _ _ hx

/-- **T3 for the request's record, first phase**: one release, sealedRecord. -/
theorem requestCtr_reveals (n : Nat) (traffic conv : BoolH) (seq frame mask : B8) (name : Bytes) :
    Reveals requestSealKinds (requestCtrScript n traffic conv seq frame mask name) := by
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .sealedRecord) (by simp [requestSealKinds]) rfl)
    (fun _ => every_seqs ?_ _ (labelIn_plain (by simp [plain])))) _ (labelIn_plain (by simp [plain]))
  split
  · exact Every.done _
  · exact Every.abort _

/-! ## T3 against any adversary (Engine/Reveal.lean `viewD_kinds`) -/

section Views

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

theorem seal_viewD_kinds (n : Nat) (a : SealArgs) :
    ∀ r ∈ (withAdv E me adv (sealScript n a) σ I vD).viewD, ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv sealKinds _ (seal_reveals n a) σ I vD

theorem devices_viewD_kinds (n : Nat) (a : DevicesArgs) :
    ∀ r ∈ (withAdv E me adv (devicesScript n a) σ I vD).viewD, ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv sealKinds _ (devices_reveals n a) σ I vD

theorem request_viewD (n : Nat) (cert state : BoolH) :
    (withAdv E me adv (requestScript n cert state) σ I vD).viewD = [] :=
  viewD_nil E me adv _ (request_reveals n cert state) σ I vD

theorem requestDevices_viewD (n : Nat) (state : BoolH) (ats : List Nat) :
    (withAdv E me adv (requestDevicesScript n state ats) σ I vD).viewD = [] :=
  viewD_nil E me adv _ (requestDevices_reveals n state ats) σ I vD

theorem requestCtr_viewD_kinds (n : Nat) (traffic conv : BoolH) (seq frame mask : B8) (name : Bytes) :
    ∀ r ∈ (withAdv E me adv (requestCtrScript n traffic conv seq frame mask name) σ I vD).viewD,
      ∃ k ∈ requestSealKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv requestSealKinds _ (requestCtr_reveals n traffic conv seq frame mask name) σ I vD

end Views

end TlsMpc.Node.Flows.Send
