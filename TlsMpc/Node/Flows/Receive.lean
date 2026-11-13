import TlsMpc.Node.Flows.Convert
import TlsMpc.Node.Flows.ContactsTable
import TlsMpc.ReceiveKernels

/-!
# `Receive.*`: a new contact's first message as scripts (ops 48-51)

REORGANIZATION_PLAN.md stage S14. Replaces `handshake_backend/EmpHybridWork/service_kernels.h`
`envelope_take`, `envelope_drop`, `envelope_open` (steps 1-12) and `envelope_session` (steps
13-17) (lines 258-408) and the receive dispatch of `tls_worker_v3.cpp` (ops 48-51) for the Lean
flows. Advance work in a new file; the C++ stays in use until the controller switches (the IO glue
of `Flows/ReceiveBackend.lean` is selectable, not selected). No I/O; no emitter imports this module.

THE SCRIPTS run the 13 receive kernels (`TlsMpc/ReceiveKernels.lean`) by their cache names, in the
order of `envelope_open` / `envelope_session`, each kernel's public shape parameters taken from
what the previous stage opened (the C++ `shaped(...)`: parameters `ReceiveKernel.find` would refuse,
or a kernel this worker did not load, REFUSE the message, they do not abort the session). Every
stage is `stage name parts widths`: concat the input handles in the kernel's input order, run the
kernel, slice its output fields, free the temporaries. Bits of bytes least significant first.

  `takeScript` (op 48): a slice `[offset, offset + count)` of a received buffer's revealed bytes
    (S12's `Tls.revealScript` handle) appended to the held envelope (at most 16 384 bytes).
  `dropScript` (op 49): frees the held envelope and arrival.
  `openFirst` (op 50, steps 1-12): envelope point, the agreement with our identity key (S11),
    `receive-unseal-static`, the second agreement, `receive-unseal-message`, OPEN the certificate's
    length prefix (`certificateLength`); gate: the prefix must name a kernel, else refused;
    `receive-content-shape`, OPEN its 4 bytes (`contentShape`); gate: exactly one of plain / hinted
    set; `receive-content`; `receive-certificate` (public signer, time, server key words); the
    signature's challenge bits into the field engine (P-B2F), `xeddsa-check` (or S11's hinted
    variant), its point back to words (P-F2W), `receive-certificate-verified`;
    `receive-prekey-shape`, OPEN its 21 flags (`prekeyShape`); gate: well-formed widths;
    `receive-prekey-open`, OPEN the prekey ids and Kyber ciphertext in one opening (`prekeyIds`);
    the base and ratchet keys into the field engine (P-W2F). Result: refused, or the opened bytes
    and the `Arrival` (handles of what the session needs, all private).
  `session` (op 51, steps 13-17): the base key's validity and torsion (`xeddsa-recover`,
    `receive-torsion`, or S11's hinted variant) back to words; the 6 or 7 agreements (S11);
    `receive-signal-shape`, OPEN its 13 bytes (`signalShape`); gate: a session kernel for them;
    `receive-session` (the `SessionIn` wiring: `verified` is `receive-certificate-verified`'s
    output), OPEN its status (`sessionStatus`); gate: 255, else refused with nothing more opened;
    `receive-text`, OPEN its status (`sessionStatus`); gate: 255; OPEN length ‖ text ‖ layout
    (`receivedText`); `receive-access-key`, OPEN its status (`accessKeyStatus`); gate: 255; keep
    the contact record (the conversation output without our certificate). Result: refused, or the
    text bytes and the record's handle (the IO glue enters it in the contact table).

THE PARAMETERS (S11 and the runner; signatures in S14_NOTES.md):
  * `Curve`: `agree` (the X25519 agreements of a list of jobs, as fresh 255-bit words),
    `signature` (the XEdDSA point `[s]B − [h]A`), `baseCheck` (the base key's validity and
    torsion); each with its `Reveals` proof. `Curve.withPrograms` builds `signature` and
    `baseCheck` from the V3 programs `xeddsa-check`, `xeddsa-recover`, `receive-torsion` through
    the `program` instruction (masks from both parties' fresh field contributions, as
    `Inversion.quotientScript`); S11's hinted mode supplies its own.
  * `loaded`: the kernels the worker loaded (the C++ `shaped` refuses unknown shapes).
The conversions are S10's (`Convert.wordToField`, `fieldToWord`, `bitsToField`) with masks from
the session's pool (`St.pool`); handle ids come from the contact table's counters (`St.table`).

J1 (the join's mask slots, STACK_NOTES.md): every FIELD-ELEMENT input of these flows (a program's
mask contributions, `programStep`; an agreement's quotient masks, `Join.receiveAgree`) reads a
store slot TAKEN from the state's supply `St.slots` (`Gen.takeSlot`: the first entry, removed), so
no slot of fresh randomness is read twice: two openings `b·m`, `b'·m` with one mask `m` would reveal
the ratio `b / b'`. `Flows/JoinOnce.lean` proves it for every run (`openFirst_reads_once`,
`session_reads_once`). Before J1, `ProgramMasks` named the slots and S11's agreements took theirs
as a parameter (`Join.AgreeSlots.masks`), which op 50 used for both of its agreements.

KINDS: `firstKinds` (certificateLength, contentShape, prekeyShape, prekeyIds, and the conversions'
maskedWord, maskedFieldValue, maskedBit), `sessionKinds` (signalShape, sessionStatus, receivedText,
accessKeyStatus, maskedFieldValue), plus the curve's `kinds`. Proved here: `openFirst_reveals`,
`session_reveals`, `take_reveals`, `drop_reveals`; the gating lemmas (`sessionRest_refused`, ...);
in `Flows/ReceiveFlowProofs.lean`: the value-level statements, T4/T13 at function level, WF.
-/

namespace TlsMpc.Node.Flows.Receive

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees bitsOf bytesOf B8 every_seq every_seqs every_openThen
  labelIn_of_none Table Entry)
open TlsMpc.Signal.ReceiveFirst (PreKeyShape SignalShape CertShape)
open TlsMpc.FieldDag (F)

instance : Inhabited BoolH := ⟨⟨0⟩⟩
instance : Inhabited FieldH := ⟨⟨0⟩⟩

/-! ## Kernel names (`service_kernels.h` `shaped(...)` arguments) -/

/-- A kernel's cache name: its name and public shape parameters, space separated. -/
def kname (s : String) (args : List Nat) : Bytes :=
  ascii (args.foldl (fun acc a => acc ++ " " ++ toString a) s)

def envelopePointName (size : Nat) : Bytes := kname "receive-envelope-point" [size]
def unsealStaticName (size : Nat) : Bytes := kname "receive-unseal-static" [size]
def unsealMessageName (size : Nat) : Bytes := kname "receive-unseal-message" [size]
def contentShapeName (u c0 c1 : Nat) : Bytes := kname "receive-content-shape" [u, c0, c1]
def contentName (u c0 c1 hint : Nat) : Bytes := kname "receive-content" [u, c0, c1, hint]
def certificateName (c0 c1 present length : Nat) : Bytes := kname "receive-certificate" [c0, c1, present, length]
def verifiedName : Bytes := kname "receive-certificate-verified" []
def prekeyShapeName (n : Nat) : Bytes := kname "receive-prekey-shape" [n]
def prekeyOpenName (n : Nat) (w : List Nat) : Bytes := kname "receive-prekey-open" (n :: w)
def signalShapeName (n : Nat) (w : List Nat) : Bytes := kname "receive-signal-shape" (n :: w)
def sessionName (cert n : Nat) (w : List Nat) (cw pw low high addr jump : Nat) : Bytes :=
  kname "receive-session" ([cert, n] ++ w ++ [cw, pw, low, high, addr, jump])
def textName (ct cap : Nat) : Bytes := kname "receive-text" [ct, cap]
def accessKeyName (cert ct offset : Nat) : Bytes := kname "receive-access-key" [cert, ct, offset]

/-! ## The output layouts (bits per output field, in the kernels' declared order)

Each list is the kernel's `outputs.map (·.bits)` (`ReceiveKernels.lean`; `ReceiveFlowProofs`
checks the ones whose widths are closed forms against the kernels' definitions). -/

/-- A 255-bit word (a point coordinate or an agreement, little endian, below 2^255). -/
abbrev word : Nat := 255

def envelopePointOut : List Nat := [word]
/-- staticValid, senderIdentity, senderPoint (word), chain. -/
def unsealStaticOut : List Nat := [8, 256, word, 256]
/-- valid, content, certificateLength (opened). -/
def unsealMessageOut (size : Nat) : List Nat := [8, 8 * ReceiveKernel.contentBytes size, 16]
/-- shape (opened, 4 bytes). -/
def contentShapeOut : List Nat := [32]
/-- The message field's length inside a content of `u` bytes with a certificate of `cert`. -/
def messageBytes (u cert : Nat) (hint : Bool) : Nat :=
  TlsMpc.Signal.ReceiveFirst.bodyOf (u - (5 + cert) - (if hint then 2 else 0))
/-- valid, messageType, certificate, message. -/
def contentOut (u cert : Nat) (hint : Bool) : List Nat := [8, 8, 8 * cert, 8 * messageBytes u cert hint]
/-- certificateValid, uuid, deviceId, signature, flip, challenge, scalar. -/
def certificateOut : List Nat := [8, 128, 8, 512, 1, 256, 253]
/-- verified. -/
def verifiedOut : List Nat := [8]
/-- shape (opened, 21 flags). -/
def prekeyShapeOut : List Nat := [168]
/-- prekeyValid, basePoint, ratchetPoint, then opened: one-time id, signed id, Kyber id, Kyber
ciphertext. -/
def prekeyOpenOut : List Nat := [8, word, word, 32, 32, 32, 8 * 1568]
/-- shape (opened, 13 bytes). -/
def signalShapeOut : List Nat := [104]
/-- **The receiver record's fields** (bytes), in `ReceiveFirst.session`'s third result: session root
32, next receiving chain key 32, their ratchet key 32, next receiving counter 4, post-quantum next root
32, next post-quantum receiving chain key 32, post-quantum receiving index 4, their base key 32.

J21 (PROOF_GAPS.md): the script used to slice by `ReceiveKernel.receiverBytes` = 236, which is wrong.
That constant (and the "(236)" in the doc comments of `ReceiveFirst.session` and
`ReceiveKernel.session`) is an arithmetic slip in the kernels' documentation: the eight fields the same
comment lists sum to 200, the kernel's definition has always concatenated exactly these eight parts
(since 9564a25, the commit that introduced it), and nothing in the kernels reads the constant. Those
modules are in the flat emitter's import closure, so they are not edited; this definition outside the
closure is THE width: the script slices by it (`sessionOut`), `ReceiveFlowProofs.session_receiver_bits`
proves the kernel's `receiver` output has `8 * receiverBytes` bits, and the layout checks
(`node_worker/tests/e2e_s14.py`, `loader.rs` `RECEIVER_BYTES`) read it from the `layout` line the S14
vectors print from it. -/
def receiverFields : List Nat := [32, 32, 32, 4, 32, 32, 4, 32]

/-- The receiver record's size in bytes (`receiverFields`), 200. -/
def receiverBytes : Nat := receiverFields.sum

theorem receiverBytes_eq : receiverBytes = 200 := rfl

/-- status (opened), conversation, receiver (`receiverBytes`, J21), plaintext. -/
def sessionOut (cert ct : Nat) : List Nat :=
  [8, 8 * TlsMpc.HybridKernel.conversationBytes cert 80, 8 * receiverBytes, 8 * (8 + ct)]
/-- status, length, text, layout (all opened). -/
def textOut (cap : Nat) : List Nat := [8, 16, 8 * cap, 24]
/-- status (opened), conversation. -/
def accessKeyOut (cert : Nat) : List Nat := [8, 8 * TlsMpc.HybridKernel.conversationBytes cert 80]

/-- The contact record's bytes inside a conversation (`service_kernels.h` CONTACT). -/
def contactBytes : Nat := 319

/-! ## The script state and its combinators -/

/-- The public state the receive scripts thread: the contact table (with the session's handle
counters, `Table.ctr`), the conversions' mask pool, and (J1) the supply of store slots holding
this party's fresh field-element contributions: `(slot, count)`, the slot holding `count` fresh
elements (drawn from `Channels.random` by the IO side before the script runs, decision D1). Each
slot is taken once (`Gen.takeSlot`). -/
structure St where
  table : Table := {}
  pool : Conv.MaskPool := {}
  slots : List (Nat × Nat) := []

/-- Scripts with the public state threaded through. -/
abbrev Gen := StateT St Script

/-- Free field handles, in order. -/
def freeFieldsI (hs : List FieldH) : List Instr := hs.map fun h => .freeField h

namespace Gen

def lift {α : Type} (s : Script α) : Gen α := StateT.lift s
def fail {α : Type} (reason : String) : Gen α := StateT.lift (.abort reason)

/-- A block of `k` fresh Boolean handle ids (the table's counter). -/
def allocB (k : Nat) : Gen Nat := fun st =>
  .done ((st.table.alloc k).1, { st with table := (st.table.alloc k).2 })

/-- A block of `k` fresh field handle ids. -/
def allocF (k : Nat) : Gen Nat := fun st =>
  .done (st.table.ctr.field, { st with table := { st.table with ctr := (st.table.ctr.allocF k).2 } })

/-- Unit-reply instructions. -/
def instrs (is : List Instr) : Gen Unit := lift (seqs is (.done ()))

def freeAll (hs : List BoolH) : Gen Unit := instrs (frees hs)
def freeFields (hs : List FieldH) : Gen Unit := instrs (freeFieldsI hs)

/-- A word mask from the pool (P-CUT (h): each handed out once). -/
def takeWord : Gen Conv.WordMask := fun st =>
  match st.pool.takeWord with
  | some (m, p) => .done (m, { st with pool := p })
  | none => .abort "mask pool"

def takeBits (k : Nat) : Gen (List Conv.BitPair) := fun st =>
  match st.pool.takeBits k with
  | some (ps, p) => .done (ps, { st with pool := p })
  | none => .abort "mask pool"

/-- **J1: a slot of fresh field elements from the supply**, `count` of them: the first entry,
removed from the supply (so it is never handed out again); abort when the supply is empty or its
first entry holds another number of elements. -/
def takeSlot (count : Nat) : Gen Nat := fun st =>
  match st.slots with
  | (s, k) :: rest => if k = count then .done (s, { st with slots := rest }) else .abort "mask slot supply"
  | [] => .abort "mask slot supply"

end Gen

/-- Element `i` of a list of output handles (every list here has its declared length). -/
def at! (o : List BoolH) (i : Nat) : BoolH := o.getD i default
def atF (o : List FieldH) (i : Nat) : FieldH := o.getD i default

/-- Bit offsets of the fields of a layout. -/
def cuts : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | lo, w :: ws => (lo, lo + w) :: cuts (lo + w) ws

/-- The instructions of one kernel stage from handle id `n`: the input bundle, the kernel, one slice
per output field (`n + 2 + i`), the temporaries freed. -/
def stageInstrs (n : Nat) (name : Bytes) (parts : List BoolH) (widths : List Nat) : List Instr :=
  [.concat ⟨n⟩ parts, .run ⟨n + 1⟩ name 1 ⟨n⟩] ++
  ((cuts 0 widths).zipIdx.map fun e => (.slice ⟨n + 2 + e.2⟩ ⟨n + 1⟩ e.1.1 e.1.2 : Instr)) ++
  [.freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]

def stageOuts (n k : Nat) : List BoolH := (List.range k).map fun i => ⟨n + 2 + i⟩

/-- **One kernel stage**: run the kernel `name` on the concatenation of `parts`; its output fields,
one handle each. Releases nothing. -/
def stage (name : Bytes) (parts : List BoolH) (widths : List Nat) : Gen (List BoolH) := do
  let n ← Gen.allocB (2 + widths.length)
  Gen.instrs (stageInstrs n name parts widths)
  pure (stageOuts n widths.length)

/-- Open `h` to both parties with label `l`, then free it. -/
def openFree (h : BoolH) (l : Label) : Gen Bits :=
  Gen.lift (openThen h l fun b => seqs [.freeBool h] (.done b))

/-- Public bits as a fresh handle. -/
def publicBits (b : Bits) : Gen BoolH := do
  let n ← Gen.allocB 1
  Gen.instrs [.boolPublic ⟨n⟩ b]
  pure ⟨n⟩

/-- Party A's private bits (`width` of them, from its store slot `slot`; party B sends none). -/
def inputA (slot width : Nat) : Gen BoolH := do
  let n ← Gen.allocB 1
  Gen.instrs [.boolInput ⟨n⟩ .a width false false slot]
  pure ⟨n⟩

/-- A concatenation as a fresh handle. -/
def join (parts : List BoolH) : Gen BoolH := do
  let n ← Gen.allocB 1
  Gen.instrs [.concat ⟨n⟩ parts]
  pure ⟨n⟩

/-- Bits `[lo, hi)` of a handle as a fresh handle. -/
def cut (h : BoolH) (lo hi : Nat) : Gen BoolH := do
  let n ← Gen.allocB 1
  Gen.instrs [.slice ⟨n⟩ h lo hi]
  pure ⟨n⟩

/-- A public field element as a fresh handle. -/
def publicField (v : F) : Gen FieldH := do
  let f ← Gen.allocF 1
  Gen.instrs [.fieldPublic ⟨f⟩ v]
  pure ⟨f⟩

/-! ## The wiring: which stage output feeds which stage input

Each function below gives a kernel's input parts, in its declared input order
(`ReceiveKernels.lean`: `staticInputs`, `messageInputs`, ...), from earlier stages' output lists
(each list in its kernel's output order). They are POLYMORPHIC: the scripts use them on handles
(`BoolH`), the function-level pipeline of `Flows/ReceiveFlowProofs.lean` on bytes; so what the
pipeline's theorems assume about the wiring (e.g. `ReceiveAccept.session_accept_certificate`'s
"`verified` is `receive-certificate-verified` on `receive-certificate`'s validity and signature")
is the script's own wiring, by definition. -/

section Wiring

variable {α : Type} [Inhabited α]

/-- `receive-unseal-static`: envelope, ourIdentity, agreement. -/
def staticIn (env ours agreement : α) : List α := [env, ours, agreement]
/-- `receive-unseal-message`: envelope, staticValid (`us[0]`), chain (`us[3]`), agreement. -/
def messageIn (env : α) (us : List α) (agreement : α) : List α :=
  [env, us.getD 0 default, us.getD 3 default, agreement]
/-- `receive-content-shape` and `receive-content`: content (`um[1]`), valid (`um[0]`). -/
def contentIn (um : List α) : List α := [um.getD 1 default, um.getD 0 default]
/-- `receive-certificate`: certificate (`ct[2]`), valid (`ct[0]`), senderIdentity (`us[1]`), the
public signer, time and server key words. -/
def certificateIn (ct us : List α) (signer now serverX serverY : α) : List α :=
  [ct.getD 2 default, ct.getD 0 default, us.getD 1 default, signer, now, serverX, serverY]
/-- `receive-certificate-verified`: certificateValid (`ce[0]`), signature (`ce[3]`), serverValid, rx,
ry. -/
def verifiedIn (ce : List α) (serverValid rx ry : α) : List α :=
  [ce.getD 0 default, ce.getD 3 default, serverValid, rx, ry]
/-- The challenge bits of `xeddsa-check`: flip (`ce[4]`), challenge (`ce[5]`), scalar (`ce[6]`). -/
def challengeIn (ce : List α) : List α := [ce.getD 4 default, ce.getD 5 default, ce.getD 6 default]
/-- `receive-prekey-shape`: message (`ct[3]`), valid (`ct[0]`). -/
def prekeyShapeIn (ct : List α) : List α := [ct.getD 3 default, ct.getD 0 default]
/-- `receive-prekey-open`: message, valid, messageType (`ct[1]`), senderIdentity (`us[1]`). -/
def prekeyOpenIn (ct us : List α) : List α :=
  [ct.getD 3 default, ct.getD 0 default, ct.getD 1 default, us.getD 1 default]

/-- What the session needs from steps 1-12 in the Boolean engine (`Arrival`'s wires). -/
structure Held (α : Type) where
  message : α
  prekeyValid : α
  verified : α
  senderIdentity : α
  uuid : α
  device : α
  ours : α

/-- The held wires from the stages' outputs: message `ct[3]`, prekeyValid `po[0]`, verified
`ve[0]`, senderIdentity `us[1]`, uuid `ce[1]`, deviceId `ce[2]`, our identity key. -/
def heldOf (us ct ce ve po : List α) (ours : α) : Held α :=
  ⟨ct.getD 3 default, po.getD 0 default, ve.getD 0 default, us.getD 1 default, ce.getD 1 default,
    ce.getD 2 default, ours⟩

def Held.list (h : Held α) : List α := [h.message, h.prekeyValid, h.verified, h.senderIdentity, h.uuid, h.device, h.ours]

/-- `receive-signal-shape`: message, valid (= prekeyValid). -/
def signalShapeIn (h : Held α) : List α := [h.message, h.prekeyValid]

/-- **The session kernel's inputs, in its declared order** (`ReceiveKernels.sessionInputs`). -/
structure SessionIn (α : Type) where
  message : α
  prekeyValid : α
  verified : α
  senderIdentity : α
  ourIdentity : α
  localAddress : α
  uuid : α
  deviceId : α
  dh1 : α
  dh2 : α
  dh3 : α
  dh4 : Option α
  kemSecret : α
  receiveAgreement : α
  sendAgreement : α
  ratchetPublic : α
  baseValid : α
  torsionX : α
  torsionY : α
  certificate : α
  accessKey : α
  requestId : α

def SessionIn.parts (x : SessionIn α) : List α :=
  [x.message, x.prekeyValid, x.verified, x.senderIdentity, x.ourIdentity, x.localAddress, x.uuid, x.deviceId,
    x.dh1, x.dh2, x.dh3] ++ x.dh4.toList ++
  [x.kemSecret, x.receiveAgreement, x.sendAgreement, x.ratchetPublic, x.baseValid, x.torsionX, x.torsionY,
    x.certificate, x.accessKey, x.requestId]

/-- **The session's wiring**: the held wires, the agreements in `sessionJobs`' order (dh1, dh2, dh3,
receiving, sending, ratchet public, dh4), the base key's checks, our inputs. `verified` is
`receive-certificate-verified`'s output (`heldOf`). -/
def sessionInOf (h : Held α) (ag : List α) (oneTime : Bool) (baseValid torsionX torsionY kem address accessKey
    requestId certificate : α) : SessionIn α :=
  { message := h.message, prekeyValid := h.prekeyValid, verified := h.verified, senderIdentity := h.senderIdentity,
    ourIdentity := h.ours, localAddress := address, uuid := h.uuid, deviceId := h.device,
    dh1 := ag.getD 0 default, dh2 := ag.getD 1 default, dh3 := ag.getD 2 default,
    dh4 := if oneTime then some (ag.getD 6 default) else none, kemSecret := kem,
    receiveAgreement := ag.getD 3 default, sendAgreement := ag.getD 4 default, ratchetPublic := ag.getD 5 default,
    baseValid := baseValid, torsionX := torsionX, torsionY := torsionY, certificate := certificate,
    accessKey := accessKey, requestId := requestId }

/-- `receive-text`: the session's plaintext (`se[3]`). -/
def textIn (se : List α) : List α := [se.getD 3 default]
/-- `receive-access-key`: the session's conversation (`se[1]`) and plaintext (`se[3]`). -/
def accessKeyIn (se : List α) : List α := [se.getD 1 default, se.getD 3 default]

end Wiring

/-! ### The conversions (S10), masks from the pool -/

/-- Word to field (P-W2F): the word's value mod p as a field handle; the word is not freed. -/
def toField (u : BoolH) : Gen FieldH := do
  let m ← Gen.takeWord
  let n ← Gen.allocB 2
  let f ← Gen.allocF 2
  Gen.lift (Convert.wordToField n f u m)

/-- Field to word (P-F2W): a fresh 255-bit word of the element; the element is not freed. -/
def toWord (v : FieldH) : Gen BoolH := do
  let m ← Gen.takeWord
  let n ← Gen.allocB 3
  let f ← Gen.allocF 1
  Gen.lift (Convert.fieldToWord n f v m)

/-- Bits to field (P-B2F): `k` field handles, one per bit of `x`; `x` is not freed. -/
def toFieldBits (x : BoolH) (k : Nat) : Gen (List FieldH) := do
  let ps ← Gen.takeBits k
  let n ← Gen.allocB 4
  let f ← Gen.allocF (2 + k)
  Gen.lift (Convert.bitsToField n f x ps)

/-! ### A V3 field program through the `program` instruction -/

def fieldRange (f k : Nat) : List FieldH := (List.range k).map fun i => ⟨f + i⟩

/-- The instructions of one program step from field id `f`: both parties' fresh mask
contributions (from store slot `slot`, `masks` elements each), the masks as their sums, the
program (its `D` openings released under `l`), the contributions freed. Outputs `f + 3·masks …`. -/
def programInstrs (f : Nat) (name : Bytes) (ins : List FieldH) (outs masks slot : Nat) (l : Label) : List Instr :=
  (if masks = 0 then [] else
    [.fieldInput (fieldRange f masks) (fieldRange (f + masks) masks) .elements false slot] ++
    (List.range masks).map (fun i => (.fieldAdd ⟨f + 2 * masks + i⟩ ⟨f + i⟩ ⟨f + masks + i⟩ : Instr))) ++
  [.program name 1 ins (fieldRange (f + 2 * masks) masks) (fieldRange (f + 3 * masks) outs) l] ++
  (fieldRange f (2 * masks)).map .freeField

/-- The slot of a program step's mask contributions: taken from the supply when the program has
masks (J1), none otherwise. -/
def maskSlot (masks : Nat) : Gen Nat := if masks = 0 then pure 0 else Gen.takeSlot masks

/-- **One field program** on `ins`: `outs` fresh output handles (the program's marks). Its
`masks` mask contributions come from a slot taken from the supply (J1). -/
def programStep (name : Bytes) (ins : List FieldH) (outs masks : Nat) (l : Label) : Gen (List FieldH) := do
  let slot ← maskSlot masks
  let f ← Gen.allocF (3 * masks + outs)
  Gen.instrs (programInstrs f name ins outs masks slot l)
  pure (fieldRange (f + 3 * masks) outs)

/-! ## The parameters: S11's curve pieces -/

/-- The scalar of an X25519 agreement. -/
inductive Scalar where
  /-- Our identity key (secret-shared: S11's account state). -/
  | identity
  /-- An OWN scalar both parties hold (a prekey's private key): this party's 32 bytes in its store
  byte slot `slot`. -/
  | own (slot : Nat)
  /-- A new scalar neither party knows (our new ratchet key): this party's 32 random bytes in its
  store byte slot `slot`; jobs naming the same slot use the same scalar. -/
  | fresh (slot : Nat)
  deriving DecidableEq

/-- The point of an agreement: a private u-coordinate in the field engine, or the base point 9. -/
inductive Point where
  | handle (h : FieldH)
  | base
  deriving DecidableEq

structure Job where
  scalar : Scalar
  point : Point

/-- **S11's curve pieces as the receive scripts use them** (S14_NOTES.md: the signatures and the
specifications S14 relies on). -/
structure Curve where
  /-- The X25519 agreements of `jobs` (clamped scalars, RFC 7748), in the same field rounds: per job
  a FRESH 255-bit Boolean handle (marks never, not once) holding X25519(scalar, point) below p
  (P-F2W); the inputs are not freed. -/
  agree : List Job → Gen (List BoolH)
  /-- The XEdDSA check point `[s]B − [h]A` (`xeddsa-check` on the public server point and the 510
  challenge bits `flip ‖ h ‖ s` as field bits): `(rx, ry)`, fresh secret field handles. -/
  signature : FieldH → FieldH → List FieldH → Gen (FieldH × FieldH)
  /-- The base key's checks (`xeddsa-recover` then `receive-torsion`): `(valid, torsionX,
  torsionY)`, fresh secret field handles (valid is 1, torsion 0 for a torsion-free curve point). -/
  baseCheck : FieldH → Gen (FieldH × FieldH × FieldH)
  /-- The kinds all three release under. -/
  kinds : List TlsMpc.Node.RevealKind
  agree_reveals : ∀ jobs st, Reveals kinds (agree jobs st)
  signature_reveals : ∀ x y bits st, Reveals kinds (signature x y bits st)
  baseCheck_reveals : ∀ b st, Reveals kinds (baseCheck b st)

def xeddsaCheckName : Bytes := ascii "xeddsa-check"
def xeddsaRecoverName : Bytes := ascii "xeddsa-recover"
def torsionName : Bytes := ascii "receive-torsion"

/-- Mask counts of the three programs (the pinned programs' `masks`, fixed at session start). Their
contributions' slots come from the supply, one per program step (J1; before J1 this structure
also named the slots, `checkSlot`, `recoverSlot`, `torsionSlot`). -/
structure ProgramMasks where
  check : Nat := 0
  recover : Nat := 0
  torsion : Nat := 0

/-- `xeddsa-check` through the `program` instruction (`service_kernels.h` line 313). -/
def programSignature (pm : ProgramMasks) (x y : FieldH) (bits : List FieldH) : Gen (FieldH × FieldH) := do
  let o ← programStep xeddsaCheckName ([x, y] ++ bits) 2 pm.check Label.maskedDenominator
  pure (atF o 0, atF o 1)

/-- `xeddsa-recover` then `receive-torsion` through the `program` instruction (lines 358-359);
the recovered coordinates are freed. -/
def programBaseCheck (pm : ProgramMasks) (b : FieldH) : Gen (FieldH × FieldH × FieldH) := do
  let r ← programStep xeddsaRecoverName [b] 3 pm.recover Label.maskedDenominator
  let t ← programStep torsionName [atF r 1, atF r 2] 2 pm.torsion Label.maskedDenominator
  Gen.freeFields [atF r 1, atF r 2]
  pure (atF r 0, atF t 0, atF t 1)

/-! ## The kinds, and `Reveals` through the state -/

/-- The kinds a state-threaded script releases under, from every state. -/
def RevealsG (ks : List TlsMpc.Node.RevealKind) {α : Type} (g : Gen α) : Prop := ∀ st, Reveals ks (g st)

namespace RevealsG

variable {ks : List TlsMpc.Node.RevealKind} {α β : Type}

theorem pure (a : α) : RevealsG ks (Pure.pure a : Gen α) := fun _ => Every.done _

theorem bind {x : Gen α} {f : α → Gen β} (hx : RevealsG ks x) (hf : ∀ a, RevealsG ks (f a)) :
    RevealsG ks (x >>= f) := by
  intro st
  show Reveals ks (Script.bind (x st) fun p => f p.1 p.2)
  exact Every.bind (hx st) (fun p => hf p.1 p.2)

theorem lift {s : Script α} (h : Reveals ks s) : RevealsG ks (Gen.lift s) := by
  intro st
  show Reveals ks (Script.bind s fun a => .done (a, st))
  exact Every.bind h (fun _ => Every.done _)

theorem fail (r : String) : RevealsG ks (Gen.fail r : Gen α) :=
  lift (Every.abort r)

theorem mono {ks' : List TlsMpc.Node.RevealKind} {g : Gen α} (h : RevealsG ks g) (hk : ∀ k ∈ ks, k ∈ ks') :
    RevealsG ks' g := fun st => (h st).mono hk

theorem ite {c : Prop} [Decidable c] {x y : Gen α} (hx : RevealsG ks x) (hy : RevealsG ks y) :
    RevealsG ks (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem allocB (k : Nat) : RevealsG ks (Gen.allocB k) := fun _ => Every.done _
theorem allocF (k : Nat) : RevealsG ks (Gen.allocF k) := fun _ => Every.done _

theorem takeWord : RevealsG ks Gen.takeWord := by
  intro st
  unfold Gen.takeWord
  split
  · exact Every.done _
  · exact Every.abort _

theorem takeBits (k : Nat) : RevealsG ks (Gen.takeBits k) := by
  intro st
  unfold Gen.takeBits
  split
  · exact Every.done _
  · exact Every.abort _

theorem takeSlot (k : Nat) : RevealsG ks (Gen.takeSlot k) := by
  intro st
  unfold Gen.takeSlot
  split
  · split
    · exact Every.done _
    · exact Every.abort _
  · exact Every.abort _

/-- A block of instructions without release. -/
theorem instrs {is : List Instr} (h : ∀ i ∈ is, i.label? = none) : RevealsG ks (Gen.instrs is) :=
  lift (every_seqs (Every.done _) _ (labelIn_of_none h))

end RevealsG

theorem frees_none (hs : List BoolH) : ∀ i ∈ frees hs, i.label? = none := by
  intro i hi
  simp only [frees, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem freeFields_none (hs : List FieldH) : ∀ i ∈ freeFieldsI hs, i.label? = none := by
  intro i hi
  simp only [freeFieldsI, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem RevealsG.freeAll {ks : List TlsMpc.Node.RevealKind} (hs : List BoolH) : RevealsG ks (Gen.freeAll hs) :=
  RevealsG.instrs (frees_none hs)

theorem RevealsG.freeFields {ks : List TlsMpc.Node.RevealKind} (hs : List FieldH) :
    RevealsG ks (Gen.freeFields hs) :=
  RevealsG.instrs (freeFields_none hs)

theorem stageInstrs_none (n : Nat) (name : Bytes) (parts : List BoolH) (widths : List Nat) :
    ∀ i ∈ stageInstrs n name parts widths, i.label? = none := by
  intro i hi
  simp only [stageInstrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hi
  rcases hi with (h | h) | h | h
  · rcases h with rfl | rfl <;> rfl
  · obtain ⟨_, _, rfl⟩ := h; rfl
  · subst h; rfl
  · subst h; rfl

theorem stage_reveals {ks : List TlsMpc.Node.RevealKind} (name : Bytes) (parts : List BoolH) (widths : List Nat) :
    RevealsG ks (stage name parts widths) :=
  RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.instrs (stageInstrs_none n name parts widths)) fun _ => RevealsG.pure _

/-- An opening labelled with a kind of `ks`. -/
theorem openFree_reveals {ks : List TlsMpc.Node.RevealKind} (h : BoolH) (k : TlsMpc.Node.RevealKind)
    (hk : k ∈ ks) : RevealsG ks (openFree h (Label.ofKind k)) :=
  RevealsG.lift (every_openThen (LabelIn.of_mem hk rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))))

theorem publicBits_reveals {ks : List TlsMpc.Node.RevealKind} (b : Bits) : RevealsG ks (publicBits b) :=
  RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.instrs (by simp [InstrP.label?])) fun _ => RevealsG.pure _

theorem inputA_reveals {ks : List TlsMpc.Node.RevealKind} (slot width : Nat) : RevealsG ks (inputA slot width) :=
  RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.instrs (by simp [InstrP.label?])) fun _ => RevealsG.pure _

theorem join_reveals {ks : List TlsMpc.Node.RevealKind} (parts : List BoolH) : RevealsG ks (join parts) :=
  RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.instrs (by simp [InstrP.label?])) fun _ => RevealsG.pure _

theorem cut_reveals {ks : List TlsMpc.Node.RevealKind} (h : BoolH) (lo hi : Nat) : RevealsG ks (cut h lo hi) :=
  RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.instrs (by simp [InstrP.label?])) fun _ => RevealsG.pure _

theorem publicField_reveals {ks : List TlsMpc.Node.RevealKind} (v : F) : RevealsG ks (publicField v) :=
  RevealsG.bind (RevealsG.allocF _) fun n =>
    RevealsG.bind (RevealsG.instrs (by simp [InstrP.label?])) fun _ => RevealsG.pure _

theorem toField_reveals {ks : List TlsMpc.Node.RevealKind} (hk : .maskedWord ∈ ks) (u : BoolH) :
    RevealsG ks (toField u) :=
  RevealsG.bind RevealsG.takeWord fun m => RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.allocF _) fun f =>
      RevealsG.lift ((Convert.w2f_reveals n f u m).mono (by simp [Convert.w2fKinds, hk]))

theorem toWord_reveals {ks : List TlsMpc.Node.RevealKind} (hk : .maskedFieldValue ∈ ks) (v : FieldH) :
    RevealsG ks (toWord v) :=
  RevealsG.bind RevealsG.takeWord fun m => RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.allocF _) fun f =>
      RevealsG.lift ((Convert.f2w_reveals n f v m).mono (by simp [Convert.f2wKinds, hk]))

theorem toFieldBits_reveals {ks : List TlsMpc.Node.RevealKind} (hk : .maskedBit ∈ ks) (x : BoolH) (k : Nat) :
    RevealsG ks (toFieldBits x k) :=
  RevealsG.bind (RevealsG.takeBits k) fun ps => RevealsG.bind (RevealsG.allocB _) fun n =>
    RevealsG.bind (RevealsG.allocF _) fun f =>
      RevealsG.lift ((Convert.b2f_reveals n f x ps).mono (by simp [Convert.b2fKinds, hk]))

theorem programInstrs_label (f : Nat) (name : Bytes) (ins : List FieldH) (outs masks slot : Nat) (l : Label) :
    ∀ i ∈ programInstrs f name ins outs masks slot l, i.label? = none ∨ i.label? = some l := by
  intro i hi
  simp only [programInstrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hi
  rcases hi with (h | h) | h
  · split at h
    · simp at h
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at h
      rcases h with rfl | ⟨_, _, rfl⟩ <;> simp [InstrP.label?]
  · subst h; simp [InstrP.label?]
  · obtain ⟨_, _, rfl⟩ := h; simp [InstrP.label?]

theorem maskSlot_reveals {ks : List TlsMpc.Node.RevealKind} (masks : Nat) : RevealsG ks (maskSlot masks) := by
  unfold maskSlot
  split
  · exact RevealsG.pure _
  · exact RevealsG.takeSlot _

theorem programStep_reveals {ks : List TlsMpc.Node.RevealKind} (k : TlsMpc.Node.RevealKind) (hk : k ∈ ks)
    (name : Bytes) (ins : List FieldH) (outs masks : Nat) :
    RevealsG ks (programStep name ins outs masks (Label.ofKind k)) :=
  RevealsG.bind (maskSlot_reveals _) fun slot =>
  RevealsG.bind (RevealsG.allocF _) fun f =>
    RevealsG.bind (RevealsG.lift (every_seqs (Every.done _) _ (fun i hi => by
      rcases programInstrs_label f name ins outs masks slot _ i hi with h | h
      · exact LabelIn.of_none h
      · exact LabelIn.of_mem hk h))) fun _ => RevealsG.pure _

/-- **The program-based curve pieces** (the non-hinted path): `signature` and `baseCheck` through
the `program` instruction, `agree` from S11; kinds: S11's and `maskedDenominator`. -/
def Curve.withPrograms (agree : List Job → Gen (List BoolH)) (kinds : List TlsMpc.Node.RevealKind)
    (hagree : ∀ jobs st, Reveals kinds (agree jobs st)) (pm : ProgramMasks) : Curve where
  agree := agree
  signature := programSignature pm
  baseCheck := programBaseCheck pm
  kinds := .maskedDenominator :: kinds
  agree_reveals jobs st := (hagree jobs st).mono (fun _ hk => List.mem_cons_of_mem _ hk)
  signature_reveals _ _ _ :=
    RevealsG.bind (programStep_reveals .maskedDenominator List.mem_cons_self _ _ _ _) fun _ => RevealsG.pure _
  baseCheck_reveals _ :=
    RevealsG.bind (programStep_reveals .maskedDenominator List.mem_cons_self _ _ _ _) fun _ =>
      RevealsG.bind (programStep_reveals .maskedDenominator List.mem_cons_self _ _ _ _) fun _ =>
        RevealsG.bind (RevealsG.freeFields _) fun _ => RevealsG.pure _

/-! ## Opened bytes: flags and widths (`service_kernels.h` `flag`, `width`) -/

/-- A flag byte: 255 → true, 0 → false, anything else refuses the message. -/
def flagAt (b : B8) (i : Nat) : Option Bool :=
  if b.getD i 0 = 255 then some true else if b.getD i 0 = 0 then some false else none

/-- 1 + the index of the single set flag among the five at `at_` (all five must be flags). -/
def widthAt (b : B8) (at_ : Nat) : Option Nat :=
  let fs := (List.range 5).map fun i => flagAt b (at_ + i)
  if fs.all Option.isSome then
    match (List.range 5).filter (fun i => fs.getD i none = some true) with
    | [i] => some (i + 1)
    | _ => none
  else none

/-- A two-byte big-endian number. -/
def be2 (b : B8) : Nat := 256 * (b.getD 0 0).toNat + (b.getD 1 0).toNat

/-- `receive-prekey-shape`'s 21 opened flags read as the C++ does (line 321-322): whether a
one-time prekey is named, and the widths `[P, R, S, K]` (P = 0 without a one-time prekey). -/
def prekeyWidths (fl : B8) : Option (Bool × List Nat) := do
  let one ← flagAt fl 0
  let p ← if one then widthAt fl 1 else some 0
  let r ← widthAt fl 6
  let s ← widthAt fl 11
  let k ← widthAt fl 16
  pure (one, [p, r, s, k])

/-- `receive-content-shape`'s bytes 2, 3 as `receive-certificate`'s shape (`ReceiveKernel.find`:
no phone number, or one of 1..127 bytes) and the certificate's layout. -/
def certShapeOf (cert : Nat) (shape : B8) : Option CertShape :=
  let present := (shape.getD 2 0).toNat
  let length := (shape.getD 3 0).toNat
  if (present == 0 && length == 0) || (present == 255 && 0 < length && length < 128) then
    TlsMpc.Signal.ReceiveFirst.certShape cert (if present == 255 then 2 + length else 0)
  else none

/-- The trusted signer the certificate names (line 303-304): the embedded server certificate or
the server key's id, by the size the shape expects. -/
def signerOf (c : CertShape) (signerCertificate signerId : B8) : Option B8 :=
  if c.signerSize == signerCertificate.length then some signerCertificate
  else if c.signerSize == signerId.length then some signerId else none

/-- `receive-signal-shape`'s 13 opened bytes read as the C++ does (lines 382-383): the counter and
previous-counter widths, the ciphertext length prefix's two bytes, the addresses flag. -/
def signalValues (shape : B8) : Option (List Nat) := do
  let cw ← widthAt shape 0
  let pw ← widthAt shape 5
  let addr ← flagAt shape 12
  pure [cw, pw, (shape.getD 10 0).toNat, (shape.getD 11 0).toNat, if addr then 1 else 0]

/-- `receive-text`'s opened length ‖ text ‖ layout read as the C++ does (lines 397-401): the body
and where it starts (4, 5 or 6), when exactly one layout flag is set and the length fits. -/
def textBody (cap : Nat) (out : B8) : Option (B8 × Nat) :=
  let count := be2 out
  let layout := (out.drop (2 + cap)).take 3
  match flagAt layout 0, flagAt layout 1, flagAt layout 2 with
  | some f0, some f1, some f2 =>
    match [f0, f1, f2].findIdx? id, ([f0, f1, f2].filter id).length with
    | some i, 1 => if count ≤ cap then some (((out.drop 2).take count), 4 + i) else none
    | _, _ => none
  | _, _, _ => none

/-! ## Op 48 and op 49: the held envelope -/

/-- The most bytes an envelope may hold (`envelope_take`). -/
def maxEnvelope : Nat := 16384

/-- **Take** (op 48): bytes `[offset, offset + count)` of a received buffer's revealed bytes
`bytes`, appended to the held envelope `env` (its handle and size). Uses fresh ids. -/
def takeScript (env : Option (BoolH × Nat)) (bytes : BoolH) (offset count : Nat) : Gen (BoolH × Nat) := do
  let part ← cut bytes (8 * offset) (8 * (offset + count))
  match env with
  | none => pure (part, count)
  | some (h, size) =>
    let whole ← join [h, part]
    Gen.freeAll [h, part]
    pure (whole, size + count)

/-! ## Op 50: open a first message (steps 1-12) -/

/-- What steps 13-17 need from steps 1-12 (`service_kernels.h` `Arrival`): handles of private
values, and the public layout of the PreKey message. -/
structure Arrival where
  /-- The Boolean wires (`heldOf`; `ours` is our identity public key as public bits). -/
  held : Held BoolH
  senderPoint : FieldH
  base : FieldH
  ratchet : FieldH
  /-- The PreKey message's size and its widths (public). -/
  size : Nat
  widths : List Nat
  oneTime : Bool

def Arrival.bools (a : Arrival) : List BoolH := a.held.list
def Arrival.fields (a : Arrival) : List FieldH := [a.senderPoint, a.base, a.ratchet]

/-- **Drop** (op 49): the held envelope and arrival, freed. -/
def dropScript (env : Option (BoolH × Nat)) (a : Option Arrival) : Gen Unit := do
  Gen.freeAll ((env.map (·.1)).toList ++ (a.map Arrival.bools).getD [])
  Gen.freeFields ((a.map Arrival.fields).getD [])

/-- A refusal: the live handles freed, nothing opened. -/
def refuse {α : Type} (hs : List BoolH) (fs : List FieldH) : Gen (Option α) := do
  Gen.freeAll hs
  Gen.freeFields fs
  pure none

/-- The public inputs of `openFirst`. -/
structure FirstIn where
  /-- Our identity public key (32 bytes). -/
  ours : B8
  /-- The agreed time, 8 bytes big endian (the certificate's expiry is checked against it). -/
  now : B8
  /-- The server key as an Edwards point, computed locally (`xeddsa-recover` on a public value). -/
  serverX : Nat
  serverY : Nat
  /-- The trusted server certificate and the server key's id (the certificate names one). -/
  signerCertificate : B8
  signerId : B8

/-- What step 12 opens: whether a one-time prekey is named, and one-time id (4), signed id (4),
Kyber id (4), Kyber ciphertext (1568). -/
abbrev FirstOpened := Bool × B8

/-- **Steps 11-12**: the prekey message's shape and its public part, the base and ratchet keys into
the field engine. Live on entry: `oursH`, `us[1]`, the content parts `ct[0]`, `ct[1]`, `ct[3]`,
`ce[1]`, `ce[2]`, `ve[0]`; `senderF`. -/
def firstPrekey (loaded : Bytes → Bool) (us ct ce ve : List BoolH) (oursH : BoolH) (senderF : FieldH) (n : Nat) :
    Gen (Option (FirstOpened × Arrival)) := do
  let live := [oursH, at! us 1, at! ct 0, at! ct 1, at! ct 3, at! ce 1, at! ce 2, at! ve 0]
  if !(1800 ≤ n + 80 && 1720 ≤ n && n ≤ 16384 && loaded (prekeyShapeName n)) then refuse live [senderF] else
  let ps ← stage (prekeyShapeName n) (prekeyShapeIn ct) prekeyShapeOut
  let flags ← openFree (at! ps 0) Label.prekeyShape
  match prekeyWidths (bytesOf flags) with
  | none => refuse live [senderF]
  | some (one, w) =>
    if !((ReceiveKernel.preKeyShape? n w).isSome && loaded (prekeyOpenName n w)) then refuse live [senderF] else
    let po ← stage (prekeyOpenName n w) (prekeyOpenIn ct us) prekeyOpenOut
    Gen.freeAll [at! ct 0, at! ct 1]
    let ids ← join [at! po 3, at! po 4, at! po 5, at! po 6]
    Gen.freeAll [at! po 3, at! po 4, at! po 5, at! po 6]
    let opened ← openFree ids Label.prekeyIds
    let baseF ← toField (at! po 1)
    let ratchetF ← toField (at! po 2)
    Gen.freeAll [at! po 1, at! po 2]
    pure (some ((one, bytesOf opened),
      { held := heldOf us ct ce ve po oursH, senderPoint := senderF, base := baseF, ratchet := ratchetF,
        size := n, widths := w, oneTime := one }))

/-- **Steps 7-10**: the sender certificate (everything but the signature in the Boolean engine), the
signature's point in the field engine, `receive-certificate-verified`. Live on entry: `oursH`,
`senderId`, the content parts `ct0 … ct3`; `senderF`. -/
def firstCertificate (cv : Curve) (loaded : Bytes → Bool) (fi : FirstIn) (us ct : List BoolH) (oursH : BoolH)
    (senderF : FieldH) (c0 c1 cert : Nat) (shape : B8) (msg : Nat) :
    Gen (Option (FirstOpened × Arrival)) := do
  match certShapeOf cert shape with
  | none => refuse [oursH, at! us 1, at! ct 0, at! ct 1, at! ct 2, at! ct 3] [senderF]
  | some c =>
    match signerOf c fi.signerCertificate fi.signerId with
    | none => refuse [oursH, at! us 1, at! ct 0, at! ct 1, at! ct 2, at! ct 3] [senderF]
    | some signer =>
      if !(loaded (certificateName c0 c1 (shape.getD 2 0).toNat (shape.getD 3 0).toNat) && loaded verifiedName) then
        refuse [oursH, at! us 1, at! ct 0, at! ct 1, at! ct 2, at! ct 3] [senderF] else
      let signerH ← publicBits (bitsOf signer)
      let nowH ← publicBits (bitsOf fi.now)
      let sx ← publicBits (Conv.word fi.serverX)
      let sy ← publicBits (Conv.word fi.serverY)
      let ce ← stage (certificateName c0 c1 (shape.getD 2 0).toNat (shape.getD 3 0).toNat)
        (certificateIn ct us signerH nowH sx sy) certificateOut
      Gen.freeAll [at! ct 2, signerH, nowH, sx, sy]
      let challenge ← join (challengeIn ce)
      Gen.freeAll (challengeIn ce)
      let bits ← toFieldBits challenge 510
      Gen.freeAll [challenge]
      let sxF ← publicField (TlsMpc.FieldDag.ofNat fi.serverX)
      let syF ← publicField (TlsMpc.FieldDag.ofNat fi.serverY)
      let (rx, ry) ← cv.signature sxF syF bits
      Gen.freeFields ([sxF, syF] ++ bits)
      let rxW ← toWord rx
      let ryW ← toWord ry
      Gen.freeFields [rx, ry]
      let valid ← publicBits (Conv.word 1)
      let ve ← stage verifiedName (verifiedIn ce valid rxW ryW) verifiedOut
      Gen.freeAll (verifiedIn ce valid rxW ryW)
      firstPrekey loaded us ct ce ve oursH senderF msg

/-- **Steps 5-6**: the content's shape and its parts. Live on entry: `oursH`, `us[1]`, `um[0]`,
`um[1]`; `senderF`. -/
def firstContent (cv : Curve) (loaded : Bytes → Bool) (fi : FirstIn) (us um : List BoolH) (oursH : BoolH)
    (senderF : FieldH) (u : Nat) (prefix_ : B8) : Gen (Option (FirstOpened × Arrival)) := do
  let live := [oursH, at! us 1, at! um 0, at! um 1]
  let c0 := (prefix_.getD 0 0).toNat
  let c1 := (prefix_.getD 1 0).toNat
  match ReceiveKernel.certLength c0 c1 with
  | none => refuse live [senderF]
  | some cert =>
    if !(ReceiveKernel.contentOk u cert false && u ≤ 16384 && loaded (contentShapeName u c0 c1)) then
      refuse live [senderF] else
    let cs ← stage (contentShapeName u c0 c1) (contentIn um) contentShapeOut
    let shape ← openFree (at! cs 0) Label.contentShape
    match flagAt (bytesOf shape) 0, flagAt (bytesOf shape) 1 with
    | some plain, some hint =>
      if plain == hint || (bytesOf shape).length != 4 then refuse live [senderF] else
      if !(ReceiveKernel.contentOk u cert hint && loaded (contentName u c0 c1 (if hint then 1 else 0))) then
        refuse live [senderF] else
      let ct ← stage (contentName u c0 c1 (if hint then 1 else 0)) (contentIn um) (contentOut u cert hint)
      Gen.freeAll (contentIn um)
      firstCertificate cv loaded fi us ct oursH senderF c0 c1 cert (bytesOf shape) (messageBytes u cert hint)
    | _, _ => refuse live [senderF]

/-- **Op 50: open the held envelope (`size` bytes) as a new contact's first message.** Refused
(`none`, every handle freed, the envelope included), or what step 12 opened and the arrival. -/
def openFirst (cv : Curve) (loaded : Bytes → Bool) (fi : FirstIn) (env : BoolH) (size : Nat) :
    Gen (Option (FirstOpened × Arrival)) := do
  if !(ReceiveKernel.envelopeOk size && loaded (envelopePointName size) && loaded (unsealStaticName size) &&
      loaded (unsealMessageName size)) then refuse [env] [] else
  -- steps 1-2: the ephemeral key, the agreement with our identity key
  let ep ← stage (envelopePointName size) [env] envelopePointOut
  let ephF ← toField (at! ep 0)
  Gen.freeAll [at! ep 0]
  let a1 ← cv.agree [⟨.identity, .handle ephF⟩]
  Gen.freeFields [ephF]
  -- step 3: the sender's identity key
  let oursH ← publicBits (bitsOf fi.ours)
  let us ← stage (unsealStaticName size) (staticIn env oursH (at! a1 0)) unsealStaticOut
  Gen.freeAll a1
  let senderF ← toField (at! us 2)
  Gen.freeAll [at! us 2]
  -- steps 4-5: the second agreement, the content; open the certificate's length prefix
  let a2 ← cv.agree [⟨.identity, .handle senderF⟩]
  let um ← stage (unsealMessageName size) (messageIn env us (at! a2 0)) (unsealMessageOut size)
  Gen.freeAll ([env, at! us 0, at! us 3] ++ a2)
  let prefix_ ← openFree (at! um 2) Label.certificateLength
  firstContent cv loaded fi us um oursH senderF (ReceiveKernel.contentBytes size) (bytesOf prefix_)

/-! ## Op 51: the new contact's session (steps 13-17) -/

/-- The public inputs of `session`. -/
structure SessionPublic where
  /-- Our account's address (17 bytes: UUID and device id). -/
  address : B8
  /-- The request counter's start (8 bytes; `2^63` as the legacy flow passes it). -/
  requestId : B8
  /-- `SIGNAL_RECEIVE_JUMP` (agreed setting, at most 16). -/
  jump : Nat

/-- The private inputs of `session`: our sender certificate (the account's handle, `cert` bytes),
the store slots of our signed and one-time prekeys' private keys (OWN, both parties hold them), of
the Kyber shared secret (A's input; both hold it), of this party's half of the new ratchet key. -/
structure SessionSecrets where
  certificate : BoolH
  cert : Nat
  signedSlot : Nat
  oneTimeSlot : Nat
  kemSlot : Nat
  ratchetSlot : Nat

/-- The agreements of step 14, in the order of `service_kernels.h` line 367:
dh1, dh2, dh3, receiving, sending, ratchet public, and dh4 when a one-time prekey is named. -/
def sessionJobs (a : Arrival) (ss : SessionSecrets) : List Job :=
  [⟨.own ss.signedSlot, .handle a.senderPoint⟩, ⟨.identity, .handle a.base⟩, ⟨.own ss.signedSlot, .handle a.base⟩,
   ⟨.own ss.signedSlot, .handle a.ratchet⟩, ⟨.fresh ss.ratchetSlot, .handle a.ratchet⟩, ⟨.fresh ss.ratchetSlot, .base⟩] ++
  (if a.oneTime then [⟨.own ss.oneTimeSlot, .handle a.base⟩] else [])

/-- **Steps 16-17 after the session's status was opened**: if it is not 255 the message is refused
and nothing more is opened (`sessionRest_refused`). Otherwise `receive-text` (status first, then
length ‖ text ‖ layout), `receive-access-key` (status), the contact record. -/
def sessionRest (loaded : Bytes → Bool) (cert ct : Nat) (se : List BoolH) (status : Bits) :
    Gen (Option (B8 × BoolH)) := do
  let conversation := at! se 1
  let plaintext := at! se 3
  if bytesOf status != [255] then refuse [conversation, plaintext] [] else
  let cap := ct - 6
  if !(16 ≤ ct && ct % 16 == 0 && ct ≤ 16384 && 0 < cap && loaded (textName ct cap)) then
    refuse [conversation, plaintext] [] else
  let tx ← stage (textName ct cap) (textIn se) (textOut cap)
  let s2 ← openFree (at! tx 0) Label.sessionStatus
  if bytesOf s2 != [255] then refuse [conversation, plaintext, at! tx 1, at! tx 2, at! tx 3] [] else
  let body ← join [at! tx 1, at! tx 2, at! tx 3]
  Gen.freeAll [at! tx 1, at! tx 2, at! tx 3]
  let out ← openFree body Label.receivedText
  match textBody cap (bytesOf out) with
  | none => refuse [conversation, plaintext] []
  | some (text, start) =>
    if !(cert ≤ 1024 && start + text.length + 34 ≤ ct && loaded (accessKeyName cert ct (start + text.length))) then
      refuse [conversation, plaintext] [] else
    let ak ← stage (accessKeyName cert ct (start + text.length)) (accessKeyIn se) (accessKeyOut cert)
    Gen.freeAll [conversation, plaintext]
    let s3 ← openFree (at! ak 0) Label.accessKeyStatus
    if bytesOf s3 != [255] then refuse [at! ak 1] [] else
    let record ← cut (at! ak 1) (8 * cert) (8 * (cert + contactBytes))
    Gen.freeAll [at! ak 1]
    pure (some (text, record))

/-- **Op 51: the new contact's session from the arrival.** Refused (`none`, every handle of the
arrival freed), or the message's text and the contact record's handle (`contactBytes` private
bytes, to be the contact's state). -/
def session (cv : Curve) (loaded : Bytes → Bool) (a : Arrival) (sp : SessionPublic) (ss : SessionSecrets) :
    Gen (Option (B8 × BoolH)) := do
  -- step 14: the base key's checks, our inputs, the agreements
  let (bv, tx, ty) ← cv.baseCheck a.base
  let bvW ← toWord bv
  let txW ← toWord tx
  let tyW ← toWord ty
  Gen.freeFields [bv, tx, ty]
  let kemH ← inputA ss.kemSlot 256
  let addrH ← publicBits (bitsOf sp.address)
  let accH ← publicBits (bitsOf (List.replicate 16 0))
  let reqH ← publicBits (bitsOf sp.requestId)
  let ag ← cv.agree (sessionJobs a ss)
  Gen.freeFields a.fields
  let live := a.bools ++ [bvW, txW, tyW, kemH, addrH, accH, reqH] ++ ag
  -- step 15: the Signal message's shape
  if !(loaded (signalShapeName a.size a.widths)) then refuse live [] else
  let sh ← stage (signalShapeName a.size a.widths) (signalShapeIn a.held) signalShapeOut
  let shape ← openFree (at! sh 0) Label.signalShape
  match signalValues (bytesOf shape) with
  | none => refuse live []
  | some vs =>
    match ReceiveKernel.preKeyShape? a.size a.widths with
    | none => refuse live []
    | some p =>
      match ReceiveKernel.signalShape? (p.signalSize a.size) vs with
      | none => refuse live []
      | some q =>
        let name := sessionName ss.cert a.size a.widths (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) (vs.getD 3 0)
          (vs.getD 4 0) sp.jump
        if !(ss.cert ≤ 1024 && sp.jump ≤ 16 && loaded name) then refuse live [] else
        -- step 16: the session; its status
        let se ← stage name
          (sessionInOf a.held ag a.oneTime bvW txW tyW kemH addrH accH reqH ss.certificate).parts
          (sessionOut ss.cert q.ciphertext)
        Gen.freeAll (live ++ [at! se 2])
        let status ← openFree (at! se 0) Label.sessionStatus
        sessionRest loaded ss.cert q.ciphertext se status

/-! ## The provisional ids (next to `Contacts.assign`, plan S14) -/

/-- The `k`-th provisional id of a session (`PublicServiceController.lean`: 2^128 − 1, then
2^128 − 3, 2^128 − 4, …): a new contact is held under it until the signup token names its id
(`Contacts.assign`). -/
def provisionalId (k : Nat) : Nat := if k = 0 then 2 ^ 128 - 1 else 2 ^ 128 - 2 - k

/-- **Provisional ids are distinct within a session** (fewer than 2^127 messages). -/
theorem provisionalId_inj (j k : Nat) (hj : j < 2 ^ 127) (hk : k < 2 ^ 127)
    (h : provisionalId j = provisionalId k) : j = k := by
  unfold provisionalId at h
  split at h <;> split at h <;> omega

/-- **Provisional ids never collide with application ids** (those below 2^128 − 2^64), for fewer
than 2^64 − 2 messages in a session. -/
theorem provisionalId_high (k : Nat) (hk : k + 2 < 2 ^ 64) : 2 ^ 128 - 2 ^ 64 ≤ provisionalId k := by
  unfold provisionalId
  split <;> omega

/-! ## The kinds each script declares -/

def firstKinds : List TlsMpc.Node.RevealKind :=
  [.certificateLength, .contentShape, .prekeyShape, .prekeyIds, .maskedWord, .maskedFieldValue, .maskedBit]

def sessionKinds : List TlsMpc.Node.RevealKind :=
  [.signalShape, .sessionStatus, .receivedText, .accessKeyStatus, .maskedFieldValue]

theorem refuse_reveals {ks : List TlsMpc.Node.RevealKind} {α : Type} (hs : List BoolH) (fs : List FieldH) :
    RevealsG ks (refuse hs fs : Gen (Option α)) :=
  RevealsG.bind (RevealsG.freeAll hs) fun _ => RevealsG.bind (RevealsG.freeFields fs) fun _ => RevealsG.pure _

theorem take_reveals (env : Option (BoolH × Nat)) (bytes : BoolH) (offset count : Nat) :
    RevealsG [] (takeScript env bytes offset count) := by
  refine RevealsG.bind (cut_reveals _ _ _) fun part => ?_
  cases env with
  | none => exact RevealsG.pure _
  | some p =>
    exact RevealsG.bind (join_reveals _) fun _ => RevealsG.bind (RevealsG.freeAll _) fun _ => RevealsG.pure _

theorem drop_reveals (env : Option (BoolH × Nat)) (a : Option Arrival) : RevealsG [] (dropScript env a) :=
  RevealsG.bind (RevealsG.freeAll _) fun _ => RevealsG.freeFields _

section KindsFirst

variable (cv : Curve) (loaded : Bytes → Bool) (fi : FirstIn)

/-- All kinds of `openFirst` (its own and the curve's). -/
def allFirst : List TlsMpc.Node.RevealKind := firstKinds ++ cv.kinds

theorem mem_allFirst (k : TlsMpc.Node.RevealKind) (hk : k ∈ firstKinds) : k ∈ allFirst cv :=
  List.mem_append_left _ hk

theorem firstPrekey_reveals (us ct ce ve : List BoolH) (oursH : BoolH) (senderF : FieldH) (n : Nat) :
    RevealsG (allFirst cv) (firstPrekey loaded us ct ce ve oursH senderF n) := by
  unfold firstPrekey
  dsimp only
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun ps => ?_
  refine RevealsG.bind (openFree_reveals _ .prekeyShape (mem_allFirst cv _ (by simp [firstKinds]))) fun flags => ?_
  split
  · exact refuse_reveals _ _
  · refine RevealsG.ite (refuse_reveals _ _) ?_
    refine RevealsG.bind (stage_reveals _ _ _) fun po => ?_
    refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
    refine RevealsG.bind (join_reveals _) fun ids => ?_
    refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
    refine RevealsG.bind (openFree_reveals _ .prekeyIds (mem_allFirst cv _ (by simp [firstKinds]))) fun _ => ?_
    refine RevealsG.bind (toField_reveals (mem_allFirst cv _ (by simp [firstKinds])) _) fun _ => ?_
    refine RevealsG.bind (toField_reveals (mem_allFirst cv _ (by simp [firstKinds])) _) fun _ => ?_
    exact RevealsG.bind (RevealsG.freeAll _) fun _ => RevealsG.pure _

theorem firstCertificate_reveals (us ct : List BoolH) (oursH : BoolH) (senderF : FieldH) (c0 c1 cert : Nat)
    (shape : B8) (msg : Nat) :
    RevealsG (allFirst cv) (firstCertificate cv loaded fi us ct oursH senderF c0 c1 cert shape msg) := by
  unfold firstCertificate
  split
  · exact refuse_reveals _ _
  · split
    · exact refuse_reveals _ _
    · refine RevealsG.ite (refuse_reveals _ _) ?_
      refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
      refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
      refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
      refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
      refine RevealsG.bind (stage_reveals _ _ _) fun ce => ?_
      refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
      refine RevealsG.bind (join_reveals _) fun _ => ?_
      refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
      refine RevealsG.bind (toFieldBits_reveals (mem_allFirst cv _ (by simp [firstKinds])) _ _) fun _ => ?_
      refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
      refine RevealsG.bind (publicField_reveals _) fun _ => ?_
      refine RevealsG.bind (publicField_reveals _) fun _ => ?_
      refine RevealsG.bind (fun st => (cv.signature_reveals _ _ _ st).mono (fun k hk => List.mem_append_right _ hk))
        fun r => ?_
      refine RevealsG.bind (RevealsG.freeFields _) fun _ => ?_
      refine RevealsG.bind (toWord_reveals (mem_allFirst cv _ (by simp [firstKinds])) _) fun _ => ?_
      refine RevealsG.bind (toWord_reveals (mem_allFirst cv _ (by simp [firstKinds])) _) fun _ => ?_
      refine RevealsG.bind (RevealsG.freeFields _) fun _ => ?_
      refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
      refine RevealsG.bind (stage_reveals _ _ _) fun _ => ?_
      refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
      exact firstPrekey_reveals cv loaded _ _ _ _ _ _ _

theorem firstContent_reveals (us um : List BoolH) (oursH : BoolH) (senderF : FieldH) (u : Nat) (prefix_ : B8) :
    RevealsG (allFirst cv) (firstContent cv loaded fi us um oursH senderF u prefix_) := by
  unfold firstContent
  dsimp only
  split
  · exact refuse_reveals _ _
  · refine RevealsG.ite (refuse_reveals _ _) ?_
    refine RevealsG.bind (stage_reveals _ _ _) fun cs => ?_
    refine RevealsG.bind (openFree_reveals _ .contentShape (mem_allFirst cv _ (by simp [firstKinds]))) fun _ => ?_
    split
    · refine RevealsG.ite (refuse_reveals _ _) ?_
      refine RevealsG.ite (refuse_reveals _ _) ?_
      refine RevealsG.bind (stage_reveals _ _ _) fun ct => ?_
      refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
      exact firstCertificate_reveals cv loaded fi _ _ _ _ _ _ _ _ _
    · exact refuse_reveals _ _

/-- **T3, kinds (op 50)**: every release of `openFirst`, on every branch, carries a label of
`firstKinds` or of the curve's kinds. -/
theorem openFirst_reveals (env : BoolH) (size : Nat) :
    RevealsG (allFirst cv) (openFirst cv loaded fi env size) := by
  unfold openFirst
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun ep => ?_
  refine RevealsG.bind (toField_reveals (mem_allFirst cv _ (by simp [firstKinds])) _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (fun st => (cv.agree_reveals _ st).mono (fun k hk => List.mem_append_right _ hk)) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeFields _) fun _ => ?_
  refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (toField_reveals (mem_allFirst cv _ (by simp [firstKinds])) _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (fun st => (cv.agree_reveals _ st).mono (fun k hk => List.mem_append_right _ hk)) fun _ => ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (openFree_reveals _ .certificateLength (mem_allFirst cv _ (by simp [firstKinds]))) fun _ => ?_
  exact firstContent_reveals cv loaded fi _ _ _ _ _ _

end KindsFirst

section KindsSession

variable (cv : Curve) (loaded : Bytes → Bool)

def allSession : List TlsMpc.Node.RevealKind := sessionKinds ++ cv.kinds

theorem mem_allSession (k : TlsMpc.Node.RevealKind) (hk : k ∈ sessionKinds) : k ∈ allSession cv :=
  List.mem_append_left _ hk

theorem sessionRest_reveals (cert ct : Nat) (se : List BoolH) (status : Bits) :
    RevealsG (allSession cv) (sessionRest loaded cert ct se status) := by
  unfold sessionRest
  dsimp only
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun tx => ?_
  refine RevealsG.bind (openFree_reveals _ .sessionStatus (mem_allSession cv _ (by simp [sessionKinds]))) fun _ => ?_
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (join_reveals _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (openFree_reveals _ .receivedText (mem_allSession cv _ (by simp [sessionKinds]))) fun _ => ?_
  split
  · exact refuse_reveals _ _
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (openFree_reveals _ .accessKeyStatus (mem_allSession cv _ (by simp [sessionKinds]))) fun _ => ?_
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (cut_reveals _ _ _) fun _ => ?_
  exact RevealsG.bind (RevealsG.freeAll _) fun _ => RevealsG.pure _

/-- **T3, kinds (op 51)**: every release of `session`, on every branch, carries a label of
`sessionKinds` or of the curve's kinds. -/
theorem session_reveals (a : Arrival) (sp : SessionPublic) (ss : SessionSecrets) :
    RevealsG (allSession cv) (session cv loaded a sp ss) := by
  unfold session
  dsimp only
  refine RevealsG.bind (fun st => (cv.baseCheck_reveals _ st).mono (fun k hk => List.mem_append_right _ hk))
    fun r => ?_
  obtain ⟨bv, tx, ty⟩ := r
  dsimp only
  refine RevealsG.bind (toWord_reveals (mem_allSession cv _ (by simp [sessionKinds])) _) fun _ => ?_
  refine RevealsG.bind (toWord_reveals (mem_allSession cv _ (by simp [sessionKinds])) _) fun _ => ?_
  refine RevealsG.bind (toWord_reveals (mem_allSession cv _ (by simp [sessionKinds])) _) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeFields _) fun _ => ?_
  refine RevealsG.bind (inputA_reveals _ _) fun _ => ?_
  refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
  refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
  refine RevealsG.bind (publicBits_reveals _) fun _ => ?_
  refine RevealsG.bind (fun st => (cv.agree_reveals _ st).mono (fun k hk => List.mem_append_right _ hk)) fun _ => ?_
  refine RevealsG.bind (RevealsG.freeFields _) fun _ => ?_
  refine RevealsG.ite (refuse_reveals _ _) ?_
  refine RevealsG.bind (stage_reveals _ _ _) fun _ => ?_
  refine RevealsG.bind (openFree_reveals _ .signalShape (mem_allSession cv _ (by simp [sessionKinds]))) fun _ => ?_
  split
  · exact refuse_reveals _ _
  · split
    · exact refuse_reveals _ _
    · split
      · exact refuse_reveals _ _
      · refine RevealsG.ite (refuse_reveals _ _) ?_
        refine RevealsG.bind (stage_reveals _ _ _) fun _ => ?_
        refine RevealsG.bind (RevealsG.freeAll _) fun _ => ?_
        refine RevealsG.bind (openFree_reveals _ .sessionStatus (mem_allSession cv _ (by simp [sessionKinds]))) fun _ => ?_
        exact sessionRest_reveals cv loaded _ _ _ _

end KindsSession

/-! ## The gating between stages -/

/-- A script that releases nothing (every instruction on every branch has no label). -/
def SilentG {α : Type} (g : Gen α) : Prop := RevealsG [] g

/-- **Nothing after a refused session is opened**: when `receive-session`'s opened status is not
255, the rest of the script releases nothing (it frees the conversation and the plaintext and
returns `none`); in particular `receive-text` is not even run, so its outputs (zero anyway,
`ReceiveAccept.receiveText_gated`) are not opened. -/
theorem sessionRest_refused (loaded : Bytes → Bool) (cert ct : Nat) (se : List BoolH) (status : Bits)
    (h : bytesOf status ≠ [255]) :
    sessionRest loaded cert ct se status = refuse [at! se 1, at! se 3] [] ∧
      SilentG (sessionRest loaded cert ct se status) := by
  have e : sessionRest loaded cert ct se status = refuse [at! se 1, at! se 3] [] := by
    unfold sessionRest
    dsimp only
    rw [if_pos (by simpa using h)]
  exact ⟨e, by rw [e]; exact refuse_reveals _ _⟩

/-- **A refused `receive-text` opens nothing more**: after its status, the length, text and layout
are opened only when the status is 255. -/
theorem refuse_silent {α : Type} (hs : List BoolH) (fs : List FieldH) : SilentG (refuse hs fs : Gen (Option α)) :=
  refuse_reveals hs fs

end TlsMpc.Node.Flows.Receive
