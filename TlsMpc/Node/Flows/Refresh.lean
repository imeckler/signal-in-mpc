import TlsMpc.Node.Flows.Tls
import TlsMpc.Node.Flows.ContactsTable
import TlsMpc.BundleKernels
import TlsMpc.BundleSlotKernels
import TlsMpc.MlKemFastKernels

/-!
# `Refresh.*`: a contact's device refresh as scripts (worker ops 56–60, 64, 65)

REORGANIZATION_PLAN.md stage S15. Replaces `handshake_backend/EmpHybridWork/service_kernels.h`
`bundle_fetch`, `bundle_take`, `bundle_drop`, `bundle_shape`, `bundle_establish` (its nine steps),
`scratch_seal`, `scratch_commit` (lines 631–925) and their dispatch in `tls_worker_v3.cpp` (ops
56–60, 64, 65). Advance work in a new file: the C++ stays in use until the controller switches
(`Flows/RefreshBackend.lean` gives the legacy signatures; nothing selects it yet).

WHAT HAPPENS (MULTI_DEVICE.md section 3). A send answered 409/410: the controllers fetch the
contact's prekey bundles for all devices (`GET /v2/keys/{uuid}/*`, the request naming the contact
in the engines), collect the response body UNOPENED, open only its punctuation shape, establish
one session per device (PQXDH: X25519 agreements and a Kyber-1024 encapsulation), keep the new
sessions as SCRATCH, seal the scratch for the database nodes, and make it the contact's state only
once both parties saw the nodes acknowledge it (ORD-2).

THE SCRIPTS (Boolean handles; `n` the first id of a fresh block from the session counter; bits of
bytes least significant first; every kernel by its cache name; every opening labelled by its kind):

  `fetchScript` (op 56 + the record seal's first phase): the contact's record (the first 319
    bytes of its state) and the frame built in the clear (slots zero) with its WebSocket mask into
    `bundle-fetch-ctr SIZE PAYLOAD UUID KEY` with the send direction's traffic block and the
    record sequence; OPENS accepted ‖ header ‖ ciphertext (`sealedRecord`), aborts unless accepted
    is 255, keeps the GHASH pad (private) for `Tls.tagScript` (the record seal's last phase).
  `takeScript` (op 57): a slice of a received record's content appended to the held body. No
    release.
  `shapeScript` (op 59): the body padded with public zeros to its size class, `bundle-shape CAP`,
    OPENS the flags (`bundleShape`); the padding's flags are dropped (they are zero).
  The establishment of device `index` of `count`, in nine steps (op 60, as the C++):
    step 0 `parseScript` (`bundle-slot`: the item SPLICED and the digit counts, both from the
      same `Widths` — `slotInput`, one source; then `establish-points`), S11's `lift` (device 0
      only), `challengeScript` (`establish-challenges`), S11's `check`, `verifyScript`
      (`establish-verified`, `bundle-rebind`; OPENS `changed` for device 0: `identityChanged`);
    step 1 S11's `agree` (dh1, dh2, dh3, ratchet, base and ratchet publics, dh4);
    steps 2–7 the Kyber-1024 encapsulation WIRED BY THE SCRIPT: `kemHashScript` (both parties'
      32-byte entropy, `kem-hash kyber`, `kem-ntt`), `kemRowScript r` (`kem-matrix r`, `kem-u r`),
      `kemFinishScript` (`kem-v`, `kem-finish kyber`), one block of ids `kemIds` for all six steps;
    step 8 `sessionScript` (`establish-session CERT ONETIME`, OPENS `status`: `deviceStatus`;
      keeps `conversation` and `pending` in the scratch).
  `scratchSealScript` (op 64): the scratch's content (per device record ‖ pending, the C++
    `entries`) as ONE handle, sealed by `Contacts.sealScript` under the nonce (`sealedBlob`); the
    content handle is kept: it is exactly what `scratchCommit` installs.
  `opCommit` (op 65): the contact's state becomes the sealed content (frees the old state, and
    with a new identity key the derived caches); the scratch is emptied.
  `opDrop` (op 58): frees the body and the scratch; the contact table is unchanged.

THE STATE (`RState`, public, Lean side, beside the contact table `Contacts.Table` and sharing its
handle counter): the held body, the device in progress (its handles between steps), the
established devices (scratch), the identity lift of the response, `changed`, `ready`, the sealed
content. Its invariant `RState.Inv` (in `RefreshFlowProofs.lean`) is `Table.Inv`'s pattern.

PARAMETERS (not in this branch; signatures and specifications in S15_NOTES.md):
  `CurveOps` — S11's field-engine parts of the establishment (`lift`, `check`, `agree`);
  `Account` — the account's certificate and sender public key handles (S9/S16 Account flows);
  `SendOps` — S13's per-device seal (`Flow.Send.sealDevices`), handed a device's records.

No I/O; no emitter imports this module (it imports kernel modules, it is not imported by them).
-/

namespace TlsMpc.Node.Flows.Refresh

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Signal.BundleResponse (Widths)

/-! ## Names -/

def flag (b : Bool) : String := if b then "1" else "0"

def fetchName (size payloadAt uuidAt keyAt : Nat) : Bytes :=
  ascii ("bundle-fetch-ctr " ++ toString size ++ " " ++ toString payloadAt ++ " " ++ toString uuidAt ++ " " ++
    toString keyAt)
def shapeName (cap : Nat) : Bytes := name1 "bundle-shape" cap
def slotName (first last oneTime : Bool) : Bytes :=
  ascii ("bundle-slot " ++ flag first ++ " " ++ flag last ++ " " ++ flag oneTime)
def pointsName (oneTime : Bool) : Bytes := ascii ("establish-points " ++ flag oneTime)
def challengesName : Bytes := name0 "establish-challenges"
def verifiedName : Bytes := name0 "establish-verified"
def rebindName : Bytes := name0 "bundle-rebind"
def sessionName (cert : Nat) (oneTime : Bool) : Bytes :=
  ascii ("establish-session " ++ toString cert ++ " " ++ flag oneTime)
def kemHashName : Bytes := name0 "kem-hash kyber"
def kemNttName : Bytes := name0 "kem-ntt"
def kemMatrixName (r : Nat) : Bytes := name1 "kem-matrix" r
def kemUName (r : Nat) : Bytes := name1 "kem-u" r
def kemVName : Bytes := name0 "kem-v"
def kemFinishName : Bytes := name0 "kem-finish kyber"

/-! ## Sizes (bytes) and layouts (bit offsets) -/

/-- One device's record (`BundleKernel.recordBytes`). -/
def recordBytes : Nat := 319
/-- `EstablishKernel.pendingBytes`. -/
def pendingBytes : Nat := 1616
/-- One established device in the stored content: record ‖ pending (`Contacts.deviceBytes 1`). -/
def deviceContent : Nat := recordBytes + pendingBytes

/-- The largest body (`bundle_take`'s bound) and the smallest a response of one device has. -/
def maxBody : Nat := 65536
def minBody : Nat := 2540

/-- **The splice's filler byte**: what the runtime inserts before each number of an item to reach
its slot (`BundleSlots.splice`; `bundle_establish`'s `'0'`). ONE place: another branch changes the
kernel's padding to NUL; the theorems used depend on the kernel theorems' names only, and this
constant is the one line to follow it (S15_NOTES.md, merge notes). -/
def slotFiller : BitVec 8 := 48

/-- `bundle-slot`'s outputs (byte widths): valid, identityKey, deviceId, registrationId,
signedPrekeyId, signedPrekey, signedPrekeySignature, kyberPrekeyId, kyberPrekey,
kyberPrekeySignature, and with a one-time prekey oneTimePrekeyId, oneTimePrekey. -/
def slotOutWidths (oneTime : Bool) : List Nat :=
  [1, 32, 1, 4, 4, 32, 64, 4, 1568, 64] ++ (if oneTime then [4, 32] else [])

/-- A field of `bundle-slot`'s output bundle as (bit offset, bit width). -/
def F_valid : Nat × Nat := (0, 8)
def F_identityKey : Nat × Nat := (8, 256)
def F_deviceId : Nat × Nat := (264, 8)
def F_registrationId : Nat × Nat := (272, 32)
def F_signedPrekeyId : Nat × Nat := (304, 32)
def F_signedPrekey : Nat × Nat := (336, 256)
def F_signedSignature : Nat × Nat := (592, 512)
def F_kyberPrekeyId : Nat × Nat := (1104, 32)
def F_kyberPrekey : Nat × Nat := (1136, 12544)
def F_kyberSignature : Nat × Nat := (13680, 512)
def F_oneTimePrekeyId : Nat × Nat := (14192, 32)
def F_oneTimePrekey : Nat × Nat := (14224, 256)

/-- A word: a 255-bit value as the field-to-Boolean conversion delivers it (`Shape.word`). -/
def wordBits : Nat := 255

/-- `kem-finish`'s outputs: kemStatus 1, kemCiphertext 1568, kemSecret 32 (bits). -/
def K_status : Nat × Nat := (0, 8)
def K_ciphertext : Nat × Nat := (8, 12544)
def K_secret : Nat × Nat := (12552, 256)

/-- `bundle-rebind`'s outputs: verified 1, uuid 16, accessKey 16, changed 1 (public). -/
def R_verified : Nat × Nat := (0, 8)
def R_uuid : Nat × Nat := (8, 128)
def R_accessKey : Nat × Nat := (136, 128)
def R_changed : Nat × Nat := (264, 8)

/-- A slice instruction of a field. -/
def sliceOf (out h : Nat) (f : Nat × Nat) : Instr := .slice ⟨out⟩ ⟨h⟩ f.1 (f.1 + f.2)

/-! ## The splice and the digit counts: ONE source

`bundle-slot` takes the item SPLICED into the fixed-width slot layout and the five digit counts as
the `widths` input. Both come from the one `Widths` value here: `cutPositions` uses
`BundleSlots.splice w` and `widthsOf w` is the counts of the same `w`, and the script's only
public input about the item is `w`. So the runtime cannot splice with one set of counts and
declare another (`BundleSlotWhole.inconsistent_width_accepts`: that combination was a proved
defect class). -/

/-- The digit counts as `bundle-slot`'s `widths` input (one byte each). -/
def widthsOf (w : Widths) : B8 :=
  [BitVec.ofNat 8 w.device, BitVec.ofNat 8 w.registration, BitVec.ofNat 8 w.signed, BitVec.ofNat 8 w.oneTime,
    BitVec.ofNat 8 w.kyber]

/-- The runs `(zeros, copy)` as byte positions in `body ‖ [filler]` (the filler at `fill`): `zeros`
times the filler, then the next `copy` bytes of the body from `p`. -/
def runPositions (fill : Nat) : Nat → List (Nat × Nat) → List Nat
  | _, [] => []
  | p, (k, c) :: rs => List.replicate k fill ++ List.range' p c ++ runPositions fill (p + c) rs

/-- The size of an item in the body for the digit counts `w`. -/
def itemSize (w : Widths) : Nat := TlsMpc.Signal.BundleResponse.size (TlsMpc.Signal.BundleResponse.item w)

/-- Byte positions, in `body ‖ [filler]` (`total` = the body's length, the filler at `total`), of
`bundle-slot`'s byte inputs in order: `head`, `before` (unless first), the item SPLICED by
`BundleSlots.splice w`, `after` (unless last), `end`. -/
def cutPositions (total start : Nat) (w : Widths) (first last : Bool) : List Nat :=
  List.range' 0 TlsMpc.Signal.BundleResponse.firstItem ++ (if first then [] else [start - 1]) ++
    runPositions total start (TlsMpc.Signal.BundleSlots.splice w) ++
    (if last then [] else [start + itemSize w]) ++ [total - 2, total - 1]

/-- The bit indices of byte positions (`pick`). -/
def byteBits (ps : List Nat) : List Nat := ps.flatMap fun p => List.range' (8 * p) 8

/-- The item is placed as `layout?` places it (`BundleItemWhole.Placed`), and the counts are
possible: what the script requires before cutting (`bundle_establish`'s refusal, made exact). -/
def placedOk (total start : Nat) (w : Widths) (first last : Bool) : Bool :=
  w.ok && decide (TlsMpc.Signal.BundleResponse.firstItem ≤ start) && decide (start + itemSize w + 2 ≤ total) &&
    (first == decide (start = TlsMpc.Signal.BundleResponse.firstItem)) && (last == decide (start + itemSize w + 2 = total))

/-! ## Parameters -/

/-- **S11's field-engine parts of the establishment** (`Flows/Curve.lean`; signatures and
specifications in S15_NOTES.md). Each takes the session counters at the start of its own block
(`bools`, `fields` ids, allocated by the caller) and returns FRESH Boolean handles of 255 private
bits (words, marks `never`, not `once`); it releases only under `kinds` (S11's: `maskedWord`,
`maskedFieldValue`, `maskedBit`, `maskedDenominator`, `curveChecks`, `liftW`, `liftZ`,
`pointValid`, `scalarBitChecks`, `commitment`, `commitOpening`), never opens its argument handles,
and frees nothing it was given. -/
structure CurveOps where
  /-- Ids each call uses: (Boolean, field). -/
  liftIds : Nat × Nat
  checkIds : Nat × Nat
  agreeIds : Nat × Nat
  /-- `xeddsa-recover` (or the hinted lift) of the identity point: (valid, x, y). -/
  lift : Counters → BoolH → Script (BoolH × BoolH × BoolH)
  /-- `xeddsa-check` of both signatures from (x, y) and the challenge halves (flip, challenge,
  scalar: 510 bits each): (ecRx, ecRy, pqRx, pqRy). -/
  check : Counters → BoolH → BoolH → BoolH → BoolH → Script (BoolH × BoolH × BoolH × BoolH)
  /-- The X25519 agreements with two fresh shared scalars (base, ratchet) and the account's identity
  scalar, on the identity, signed and one-time points: dh1, dh2, dh3, ratchetAgreement,
  basePublic, ratchetPublic, and dh4 when a one-time point is given. -/
  agree : Counters → BoolH → BoolH → Option BoolH → Script (List BoolH)
  /-- The kinds its releases carry. -/
  kinds : List TlsMpc.Node.RevealKind

/-- The account's handles the establishment reads (Account flows): its sender certificate
(`cert` bytes) and its identity public key (`senderPublic`, a word). -/
structure Account where
  certificate : BoolH
  cert : Nat
  senderPublic : BoolH

/-! ## The state -/

/-- What `parseScript` leaves for the rest of the device's steps. -/
structure Parsed where
  fields : BoolH
  identityPoint : BoolH
  signedPoint : BoolH
  oneTimePoint : Option BoolH

def Parsed.handles (p : Parsed) : List BoolH := [p.fields, p.identityPoint, p.signedPoint] ++ p.oneTimePoint.toList

/-- The identity key lifted (device 0's, reused by the response's other devices). -/
structure Lifted where
  valid : BoolH
  x : BoolH
  y : BoolH

def Lifted.handles (l : Lifted) : List BoolH := [l.valid, l.x, l.y]

/-- One device between its steps. -/
structure Progress where
  index : Nat
  step : Nat
  oneTime : Bool
  parsed : Option Parsed := none
  bound : Option BoolH := none
  agreements : List BoolH := []
  /-- The KEM block's first id (steps 2–7). -/
  kem : Option Nat := none
  /-- The KEM block's handles alive between its steps (after step 7: the result `k + 32`). -/
  kemHeld : List BoolH := []

/-- An established device in the scratch: `establish-session`'s `conversation` (certificate ‖
record) and `pending` outputs. -/
structure Device where
  conversation : BoolH
  pending : BoolH
  oneTime : Bool

def Device.handles (d : Device) : List BoolH := [d.conversation, d.pending]
/-- The stored kind (`service_kernels.h`: 2 with a one-time prekey, else 1). -/
def Device.kind (d : Device) : Nat := if d.oneTime then 2 else 1

/-- **The refresh state** (the C++ `bundle` and `Establishing`), public, Lean side. -/
structure RState where
  body : Option (BoolH × Nat) := none
  contact : Option Nat := none
  count : Nat := 0
  lifted : Option Lifted := none
  progress : Option Progress := none
  done : List Device := []
  statuses : List Nat := []
  changed : Bool := false
  /-- Every device's status opened 255: the scratch is complete. -/
  ready : Bool := false
  /-- The scratch's content as sealed (`scratchSealScript`): handle, bytes, kinds. -/
  sealed : Option (BoolH × Nat × List Nat) := none

/-! ## Scripts: the fetch, the body, the shape -/

/-- The 8-byte big-endian value (`TlsWorker`'s `uint 8`). -/
def be (k v : Nat) : B8 := (List.range k).map fun i => BitVec.ofNat 8 (v / 256 ^ (k - 1 - i))

/-- **The prekey fetch, first phase of its record seal** (op 56 and the C++ sealer
`bundle-fetch-ctr`): the frame (`size` bytes, its two slots zero) and its 4-byte mask, the
contact's record (`state`'s first 319 bytes), the send direction's traffic block and the record
sequence. Opens accepted ‖ header ‖ ciphertext (`sealedRecord`); aborts unless accepted is 255;
returns header ‖ ciphertext and the private GHASH pad for `Tls.tagScript`. Uses ids `n … n+6`. -/
def fetchScript (n : Nat) (traffic state : BoolH) (seq : B8) (frame mask : B8) (payloadAt uuidAt keyAt : Nat) :
    Script (B8 × BoolH) :=
  let size := frame.length
  let body := 1 + 5 + size + 1
  seqs [.slice ⟨n⟩ state 0 (8 * recordBytes),
        .boolPublic ⟨n + 1⟩ (bitsOf seq),
        .boolPublic ⟨n + 2⟩ (bitsOf frame ++ bitsOf mask),
        .concat ⟨n + 3⟩ [traffic, ⟨n + 1⟩, ⟨n⟩, ⟨n + 2⟩],
        .run ⟨n + 4⟩ (fetchName size payloadAt uuidAt keyAt) 1 ⟨n + 3⟩,
        .slice ⟨n + 5⟩ ⟨n + 4⟩ (8 * body) (8 * (body + 16)),
        .slice ⟨n + 6⟩ ⟨n + 4⟩ 0 (8 * body),
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩, .freeBool ⟨n + 3⟩, .freeBool ⟨n + 4⟩]
    (openThen ⟨n + 6⟩ Label.sealedRecord fun out =>
      seqs [.freeBool ⟨n + 6⟩]
        (if (bytesOf out).take 1 = [255] then .done ((bytesOf out).drop 1, ⟨n + 5⟩)
         else .abort "prekey fetch record"))

/-- **Collect `count` bytes of a received record's content from `offset`** (op 57), appended to
the held body (or starting it). Nothing released. Uses ids `n, n+1`. -/
def takeScript (n : Nat) (body : Option BoolH) (content : BoolH) (offset count : Nat) : Script BoolH :=
  match body with
  | none => seqs [.slice ⟨n⟩ content (8 * offset) (8 * (offset + count))] (.done ⟨n⟩)
  | some b =>
    seqs [.slice ⟨n⟩ content (8 * offset) (8 * (offset + count)), .concat ⟨n + 1⟩ [b, ⟨n⟩],
          .freeBool b, .freeBool ⟨n⟩] (.done ⟨n + 1⟩)

/-- The size class a body is padded to (`TlsKernels::record_capacity`). -/
def shapeCapacity (size : Nat) : Nat := Tls.capacity size

/-- **The body's punctuation shape** (op 59): the body and public zeros up to the size class,
`bundle-shape CAP`; OPENS the flags (`bundleShape`), returns one per body byte (whether it is 255).
Uses ids `n … n+2`. -/
def shapeScript (n : Nat) (body : BoolH) (size : Nat) : Script (List Bool) :=
  let cap := shapeCapacity size
  seqs [.boolPublic ⟨n⟩ (List.replicate (8 * (cap - size)) false),
        .concat ⟨n + 1⟩ [body, ⟨n⟩],
        .run ⟨n + 2⟩ (shapeName cap) 1 ⟨n + 1⟩,
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]
    (openThen ⟨n + 2⟩ Label.bundleShape fun out =>
      seqs [.freeBool ⟨n + 2⟩] (.done (((bytesOf out).take size).map (· == 255))))

/-! ## Scripts: one device, step 0 -/

/-- The bits fed to `bundle-slot`, from `body ‖ [filler]` and the counts (`slotInput`'s pick). -/
def slotIndices (total start : Nat) (w : Widths) (first last : Bool) : List Nat :=
  byteBits (cutPositions total start w first last)

/-- **`bundle-slot`'s input from ONE `Widths`**: the instructions that build it (ids `n … n+4`; the
input bundle is `n + 4`). The pick takes the cut and the splice of `w`; the public `widths` are
`widthsOf w`. -/
def slotInput (n : Nat) (body : BoolH) (total start : Nat) (w : Widths) (first last : Bool) : List Instr :=
  [.boolPublic ⟨n⟩ (bitsOf [slotFiller]),
   .concat ⟨n + 1⟩ [body, ⟨n⟩],
   .pick ⟨n + 2⟩ ⟨n + 1⟩ (slotIndices total start w first last),
   .boolPublic ⟨n + 3⟩ (bitsOf (widthsOf w)),
   .concat ⟨n + 4⟩ [⟨n + 2⟩, ⟨n + 3⟩]]

/-- **Step 0, first part** (`bundle-slot`, `establish-points`): the device's fields (private) and
its keys as 255-bit words. Uses ids `n … n+13`. Refuses (returns `none`, nothing run) unless the
item is placed as `layout?` places it. -/
def parseScript (n : Nat) (body : BoolH) (total start : Nat) (w : Widths) (first last : Bool) :
    Script (Option Parsed) :=
  let o := w.oneTime != 0
  if placedOk total start w first last then
    seqs (slotInput n body total start w first last ++
          [.run ⟨n + 5⟩ (slotName first last o) 1 ⟨n + 4⟩,
           sliceOf (n + 6) (n + 5) F_identityKey,
           sliceOf (n + 7) (n + 5) F_signedPrekey] ++
          (if o then [sliceOf (n + 8) (n + 5) F_oneTimePrekey] else []) ++
          [.concat ⟨n + 9⟩ ([⟨n + 6⟩, ⟨n + 7⟩] ++ (if o then [⟨n + 8⟩] else [])),
           .run ⟨n + 10⟩ (pointsName o) 1 ⟨n + 9⟩,
           .slice ⟨n + 11⟩ ⟨n + 10⟩ 0 wordBits,
           .slice ⟨n + 12⟩ ⟨n + 10⟩ wordBits (2 * wordBits)] ++
          (if o then [.slice ⟨n + 13⟩ ⟨n + 10⟩ (2 * wordBits) (3 * wordBits)] else []) ++
          frees ([⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 6⟩, ⟨n + 7⟩] ++
            (if o then [⟨n + 8⟩] else []) ++ [⟨n + 9⟩, ⟨n + 10⟩]))
      (.done (some ⟨⟨n + 5⟩, ⟨n + 11⟩, ⟨n + 12⟩, if o then some ⟨n + 13⟩ else none⟩))
  else .done none

/-- **Step 0, the challenges** (`establish-challenges`): the identity key's (x, y) and the bundle's
signed prekey, Kyber prekey and their signatures; returns the two signatures' halves (flip,
challenge, scalar: 510 bits each) for S11's `check`. Uses ids `n … n+8`. -/
def challengeScript (n : Nat) (fields : BoolH) (l : Lifted) : Script (BoolH × BoolH) :=
  seqs [sliceOf n fields.id F_signedPrekey, sliceOf (n + 1) fields.id F_signedSignature,
        sliceOf (n + 2) fields.id F_kyberPrekey, sliceOf (n + 3) fields.id F_kyberSignature,
        .concat ⟨n + 4⟩ [l.x, l.y, ⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩],
        .run ⟨n + 5⟩ challengesName 1 ⟨n + 4⟩,
        .slice ⟨n + 6⟩ ⟨n + 5⟩ 0 510, .slice ⟨n + 7⟩ ⟨n + 5⟩ 510 1020]
    (seqs (frees [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩]) (.done (⟨n + 6⟩, ⟨n + 7⟩)))

/-- **Step 0, last part** (`establish-verified`, `bundle-rebind`): the private `verified` byte from
the lift's validity and the recomputed points; the rebind against the contact's record (`state`'s
first 319 bytes) gives the private (verified, uuid, accessKey) kept for step 8, and `changed`,
OPENED for device 0 only (`identityChanged`). Returns the rebind's handle and, for device 0,
whether the identity key is a new one. Frees the four points. Uses ids `n … n+9`. -/
def verifyScript (n : Nat) (state fields : BoolH) (l : Lifted) (r : BoolH × BoolH × BoolH × BoolH)
    (first : Bool) : Script (BoolH × Bool) :=
  seqs [sliceOf n fields.id F_signedSignature, sliceOf (n + 1) fields.id F_kyberSignature,
        .concat ⟨n + 2⟩ [l.valid, r.1, r.2.1, r.2.2.1, r.2.2.2, ⟨n⟩, ⟨n + 1⟩],
        .run ⟨n + 3⟩ verifiedName 1 ⟨n + 2⟩,
        .slice ⟨n + 4⟩ state 0 (8 * recordBytes),
        sliceOf (n + 5) fields.id F_valid, sliceOf (n + 6) fields.id F_identityKey,
        .concat ⟨n + 7⟩ [⟨n + 4⟩, ⟨n + 5⟩, ⟨n + 3⟩, ⟨n + 6⟩],
        .run ⟨n + 8⟩ rebindName 1 ⟨n + 7⟩]
    (seqs (frees [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩, ⟨n + 6⟩, ⟨n + 7⟩, r.1, r.2.1, r.2.2.1,
        r.2.2.2])
      (if first then
        seqs [sliceOf (n + 9) (n + 8) R_changed]
          (openThen ⟨n + 9⟩ Label.identityChanged fun c =>
            seqs [.freeBool ⟨n + 9⟩] (.done (⟨n + 8⟩, bytesOf c = [255])))
       else .done (⟨n + 8⟩, false)))

/-! ## Scripts: steps 2–7, the encapsulation wired by the script

One block of `kemIds` ids from `k`: entropy `k, k+1`; `kem-hash` input `k+2`, output `k+3`
(message, kbar, coins, keyValid at `k+4 … k+7`); `kem-ntt` `k+8` (rhat); per row `r` at
`m = k + 9 + 5r`: `kem-matrix r` `m`, its row `m+1` and ok `m+2`, `kem-u r` input `m+3`, output
`m+4`; `kem-v` input `k+29`, output `k+30`; `kem-finish` input `k+31`, output `k+32` (status,
ciphertext, secret). Every input is bound by the kernel's declared field order
(`MlKemFastKernel.hashInputs`, `nttInputs`, `matrixInputs`, `uInputs r`, `vInputs`, `finishInputs`). -/

def kemIds : Nat := 33
def kemRow (k r : Nat) : Nat := k + 9 + 5 * r

/-- Step 2: both parties' 32-byte entropy (`slot`: this party's), `kem-hash kyber`, `kem-ntt`. -/
def kemHashInstrs (k : Nat) (key : BoolH) (slot : Nat) : List Instr :=
  [.boolInputBoth ⟨k⟩ ⟨k + 1⟩ 256 true false slot,
   .concat ⟨k + 2⟩ [key, ⟨k⟩, ⟨k + 1⟩],
   .run ⟨k + 3⟩ kemHashName 1 ⟨k + 2⟩,
   .slice ⟨k + 4⟩ ⟨k + 3⟩ 0 256, .slice ⟨k + 5⟩ ⟨k + 3⟩ 256 512, .slice ⟨k + 6⟩ ⟨k + 3⟩ 512 768,
   .slice ⟨k + 7⟩ ⟨k + 3⟩ 768 776,
   .run ⟨k + 8⟩ kemNttName 1 ⟨k + 6⟩]

/-- Steps 3–6: row `r` (`kem-matrix r` on the key, `kem-u r` on row ‖ rhat ‖ coins). -/
def kemRowInstrs (k : Nat) (key : BoolH) (r : Nat) : List Instr :=
  let m := kemRow k r
  [.run ⟨m⟩ (kemMatrixName r) 1 key,
   .slice ⟨m + 1⟩ ⟨m⟩ 0 12288, .slice ⟨m + 2⟩ ⟨m⟩ 12288 12296,
   .concat ⟨m + 3⟩ [⟨m + 1⟩, ⟨k + 8⟩, ⟨k + 6⟩],
   .run ⟨m + 4⟩ (kemUName r) 1 ⟨m + 3⟩]

/-- Step 7: `kem-v` on key ‖ rhat ‖ coins ‖ message, `kem-finish kyber` on u0‖u1‖u2‖u3‖v‖kbar‖
ok0‖ok1‖ok2‖ok3‖keyValid; frees everything but the result `k + 32`. -/
def kemFinishInstrs (k : Nat) (key : BoolH) : List Instr :=
  [.concat ⟨k + 29⟩ [key, ⟨k + 8⟩, ⟨k + 6⟩, ⟨k + 4⟩],
   .run ⟨k + 30⟩ kemVName 1 ⟨k + 29⟩,
   .concat ⟨k + 31⟩ [⟨kemRow k 0 + 4⟩, ⟨kemRow k 1 + 4⟩, ⟨kemRow k 2 + 4⟩, ⟨kemRow k 3 + 4⟩, ⟨k + 30⟩, ⟨k + 5⟩,
     ⟨kemRow k 0 + 2⟩, ⟨kemRow k 1 + 2⟩, ⟨kemRow k 2 + 2⟩, ⟨kemRow k 3 + 2⟩, ⟨k + 7⟩],
   .run ⟨k + 32⟩ kemFinishName 1 ⟨k + 31⟩] ++
  frees ((List.range 29).map fun j => ⟨k + 3 + j⟩)

/-- **The whole encapsulation block** (steps 2–7 in order). -/
def kemBlock (k : Nat) (key : BoolH) (slot : Nat) : List Instr :=
  kemHashInstrs k key slot ++ kemRowInstrs k key 0 ++ kemRowInstrs k key 1 ++ kemRowInstrs k key 2 ++
    kemRowInstrs k key 3 ++ kemFinishInstrs k key

/-! ## Scripts: step 8, the session -/

/-- `establish-session`'s public inputs: the request id (2^63, `uint 8`) and our registration id. -/
def requestId : B8 := be 8 (2 ^ 63)

/-- **Step 8** (`establish-session CERT ONETIME`): binds every input by the kernel's declared order
(`EstablishKernel.sessionInputs`); OPENS `status` (`deviceStatus`); keeps `conversation` (ids
`n+29`) and `pending` (`n+30`); frees the device's other handles. Uses ids `n … n+30`. -/
def sessionScript (n : Nat) (acct : Account) (registration : Nat) (parsed : Parsed) (bound kem : BoolH)
    (ag : List BoolH) (oneTime : Bool) : Script (Nat × Device) :=
  let fields := parsed.fields
  let conv := acct.cert + recordBytes
  let dh4 : List BoolH := if oneTime then [ag.getD 6 ⟨0⟩] else []
  seqs ([sliceOf n bound.id R_verified, sliceOf (n + 1) kem.id K_status, sliceOf (n + 2) kem.id K_secret,
         sliceOf (n + 3) kem.id K_ciphertext, sliceOf (n + 4) fields.id F_identityKey,
         sliceOf (n + 5) fields.id F_signedPrekey, sliceOf (n + 6) bound.id R_uuid,
         sliceOf (n + 7) bound.id R_accessKey, .boolPublic ⟨n + 8⟩ (bitsOf requestId),
         sliceOf (n + 9) fields.id F_deviceId, sliceOf (n + 10) fields.id F_registrationId,
         .boolPublic ⟨n + 11⟩ (bitsOf (be 4 registration))] ++
        (if oneTime then [sliceOf (n + 12) fields.id F_oneTimePrekeyId] else []) ++
        [sliceOf (n + 13) fields.id F_signedPrekeyId,
         sliceOf (n + 14) fields.id F_kyberPrekeyId,
         .concat ⟨n + 15⟩ ([⟨n⟩, ⟨n + 1⟩, ag.getD 0 ⟨0⟩, ag.getD 1 ⟨0⟩, ag.getD 2 ⟨0⟩] ++ dh4 ++
           [ag.getD 3 ⟨0⟩, ⟨n + 2⟩, ⟨n + 3⟩, ag.getD 4 ⟨0⟩, ag.getD 5 ⟨0⟩, acct.senderPublic, ⟨n + 4⟩, ⟨n + 5⟩,
            acct.certificate, ⟨n + 6⟩, ⟨n + 7⟩, ⟨n + 8⟩, ⟨n + 9⟩, ⟨n + 10⟩, ⟨n + 11⟩] ++
           (if oneTime then [⟨n + 12⟩] else []) ++ [⟨n + 13⟩, ⟨n + 14⟩]),
         .run ⟨n + 16⟩ (sessionName acct.cert oneTime) 1 ⟨n + 15⟩,
         .slice ⟨n + 17⟩ ⟨n + 16⟩ 0 8,
         .slice ⟨n + 29⟩ ⟨n + 16⟩ 8 (8 + 8 * conv),
         .slice ⟨n + 30⟩ ⟨n + 16⟩ (8 + 8 * conv) (8 + 8 * conv + 8 * pendingBytes)] ++
        frees ((((List.range 17).filter fun j => j != 12 || oneTime).map fun j => ⟨n + j⟩) ++
          parsed.handles ++ [bound, kem] ++ ag))
    (openThen ⟨n + 17⟩ Label.deviceStatus fun s =>
      seqs [.freeBool ⟨n + 17⟩]
        (.done ((bytesOf s).headD 0 |>.toNat, ⟨⟨n + 29⟩, ⟨n + 30⟩, oneTime⟩)))

/-! ## Scripts: the scratch -/

/-- A device's stored part: its record (the conversation without the certificate) ‖ pending. -/
def contentParts (n cert : Nat) (ds : List Device) : List Instr × List BoolH :=
  let slices := ds.zipIdx.map fun (d, i) => (InstrP.slice ⟨n + i⟩ d.conversation (8 * cert) (8 * (cert + recordBytes)))
  (slices, (ds.zipIdx.map fun (d, i) => [(⟨n + i⟩ : BoolH), d.pending]).flatten)

/-- **The scratch's content** (the C++ `entries`: per device record ‖ pending) as ONE handle `n + 6`
(at most 6 devices: ids `n … n+6`), then its seal under `version` (`Contacts.sealScript`, ids
`n+7 … n+9`, `sealedBlob`). Returns the content handle (kept) and check ‖ ciphertext. -/
def scratchSealScript (n : Nat) (key : BoolH) (cert : Nat) (ds : List Device) (version : B8) :
    Script (BoolH × B8) :=
  let (slices, parts) := contentParts n cert ds
  seqs (slices ++ [.concat ⟨n + 6⟩ parts] ++ frees ((List.range ds.length).map fun i => ⟨n + i⟩))
    ((sealScript (n + 7) key ⟨n + 6⟩ (deviceContent * ds.length) version).bind fun r => .done (⟨n + 6⟩, r))


/-! ## The state's handles -/

def Progress.handles (p : Progress) : List BoolH :=
  ((p.parsed.map Parsed.handles).getD []) ++ p.bound.toList ++ p.agreements ++ p.kemHeld

/-- Every handle the scratch holds (body, lift, the device in progress, the established devices),
the sealed content excepted. -/
def RState.scratchHandles (st : RState) : List BoolH :=
  (st.body.map (·.1)).toList ++ ((st.lifted.map Lifted.handles).getD []) ++
    ((st.progress.map Progress.handles).getD []) ++ (st.done.map Device.handles).flatten

/-- Every handle the refresh state holds. -/
def RState.handles (st : RState) : List BoolH := st.scratchHandles ++ (st.sealed.map (fun s => s.1)).toList

/-! ## The operations on the contact table and the refresh state

Each is a script and the (table, refresh state) it leaves once the script returned. The contact
table's ENTRIES change in `opCommit` only (ORD-2, `RefreshFlowProofs.lean`). -/

/-- An operation of the refresh. -/
structure RStep (α : Type) where
  script : Script α
  commit : α → Contacts.Table × RState

/-- **Op 57.** -/
def opTake (t : Contacts.Table) (st : RState) (content : BoolH) (offset count : Nat) : RStep BoolH :=
  let held := (st.body.map (·.2)).getD 0
  if 0 < count ∧ held + count ≤ maxBody ∧ st.sealed = none then
    { script := takeScript (t.alloc 2).1 (st.body.map (·.1)) content offset count
      commit := fun h => ((t.alloc 2).2, { st with body := some (h, held + count) }) }
  else { script := .abort "bundle take", commit := fun _ => (t, st) }

/-- **Op 58.** Frees the body and the scratch; the contact table is unchanged. -/
def opDrop (t : Contacts.Table) (st : RState) : RStep Unit :=
  { script := seqs (frees st.handles) (.done ()), commit := fun _ => (t, {}) }

/-- **Op 59.** `none` when the size class has no circuit (strict manifest: `loaded` is false). -/
def opShape (t : Contacts.Table) (st : RState) (loaded : Bytes → Bool) : RStep (Option (List Bool)) :=
  match st.body with
  | some (b, size) =>
    if minBody ≤ size ∧ loaded (shapeName (shapeCapacity size)) = true then
      { script := (shapeScript (t.alloc 3).1 b size).bind (fun f => .done (some f))
        commit := fun _ => ((t.alloc 3).2, st) }
    else if minBody ≤ size then { script := .done none, commit := fun _ => (t, st) }
    else { script := .abort "bundle shape", commit := fun _ => (t, st) }
  | none => { script := .abort "bundle shape", commit := fun _ => (t, st) }

/-- **Op 56 (with the record seal's first phase).** Needs the contact's state. -/
def opFetch (t : Contacts.Table) (st : RState) (id : Nat) (traffic : BoolH) (seq frame mask : B8)
    (payloadAt uuidAt keyAt : Nat) : RStep (B8 × BoolH) :=
  match t.find? id with
  | some e =>
    match e.state with
    | some s =>
      if mask.length = 4 ∧ 0 < frame.length then
        { script := fetchScript (t.alloc 7).1 traffic s seq frame mask payloadAt uuidAt keyAt
          commit := fun _ => ((t.alloc 7).2, st) }
      else { script := .abort "bundle fetch unavailable", commit := fun _ => (t, st) }
    | none => { script := .abort "bundle fetch unavailable", commit := fun _ => (t, st) }
  | none => { script := .abort "bundle fetch unavailable", commit := fun _ => (t, st) }

/-- **Op 64.** Needs the contact's key and a complete scratch for it. -/
def opScratchSeal (t : Contacts.Table) (st : RState) (id : Nat) (cert : Nat) (version : B8) :
    RStep (BoolH × B8) :=
  match t.find? id, st.contact with
  | some e, some c =>
    match e.key with
    | some k =>
      if st.ready = true ∧ c = id ∧ st.done ≠ [] ∧ st.done.length ≤ 6 ∧ st.sealed = none then
        { script := scratchSealScript (t.alloc 10).1 k cert st.done version
          commit := fun r => ((t.alloc 10).2,
            { st with sealed := some (r.1, deviceContent * st.done.length, st.done.map Device.kind) }) }
      else { script := .abort "scratch seal unavailable", commit := fun _ => (t, st) }
    | none => { script := .abort "scratch seal unavailable", commit := fun _ => (t, st) }
  | _, _ => { script := .abort "scratch seal unavailable", commit := fun _ => (t, st) }

/-- **Op 65: the ONLY change of a contact's entry by the refresh.** Once the database nodes
acknowledged the sealed scratch (the caller's precondition: ORD-2), the contact's state becomes the
sealed content; its old state is freed, and with a new identity key also the values derived from
the old one (`derived`: the C++ recipient point, static agreement, offset table). The scratch's
other handles are freed; the refresh state is emptied. -/
def opCommit (t : Contacts.Table) (st : RState) (id : Nat) : RStep Unit :=
  match t.find? id, st.contact, st.sealed with
  | some e, some c, some (content, size, kinds) =>
    if st.ready = true ∧ c = id then
      { script := seqs (frees (e.state.toList ++ (if st.changed then e.derived else []) ++ st.scratchHandles))
          (.done ())
        commit := fun _ =>
          let e' : Contacts.Entry := { e with state := some content, size := size, kinds := kinds }
          (t.put id { e' with derived := if st.changed then [] else e.derived }, {}) }
    else { script := .abort "scratch commit unavailable", commit := fun _ => (t, st) }
  | _, _, _ => { script := .abort "scratch commit unavailable", commit := fun _ => (t, st) }

/-! ## The establishment (op 60), step by step -/

/-- What one step replies (the C++ status byte): 255 done, 254 (step 0 of device 0) the identity
key is a new one, 0 refused (the refresh state is dropped), or the session's opened status after
step 8. -/
abbrev Status := Nat

/-- An S11 parameter's blocks (Boolean and field ids) from the table's counters. -/
def allocBoth (t : Contacts.Table) (ids : Nat × Nat) : Counters × Contacts.Table :=
  (t.ctr, { t with ctr := { bool := t.ctr.bool + ids.1, field := t.ctr.field + ids.2 } })

/-- A step's script and the table after its allocations; the script returns the status and the
refresh state after it. -/
abbrev Stepped := Script (Status × RState) × Contacts.Table

/-- A refusal (the C++ `Rejected`): everything the refresh state holds is freed; status 0. -/
def refuse (st : RState) : Script (Status × RState) := seqs (frees st.handles) (.done (0, {}))

/-- **Step 0 of device `index`** of `count`: parse, (device 0) lift, challenges, check, verify,
rebind. -/
def step0 (cv : CurveOps) (t : Contacts.Table) (st : RState) (id : Nat) (state body : BoolH) (total : Nat)
    (index count start : Nat) (w : Widths) : Stepped :=
  let first := index == 0
  let last := index + 1 == count
  let o := w.oneTime != 0
  let n0 := (t.alloc 14).1
  let t1 := (t.alloc 14).2
  let cLift := (allocBoth t1 cv.liftIds).1
  let t2 := (allocBoth t1 cv.liftIds).2
  let n1 := (t2.alloc 9).1
  let t3 := (t2.alloc 9).2
  let cCheck := (allocBoth t3 cv.checkIds).1
  let t4 := (allocBoth t3 cv.checkIds).2
  let n2 := (t4.alloc 10).1
  let t5 := (t4.alloc 10).2
  ((parseScript n0 body total start w first last).bind fun
      | none => refuse st
      | some p =>
        ((match st.lifted, first with
          | some l, false => Script.done l
          | _, _ => (cv.lift cLift p.identityPoint).bind fun r => Script.done (Lifted.mk r.1 r.2.1 r.2.2)) :
            Script Lifted).bind fun l =>
        (challengeScript n1 p.fields l).bind fun ch =>
        (cv.check cCheck l.x l.y ch.1 ch.2).bind fun r =>
        (seqs (frees [ch.1, ch.2]) (verifyScript n2 state p.fields l r first)).bind fun br =>
          let pg : Progress := { index := index, step := 1, oneTime := o, parsed := some p, bound := some br.1 }
          let st' : RState := { st with lifted := some l, changed := st.changed || br.2, contact := some id }
          .done (if br.2 then 254 else 255, { st' with progress := some pg }),
    t5)

/-- **Step 1**: S11's agreements (6, or 7 with a one-time prekey). -/
def step1 (cv : CurveOps) (t : Contacts.Table) (st : RState) (p : Progress) (pr : Parsed) : Stepped :=
  let c := (allocBoth t cv.agreeIds).1
  ((cv.agree c pr.identityPoint pr.signedPoint pr.oneTimePoint).bind fun ag =>
      if ag.length = (if p.oneTime then 7 else 6) then
        .done (255, { st with progress := some { p with step := 2, agreements := ag } })
      else .abort "bundle establish agreements",
    (allocBoth t cv.agreeIds).2)

/-- The KEM block's handles alive after step 2 (`k + 33`: the Kyber prekey's slice). -/
def kemAfterHash (k : Nat) : List BoolH := [⟨k + 3⟩, ⟨k + 4⟩, ⟨k + 5⟩, ⟨k + 6⟩, ⟨k + 7⟩, ⟨k + 8⟩, ⟨k + 33⟩]
/-- … and the handles a row adds. -/
def kemAfterRow (k r : Nat) : List BoolH := (List.range 5).map fun j => ⟨kemRow k r + j⟩

/-- **Step 2**: the Kyber prekey's slice, both entropies, `kem-hash`, `kem-ntt`. -/
def step2 (t : Contacts.Table) (st : RState) (p : Progress) (pr : Parsed) (slot : Nat) : Stepped :=
  let k := (t.alloc (kemIds + 1)).1
  (seqs ([sliceOf (k + 33) pr.fields.id F_kyberPrekey] ++ kemHashInstrs k ⟨k + 33⟩ slot)
      (.done (255, { st with progress := some { p with step := 3, kem := some k, kemHeld := kemAfterHash k } })),
    (t.alloc (kemIds + 1)).2)

/-- **Steps 3–6**: row `step − 3`. -/
def stepRow (st : RState) (p : Progress) (k : Nat) : Script (Status × RState) :=
  let pg : Progress := { p with step := p.step + 1, kemHeld := p.kemHeld ++ kemAfterRow k (p.step - 3) }
  seqs (kemRowInstrs k ⟨k + 33⟩ (p.step - 3)) (.done (255, { st with progress := some pg }))

/-- **Step 7**: `kem-v`, `kem-finish`; the block's temporaries and the key slice are freed. -/
def step7 (st : RState) (p : Progress) (k : Nat) : Script (Status × RState) :=
  seqs (kemFinishInstrs k ⟨k + 33⟩ ++ [.freeBool ⟨k + 33⟩])
    (.done (255, { st with progress := some { p with step := 8, kemHeld := [⟨k + 32⟩] } }))

/-- **Step 8**: the session; the device joins the scratch. After the last device the scratch is
complete (`ready`) exactly when every status opened 255. -/
def step8 (acct : Account) (t : Contacts.Table) (st : RState) (p : Progress) (pr : Parsed) (bound : BoolH)
    (k registration count : Nat) : Stepped :=
  let n := (t.alloc 31).1
  ((sessionScript n acct registration pr bound ⟨k + 32⟩ p.agreements p.oneTime).bind fun r =>
      let statuses := st.statuses ++ [r.1]
      let st' : RState := { st with progress := none, done := st.done ++ [r.2], statuses := statuses }
      .done (r.1, { st' with ready := decide (p.index + 1 = count) && statuses.all (· == 255) }),
    (t.alloc 31).2)

/-- **Op 60: one step of one device's establishment**, as the C++ `bundle_establish`: the steps of
device 0, then of device 1, …, in order (`need` failures abort the session; a refused item drops
the refresh state and replies 0). `slot`: this party's 32 random bytes for step 2 (its store slot). -/
def opEstablish (cv : CurveOps) (acct : Account) (t : Contacts.Table) (st : RState) (id registration index count step
    start : Nat) (w : Widths) (slot : Nat) : RStep (Status × RState) :=
  let stop : RStep (Status × RState) := { script := .abort "bundle establish", commit := fun _ => (t, st) }
  let run : Stepped → RStep (Status × RState) := fun s => { script := s.1, commit := fun r => (s.2, r.2) }
  match t.find? id, st.body with
  | some e, some (body, total) =>
    match e.state with
    | some state =>
      if 1 ≤ count ∧ count ≤ 6 ∧ index < count ∧ st.sealed = none ∧ st.ready = false ∧
          (st.contact = none ∨ st.contact = some id) then
        match step, st.progress with
        | 0, none =>
          if st.done.length = index ∧ (index = 0 → st.lifted = none ∧ st.statuses = []) then
            run (step0 cv t st id state body total index count start w)
          else stop
        | s + 1, some p =>
          if p.index = index ∧ p.step = s + 1 then
            match s + 1, p.parsed, p.bound, p.kem with
            | 1, some pr, _, _ => run (step1 cv t st p pr)
            | 2, some pr, _, _ => run (step2 t st p pr slot)
            | 8, some pr, some b, some k => run (step8 acct t st p pr b k registration count)
            | 7, _, _, some k => run (step7 st p k, t)
            | j, _, _, some k => if 3 ≤ j ∧ j ≤ 6 then run (stepRow st p k, t) else stop
            | _, _, _, _ => stop
          else stop
        | _, _ => stop
      else stop
    | none => stop
  | _, _ => stop

/-! ## The reveal list -/

def fetchKinds : List TlsMpc.Node.RevealKind := [.sealedRecord]
def shapeKinds : List TlsMpc.Node.RevealKind := [.bundleShape]
def scratchKinds : List TlsMpc.Node.RevealKind := [.sealedBlob]
/-- The kinds the establishment's own instructions release under (S11's parameter adds its own). -/
def establishKinds : List TlsMpc.Node.RevealKind := [.identityChanged, .deviceStatus]
/-- Everything a refresh may release under, with S11's kinds `ks`. -/
def refreshKinds (ks : List TlsMpc.Node.RevealKind) : List TlsMpc.Node.RevealKind :=
  [.sealedRecord, .bundleShape, .identityChanged, .deviceStatus, .sealedBlob] ++ ks

end TlsMpc.Node.Flows.Refresh
