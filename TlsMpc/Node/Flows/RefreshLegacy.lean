import TlsMpc.Signal.BundleResponse
import TlsMpc.Signal.BundleSlots
import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Refresh`, legacy implementation (worker ops 56-60, 64, 65)

Plan 6.2: `Refresh.fetch/take/drop/shape/establish/scratchSeal/scratchCommit` move to Lean scripts
in S15. A contact whose device list changed: fetch its devices' prekey bundles (the request names
the contact in the engines), collect the response body unopened, open only its punctuation shape,
establish a session per device as SCRATCH, and make the scratch the contact's state only once the
database nodes stored it.
-/

namespace TlsMpc.Node.Flow.Refresh
open TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal

/-- **The prekey fetch's request into the engines** (op 56): the frame built in the clear, masked
with `mask`; the contact's UUID and access key are inserted at its slots. The reply is the
request's buffer handle, to seal and send. -/
def fetch (w : Worker) (contact : ContactId) (payloadAt : Nat) (offsets : List Nat) (mask frame : Bytes) :
    M TlsWorker.BufferHandle := do
  if let some f := w.overrides.refreshFetch then
    Legacy.note w 56
    return ← f contact payloadAt offsets mask frame
  Legacy.handle (← Legacy.call w .bundleFetch (uint 16 contact ++ uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++
      uint 2 (offsets.getD 1 0) ++ mask ++ frame))
    "invalid request handle"

/-- **Collect `count` bytes of an authenticated record from `offset` into the held prekey response,
unopened** (op 57). -/
def take (w : Worker) (handle offset count : Nat) : M Unit := do
  if let some f := w.overrides.refreshTake then
    Legacy.note w 57
    return ← f handle offset count
  let held ← Legacy.call w .bundleTake (uint 8 handle ++ uint 2 offset ++ uint 2 count)
  insist (held.length == 4) "invalid bundle reply"

/-- **Discard the held response and any scratch device list** (op 58). -/
def drop (w : Worker) : M Unit := do
  if let some f := w.overrides.refreshDrop then
    Legacy.note w 58
    return ← f
  Legacy.empty w .bundleDrop []

/-- **The held response's shape** (op 59): per byte, whether it is JSON punctuation. `none` in
strict mode when no circuit covers the response's size class. -/
def shape (w : Worker) : M (Option (Opened .bundleShape (List Bool))) := do
  if let some f := w.overrides.refreshShape then
    Legacy.note w 59
    return ← f
  let flags ← Legacy.call w .bundleShape []
  if flags.isEmpty then return none
  insist (flags.all (fun b => b == 0 || b == 255)) "invalid bundle shape"
  pure (some (Reveal.bundleShape (flags.map (· == 255))))

/-- The end of operation 60's argument for an item with digit counts `w`: the counts, and with
`slots` (`SIGNAL_BUNDLE_SLOTS`, on unless `0`) the splice that turns the item into the fixed-width
layout of `bundle-slot` (`BundleSlots.splice`: a count, then per run zeros 1 byte, copy 2 bytes),
so that one circuit serves every digit count (CIRCUIT_SHAPES.md). -/
def establishTail (slots : Bool) (w : BundleResponse.Widths) : List UInt8 :=
  [w.device, w.registration, w.signed, w.oneTime, w.kyber].map UInt8.ofNat ++
    (if slots then
      let runs := BundleSlots.splice w
      UInt8.ofNat runs.length :: runs.flatMap fun (zeros, copy) => [UInt8.ofNat zeros, UInt8.ofNat (copy / 256), UInt8.ofNat (copy % 256)]
    else [])

/-- **One step of one device's session establishment** (op 60) into the scratch device list:
device `index` of `devices`, step `step` of 9, its item at `at_` with digit counts `widths`; our
registration id and the request counter's start. One status byte: 255 done, 254 (first step of
the first device) the bundle's identity key is a new one, anything else refused. -/
def establish (w : Worker) (contact : ContactId) (registration index devices step at_ : Nat) (slots : Bool)
    (widths : BundleResponse.Widths) : M (Opened .deviceStatus Bytes) := do
  if let some f := w.overrides.refreshEstablish then
    Legacy.note w 60
    return ← f contact registration index devices step at_ slots widths
  let out ← Legacy.call w .bundleEstablish (uint 16 contact ++ uint 8 (2 ^ 63) ++ uint 4 registration ++
    [UInt8.ofNat index, UInt8.ofNat devices, UInt8.ofNat step] ++ uint 4 at_ ++ establishTail slots widths)
  pure (Reveal.deviceStatus out)

/-- **Seal the scratch device list under the nonce `version`** (op 64): `check ‖ ciphertext`. -/
def scratchSeal (w : Worker) (contact : ContactId) (version : Bytes) : M (Opened .sealedBlob Bytes) := do
  if let some f := w.overrides.refreshScratchSeal then
    Legacy.note w 64
    return ← f contact version
  let stored ← Legacy.call w .scratchSeal (uint 16 contact ++ version)
  insist (stored.length > 16) "invalid sealed device list"
  pure (Reveal.sealedBlob stored)

/-- **Make the scratch device list the contact's state** (op 65), once the database nodes stored it. -/
def scratchCommit (w : Worker) (contact : ContactId) : M Unit := do
  if let some f := w.overrides.refreshScratchCommit then
    Legacy.note w 65
    return ← f contact
  Legacy.empty w .scratchCommit (uint 16 contact)

end TlsMpc.Node.Flow.Refresh
