import TlsMpc.RecordClassKernels
import TlsMpc.BundleItemKernels
import TlsMpc.ReceiveKernels
open TlsMpc Signal

/-! The names of every kernel a deployment can ask for, from a description of the deployment
(`CIRCUIT_SHAPES.md` explains each family and setting; `scripts/produce_circuits.py` runs this,
produces the kernels and writes the manifest).

    circuit_inventory KEY=VALUE ...

prints one `kernel NAME [PARAMETERS]` line per kernel. Sizes are computed with the definitions
the kernels themselves use (`RecordClass.capacity`, the `ReceiveFirst` and `BundleResponse`
layout functions, the record sizes of `BundleKernel` and `EstablishKernel`), and a shape the
kernels' own acceptance tests would refuse is an error here. Two families are not printed
because their parameters are frame offsets computed by the controller from the size of an
envelope that a produced kernel declares: `signal-request-ctr` and `bundle-request-ctr`
(`public_service_controller request-shape`, which `produce_circuits.py` runs after the seal
kernels exist).

Settings (lists are comma separated; a tuple's parts are separated by `:`):

* `certificate` (244): bytes of OUR sender certificate. `password` (22): bytes of the socket password.
  `ceremony` (0): 1 also lists `ceremony-secrets` (the registration ceremony, CEREMONY.md).
* `client_certificate` (0): bytes of the TLS client certificate message (`tls-finish`).
* `handshake`: sizes of the server's encrypted handshake records (`tls-open-handshake`).
* `record_max`: the largest TLS record the server sends, in bytes; `seal_max`: the largest content
  sealed in a record of its own (upgrade request, replies, keepalives). `typed_records` (0): 1 also
  lists `tls-open-typed` and `tls-frame` for every record class.
* `sends`: `CLASS:COUNTER:PREVIOUS:EPOCH:INDEX` for each message size class and counter-width
  combination to cover (`signal-seal-built`, and `bundle-seal` when there are bundles).
* `devices` (1): the most devices a contact may have (sizes of stored device lists).
* `bundle_items`: `D/R/S/P/K` groups separated by `+`, each part a `.`-separated list of digit
  counts; every combination in a group is covered (`bundle-item`). `bundle_max`: the largest
  prekey response body, in bytes.
* Signups (a new user's first message; every combination is covered): `signup_certificates`
  (`BYTES:PRESENT:LENGTH` of the SENDER's certificate and its phone-number field, `PRESENT` 0 or
  255), `signup_hints`, `signup_one_time` (0: none), `signup_registration`, `signup_signed`,
  `signup_kyber`, `signup_counter`, `signup_previous` (varint widths), `signup_ciphertext`
  (bytes), `signup_addresses` (0 or 1), `signup_pq` (bytes of the post-quantum field's body),
  `signup_text` (bytes of the text: the signup token), `signup_jump`. -/

abbrev Settings := List (String × String)

def setting (s : Settings) (key fallback : String) : String := (s.lookup key).getD fallback

def numbers (text separator : String) : Except String (List Nat) :=
  (text.splitOn separator).filter (· != "") |>.mapM fun part =>
    match part.toNat? with
    | some n => pure n
    | none => throw s!"not a number: {part}"

def numberList (s : Settings) (key fallback : String) : Except String (List Nat) := numbers (setting s key fallback) ","

def number (s : Settings) (key fallback : String) : Except String Nat := do
  match ← numberList s key fallback with
  | [n] => pure n
  | _ => throw s!"{key} must be one number"

def tuples (s : Settings) (key fallback : String) (width : Nat) : Except String (List (List Nat)) :=
  ((setting s key fallback).splitOn ",").filter (· != "") |>.mapM fun part => do
    let values ← numbers part ":"
    unless values.length == width do throw s!"{key}: {part} must have {width} parts"
    pure values

def kernel (parts : List String) : String := " ".intercalate ("kernel" :: parts)
def named (name : String) (parameters : List Nat) : String := kernel (name :: parameters.map toString)

/-- The capacities of the ladder from `first` up to the class of `last`. -/
partial def ladder (first last : Nat) : List Nat :=
  let top := RecordClass.capacity last
  let rec go (c : Nat) (out : Array Nat) : Array Nat :=
    if c > top then out else go (RecordClass.capacity (c + 1)) (out.push c)
  (go (RecordClass.capacity first) #[]).toList

/-- All combinations, one element from each list. -/
def combinations : List (List Nat) → List (List Nat)
  | [] => [[]]
  | choices :: rest => choices.flatMap fun x => (combinations rest).map (x :: ·)

def always (s : Settings) : Except String (List String) := do
  let certificate ← number s "certificate" "244"
  let password ← number s "password" "22"
  let client ← number s "client_certificate" "0"
  let handshake ← numberList s "handshake" ""
  pure <| ["tls-derive", "tls-verify-finished", "tls-update", "tls-parser-initial", "ws-initial", "gcm-key-share",
      "gcm-multiply", "gcm-tag", "gcm-check", "contact-key"].map (kernel [·]) ++
    [named "tls-finish" [client], named "tls-seal-ctr" [22, 5, 0], named "tls-seal-ctr" [21, 2, 0],
      named "signal-upgrade" [password], named "signal-upgrade-shared" [password],
      named "signal-conversation-view" [certificate], named "signal-widths" [certificate]] ++
    handshake.map (named "tls-open-handshake" [·]) ++
    -- `ceremony=1`: the registration ceremony (CEREMONY.md). Its second kernel,
    -- `ceremony-register-ctr`, is not printed: its parameters are frame offsets the controller
    -- computes from the number, the verification session's id and the key ids.
    (if (← number s "ceremony" "0") == 0 then [] else [kernel ["ceremony-secrets"]])

def records (s : Settings) : Except String (List String) := do
  let opened := ladder 22 (← number s "record_max" "4096")
  let sealed := ladder 1 (← number s "seal_max" "512")
  -- The second way of opening records (`TlsMpc/TypedOpenKernels.lean`), in the same classes; off
  -- until a worker asks for them (`typed_records=1`).
  let typed := if (← number s "typed_records" "0") == 0 then [] else
    opened.flatMap fun c => [named "tls-open-typed" [c], named "tls-frame" [c]]
  pure <| opened.map (named "tls-open-application-class" [·]) ++ opened.map (fun c => named "tls-reveal-masked" [c - 21]) ++
    sealed.map (named "tls-seal-class" [·]) ++ typed

def stored (s : Settings) (bundles : Bool) : Except String (List String) := do
  let certificate ← number s "certificate" "244"
  let password ← number s "password" "22"
  let devices ← number s "devices" "1"
  let lists := if bundles then
      (List.range devices).flatMap fun d => (List.range (d + 2)).map fun pending =>
        BundleKernel.recordBytes * (d + 1) + EstablishKernel.pendingBytes * pending
    else []
  let sizes := ([BundleKernel.recordBytes, 32 + 16 + password + certificate] ++ lists).eraseDups
  pure <| sizes.flatMap fun size => [named "contact-seal" [size], named "contact-open" [size]]

def sends (s : Settings) (bundles : Bool) : Except String (List String) := do
  let certificate ← number s "certificate" "244"
  (← tuples s "sends" "1:1:1:1:1" 5).flatMapM fun row =>
    match row with
    | [size, counter, previous, epoch, index] => do
        unless 1 ≤ size && size ≤ 4 do throw "message size class"
        pure <| named "signal-seal-built" [certificate, size, counter, previous, epoch, index] ::
          (if bundles then [0, 1].map fun oneTime =>
            named "bundle-seal" [certificate, oneTime, PrivateTextNotification.paddedBytes size, counter, previous, epoch, index]
          else [])
    | _ => throw "sends"

def bundleWidths (s : Settings) : Except String (List BundleResponse.Widths) := do
  let groups := ((setting s "bundle_items" "").splitOn "+").filter (· != "")
  let all ← groups.flatMapM fun group => do
    let parts ← (group.splitOn "/").mapM (numbers · ".")
    unless parts.length == 5 do throw s!"bundle_items: {group} must have five parts"
    (combinations parts).mapM fun row =>
      match row with
      | [d, r, sg, p, k] =>
          let w : BundleResponse.Widths := ⟨d, r, sg, p, k⟩
          if w.ok then pure w else throw s!"bundle_items: widths {row} are out of range"
      | _ => throw "bundle_items"
  pure all.eraseDups

def bundles (s : Settings) : Except String (List String) := do
  let widths ← bundleWidths s
  if widths.isEmpty then return []
  let certificate ← number s "certificate" "244"
  let devices ← number s "devices" "1"
  let largest := BundleResponse.firstItem + 2 + devices * (1 + (widths.map fun w => BundleResponse.size (BundleResponse.item w)).foldl max 0)
  let bodies := ladder 2540 (← number s "bundle_max" (toString largest))
  let positions := [(true, true)] ++ (if devices ≥ 2 then [(true, false), (false, true)] else []) ++
    (if devices ≥ 3 then [(false, false)] else [])
  pure <| ["establish-challenges", "establish-verified", "bundle-rebind", "kem-ntt", "kem-v"].map (kernel [·]) ++
    [kernel ["kem-hash", "kyber"], kernel ["kem-finish", "kyber"]] ++
    (List.range 4).flatMap (fun row => [named "kem-matrix" [row], named "kem-u" [row]]) ++
    [0, 1].flatMap (fun oneTime => [named "establish-points" [oneTime], named "establish-session" [certificate, oneTime]]) ++
    bodies.map (named "bundle-shape" [·]) ++
    positions.flatMap fun (first, last) => widths.map fun w =>
      named "bundle-item" [first.toNat, last.toNat, w.device, w.registration, w.signed, w.oneTime, w.kyber]

/-- A length-delimited field with a body of `body` bytes: tag, length prefix, body. -/
def framedBytes (body : Nat) : Nat := 1 + ReceiveFirst.varintWidth body + body

/-- The kernels of one signup shape (the steps of `TlsMpc/ReceiveKernels.lean`). The sizes are
built up from the message's parts and then checked against the kernels' own arithmetic. -/
def signup (ours cert present length hint oneTime registration signed kyber counter previous ciphertext addresses pq
    jump : Nat) : Except String (List String) := do
  let p : ReceiveFirst.PreKeyShape := ⟨oneTime, registration, signed, kyber⟩
  let q : ReceiveFirst.SignalShape := ⟨counter, previous, ciphertext, addresses == 1⟩
  let hinted := if hint == 1 then 2 else 0
  let signal := q.cipherAt + ciphertext + 8 + (if addresses == 1 then 38 else 0) + framedBytes pq
  let message := p.keysAt + 70 + framedBytes signal + p.tail
  let content := 5 + cert + hinted + framedBytes message
  let envelope := 81 + framedBytes (content + 10)
  let low := cert % 128 + 128
  let high := cert / 128
  let (l0, l1) := if ciphertext < 128 then (ciphertext, 0) else (ciphertext % 128 + 128, ciphertext / 128)
  let shape := s!"certificate {cert}, hint {hint}, widths {oneTime} {registration} {signed} {kyber} {counter} {previous}, ciphertext {ciphertext}"
  unless ReceiveKernel.envelopeOk envelope && ReceiveKernel.contentBytes envelope == content &&
      ReceiveKernel.certLength low high == some cert && ReceiveKernel.contentOk content cert (hint == 1) &&
      ReceiveFirst.bodyOf (content - (5 + cert) - hinted) == message &&
      (ReceiveKernel.preKeyShape? message [oneTime, registration, signed, kyber]).isSome &&
      p.signalSize message == signal &&
      (ReceiveKernel.signalShape? signal [counter, previous, l0, l1, addresses]).isSome &&
      ReceiveFirst.bodyOf (q.pqField signal) == pq && hint ≤ 1 && addresses ≤ 1 && jump ≤ 16 &&
      ((present == 0 && length == 0) || (present == 255 && 0 < length && length < 128)) &&
      (ReceiveFirst.certShape cert (if present == 255 then 2 + length else 0)).isSome do
    throw s!"signup shape is not one the receive kernels accept: {shape}"
  pure [named "receive-envelope-point" [envelope], named "receive-unseal-static" [envelope],
    named "receive-unseal-message" [envelope], named "receive-content-shape" [content, low, high],
    named "receive-content" [content, low, high, hint], named "receive-certificate" [low, high, present, length],
    named "receive-prekey-shape" [message], named "receive-prekey-open" [message, oneTime, registration, signed, kyber],
    named "receive-signal-shape" [message, oneTime, registration, signed, kyber],
    named "receive-session" [ours, message, oneTime, registration, signed, kyber, counter, previous, l0, l1, addresses, jump]]

def signups (s : Settings) : Except String (List String) := do
  let certificates ← tuples s "signup_certificates" "" 3
  if certificates.isEmpty then return []
  let ours ← number s "certificate" "244"
  let ciphertexts ← numberList s "signup_ciphertext" "176"
  let text ← number s "signup_text" "108"
  let choices ← ["signup_hints", "signup_one_time", "signup_registration", "signup_signed", "signup_kyber",
      "signup_counter", "signup_previous", "signup_addresses", "signup_pq", "signup_jump"].zip
      ["0", "0,1", "1,2", "1", "1", "1", "1", "1", "37", "0"] |>.mapM fun (key, fallback) => numberList s key fallback
  let chains ← certificates.flatMapM fun certificate => ciphertexts.flatMapM fun ciphertext =>
    (combinations choices).flatMapM fun row =>
      match certificate, row with
      | [cert, present, length], [hint, oneTime, registration, signed, kyber, counter, previous, addresses, pq, jump] =>
          signup ours cert present length hint oneTime registration signed kyber counter previous ciphertext addresses pq jump
      | _, _ => throw "signup settings"
  -- The text and the access key: the text's start in the content is 4, 5 or 6 (two length prefixes).
  let texts := ciphertexts.flatMap fun ciphertext =>
    named "receive-text" [ciphertext, ciphertext - 6] ::
      ([4, 5, 6].filter (fun start => start + text + 34 ≤ ciphertext)).map
        (fun start => named "receive-access-key" [ours, ciphertext, start + text])
  pure <| kernel ["receive-certificate-verified"] :: chains ++ texts

def main (args : List String) : IO Unit := do
  let s : Settings := args.filterMap fun arg =>
    match arg.splitOn "=" with
    | [key, value] => some (key, value)
    | _ => none
  unless s.length == args.length do throw (IO.userError "circuit_inventory KEY=VALUE ...")
  let result : Except String (List String) := do
    let withBundles := !(← bundleWidths s).isEmpty
    pure ((← always s) ++ (← records s) ++ (← stored s withBundles) ++ (← sends s withBundles) ++ (← bundles s) ++ (← signups s))
  match result with
  | .error message => throw (IO.userError message)
  | .ok names => for name in names.eraseDups do IO.println name
