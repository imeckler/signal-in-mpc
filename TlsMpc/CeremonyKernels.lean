import TlsMpc.BundleKernels

/-!
The registration ceremony (`CEREMONY.md`): the account password and the registration recovery
password are produced inside the Boolean engine from one private contribution of each node, and
enter the registration request only there.

* `Ceremony.password`: the 22-character password. Each node enters 18 private bytes; the password
  is the first 22 characters of the standard base64 of their XOR (132 bits; characters of
  `A–Z a–z 0–9 + /`, so never a `:`, which would end the user name of a Basic credential).
* `Ceremony.secrets`: that password, the recovery password (32 bytes, the XOR of the nodes' two
  private values), and the one opened value: the password XOR a private mask of each node. With
  it the nodes hold XOR shares of the password (`mask_A ⊕ masked` and `mask_B`), the form the
  stored credentials already have (`service_kernels.h`, `account_credentials`).
* `Ceremony.fill`: a WebSocket frame built in the clear with zero bytes in its slots, with the
  private values written into the slots under the frame's public mask.
* `ceremony-register-ctr`: `POST /v1/registration`. Slot 1 (32 characters) is the end of the
  Basic credential: base64 of the last `tail` bytes of `NUMBER:` (public; what is left after
  whole base64 groups), then the password. Slot 2 (44 characters) is base64 of the recovery
  password, in the JSON body. The record is encrypted without its tag, as by
  `BundleKernel.sealSlots` (`gcm-tag` adds it).

The theorems are in `TlsMpc/CeremonyProofs.lean`.
-/
namespace TlsMpc.Ceremony
open Signal

def passwordBytes : Nat := 22
/-- Each node's private contribution to the password. Base64 of 18 bytes is 24 characters. -/
def seedBytes : Nat := 18
def recoveryBytes : Nat := 32

def password (a : ByteAuth.Ops B) (seedA seedB : List B) : List B :=
  (RelayEncoding.base64 a (List.zipWith a.xor seedA seedB)).take passwordBytes

/-- `[password, recovery password, masked password]`; only the third is opened. -/
def secrets (a : ByteAuth.Ops B) (seedA seedB maskA maskB recoveryA recoveryB : List B) : List (List B) :=
  let word := password a seedA seedB
  [word, List.zipWith a.xor recoveryA recoveryB, List.zipWith a.xor word (List.zipWith a.xor maskA maskB)]

/-- The slot value covering frame index `index`, if any. -/
def slotAt (zero : B) (slots : List (Nat × List B)) (index : Nat) : Option B :=
  slots.findSome? (fun slot =>
    if slot.1 ≤ index && index < slot.1 + slot.2.length then some (slot.2.getD (index - slot.1) zero) else none)

/-- The frame with its slots filled. The frame's bytes are already masked, with zero bytes in the
slots; the WebSocket payload starts at `payloadAt`, so frame index `i` has mask byte
`mask[(i - payloadAt) % 4]`. -/
def fill (a : ByteAuth.Ops B) (frame mask : List B) (payloadAt : Nat) (slots : List (Nat × List B)) : List B :=
  frame.zipIdx.map (fun pair => match slotAt (a.const 0) slots pair.2 with
    | some secret => a.xor pair.1 (a.xor secret (mask.getD ((pair.2 - payloadAt) % 4) (a.const 0)))
    | none => pair.1)

/-- The two private slots of the registration request, from `secrets` = the public tail of
`NUMBER:` (`tail` bytes), the password, the recovery password. -/
def registerSlots (a : ByteAuth.Ops B) (secrets : List B) (tail authAt recoveryAt : Nat) : List (Nat × List B) :=
  [(authAt, RelayEncoding.base64 a (secrets.take (tail + passwordBytes))),
   (recoveryAt, RelayEncoding.base64 a ((secrets.drop (tail + passwordBytes)).take recoveryBytes))]

end TlsMpc.Ceremony

namespace TlsMpc.CeremonyKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup pub priv sl)

def secretsInputs : List (String × Shape) :=
  [("seedA", Shape.bytes Ceremony.seedBytes), ("seedB", .bytes Ceremony.seedBytes),
    ("maskA", .bytes Ceremony.passwordBytes), ("maskB", .bytes Ceremony.passwordBytes),
    ("recoveryA", .bytes Ceremony.recoveryBytes), ("recoveryB", .bytes Ceremony.recoveryBytes)]

/-- Opens `masked` only. `password` and `recovery` stay in the engine. -/
def ceremonySecrets (_ : Unit := ()) : Kernel :=   -- a function: a constant kernel would be built at program start
  let get := lookup secretsInputs
  let out := Ceremony.secrets ByteAuth.symbolic (get "seedA") (get "seedB") (get "maskA") (get "maskB")
    (get "recoveryA") (get "recoveryB")
  { name := "ceremony-secrets", inputs := secretsInputs, outputs := [
      priv "password" (out.getD 0 []), priv "recovery" (out.getD 1 []), pub "masked" (out.getD 2 [])] }

def registerInputs (size tail : Nat) : List (String × Shape) :=
  BundleKernel.requestInputs ("secrets", Shape.bytes (tail + Ceremony.passwordBytes + Ceremony.recoveryBytes)) size

/-- The registration request's plaintext: the frame with the two private slots filled. -/
def registerPlaintext (size payloadAt authAt tail recoveryAt : Nat) : List (BVExpr 8) :=
  let get := lookup (registerInputs size tail)
  Ceremony.fill ByteAuth.symbolic (get "frame") (get "mask") payloadAt
    (Ceremony.registerSlots ByteAuth.symbolic (get "secrets") tail authAt recoveryAt)

/-- Opens the encrypted record (and its header); the plaintext is never an output. -/
def ceremonyRegisterCtr (size payloadAt authAt tail recoveryAt : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := registerInputs size tail
  let get := lookup inputs
  let block := get "clientApplication"
  let inner := TlsRecord.inner g (registerPlaintext size payloadAt authAt tail recoveryAt) 23 0
  let ciphertext := Gcm.ctr g (HybridKernel.gcmExpanded block) (TlsRecord.nonce g (HybridKernel.blockIv block) (get "sequence")) inner
  { name := "ceremony-register-ctr", inputs, outputs := [
      pub "accepted" [a.const 255], pub "header" (TlsRecord.header g (inner.length + 16)),
      pub "ciphertext" (ByteAuth.release a (a.const 255) ciphertext),
      priv "pad" (HybridKernel.gcmPad block (get "sequence"))] }

set_option compiler.extract_closed false in   -- or `ceremonySecrets ()` would be built at program start
/-- `ceremony-secrets`; `ceremony-register-ctr SIZE PAYLOAD AUTH TAIL RECOVERY` (frame size, where
the WebSocket payload starts, the offset of the credential slot, how many public bytes precede the
password in it, the offset of the recovery-password slot). -/
def find (arguments : List String) : Option Kernel :=
  match arguments with
  | [] => none
  | name :: rest =>
      match name, rest.mapM (·.toNat?) with
      | "ceremony-secrets", some [] => some (ceremonySecrets ())
      | "ceremony-register-ctr", some [size, payloadAt, authAt, tail, recoveryAt] =>
          if size ≤ 16384 && 6 ≤ payloadAt && tail ≤ 2 &&
              BundleKernel.slotsOk size payloadAt [(authAt, 32), (recoveryAt, 44)] then
            some (ceremonyRegisterCtr size payloadAt authAt tail recoveryAt) else none
      | _, _ => none

end TlsMpc.CeremonyKernel
