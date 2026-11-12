import Lean.Data.Json
import TlsMpc.TlsWire
import TlsMpc.Node.Bytes
import TlsMpc.Node.Secret

/-!
# Parsers of the exported account state (pure)

Moved unchanged from the controller (`handshake_backend/EmpHybridWork/PublicServiceController.lean`)
in REORGANIZATION_PLAN.md stage S2; they were `private` there, and the controller opens this
namespace and uses the same names. They parse the text of the file written by
`lss-provision export-mpc` (or by the registration ceremony); reading the file stays in the
controller. Since stage S4 the keys and records they return are `Secret` (plan 4.2 rows 5, 6): our
identity key, our prekey private keys, and the TEST contact records. No emitter imports this
module.
-/

namespace TlsMpc.Node.Export
open TlsMpc.TlsWire TlsMpc.Node.Bytes TlsMpc.Node

/-- TEST state for a run against the local Signal server: the file written by
`lss-provision export-mpc` (local_signal_server/). Returns the sender's
certificate (public) and identity key (OWN, `Secret`) and, per contact, its id and record without
the certificate (session block ++ metadata; TEST, `Secret`). -/
def readExport (text : String) : Except String (Bytes × Secret Bytes × List (Nat × Secret Bytes)) := do
  let json ← Lean.Json.parse text
  let sender ← json.getObjVal? "sender"
  let certificate ← fromHex (← sender.getObjValAs? String "certificate_hex")
  let identity ← fromHex (← sender.getObjValAs? String "identity_private_hex")
  let contacts ← json.getObjValAs? (Array Lean.Json) "contacts"
  let records ← contacts.toList.mapM (fun contact => do
    let id ← fromHex (← contact.getObjValAs? String "contact_id_u128_hex")
    let session ← fromHex (← contact.getObjValAs? String "session_block_hex")
    let metadata ← fromHex (← contact.getObjValAs? String "metadata_hex")
    unless id.length == 16 && session.length == 262 && metadata.length == 57 do throw "export contact shape"
    pure (number id, Secret.hide (session ++ metadata)))
  -- No contacts is allowed: an account exported from its registration (real_signal/, a real
  -- account has no pre-established contacts; they arrive by signup and live on the database nodes).
  unless identity.length == 32 && 0 < certificate.length && certificate.length ≤ 1024 do
    throw "export shape"
  pure (certificate, Secret.hide identity, records)

/-- Our own address (account id, device id 1) and registration id, for sessions the client
starts itself (a contact's new device). Both are public to the two parties. -/
def readSelf (text : String) : Except String (Bytes × Nat) := do
  let json ← Lean.Json.parse text
  let sender ← json.getObjVal? "sender"
  let account ← fromHex (← sender.getObjValAs? String "aci_hex")
  unless account.length == 16 do throw "export sender shape"
  pure (account ++ [1], (sender.getObjValAs? Nat "registration_id").toOption.getD 0)

/-- What receiving a new contact's first message needs besides the shared
identity key: our public identity key and address, OUR prekey private keys by
id (OWN: held in the clear by both parties, and `Secret` so that they reach no log,
record or argv), and the server certificate that signs sender certificates
(validated against the trust root by the export tool). -/
structure ReceiveKeys where
  identityPublic : Bytes
  address : Bytes
  serverKey : Bytes
  serverCertificate : Bytes
  serverId : Nat
  oneTime : List (Nat × Secret Bytes)
  signed : List (Nat × Secret Bytes)
  kyber : List (Nat × Secret Bytes)

def readReceive (text : String) : Except String ReceiveKeys := do
  let json ← Lean.Json.parse text
  let sender ← json.getObjVal? "sender"
  let server ← json.getObjVal? "sealed_sender_server"
  let keys (name : String) : Except String (List (Nat × Bytes)) := do
    (← sender.getObjValAs? (Array Lean.Json) name).toList.mapM (fun entry => do
      pure (← entry.getObjValAs? Nat "id", ← fromHex (← entry.getObjValAs? String "key_hex")))
  let hidden (entries : List (Nat × Bytes)) : List (Nat × Secret Bytes) :=
    entries.map fun (id, key) => (id, Secret.hide key)
  let identityPublic ← fromHex (← sender.getObjValAs? String "identity_public_hex")
  let account ← fromHex (← sender.getObjValAs? String "aci_hex")
  let serverKey ← fromHex (← server.getObjValAs? String "public_key_hex")
  let oneTime ← keys "one_time_prekeys"
  let signed ← keys "signed_prekeys"
  unless identityPublic.length == 32 && account.length == 16 && serverKey.length == 32 &&
      (oneTime ++ signed).all (fun entry => entry.2.length == 32) do throw "export receive shape"
  pure { identityPublic, address := account ++ [1], serverKey
         serverCertificate := ← fromHex (← server.getObjValAs? String "certificate_hex")
         serverId := ← server.getObjValAs? Nat "key_id", oneTime := hidden oneTime, signed := hidden signed
         kyber := hidden (← keys "kyber_prekeys") }

end TlsMpc.Node.Export
