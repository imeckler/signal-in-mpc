import Lean
import TlsMpc.CeremonyKernels

/-!
The registration ceremony's requests as text (`CEREMONY.md`). Everything here is public to both
nodes: the phone number, the captcha token, the SMS code, the verification session's id, and the
account's public registration material (the keys were generated in the clear). The two private
values, the password and the recovery password, are slots that only the engines fill
(`ceremony-register-ctr`); here they are the boundaries between the returned strings.

Each request goes over the chat WebSocket as a `WebSocketRequestMessage`; the controller frames
these strings (`PublicRequest.assemble`). The requests and field names are those of
`real_signal/register/src/main.rs` (libsignal's `RegistrationService`) and of
`local_signal_server/provision/src/main.rs` (`register_full`), which the local server accepts.
-/
namespace TlsMpc.Ceremony
open Lean (Json)

structure SignedKey where
  keyId : Nat
  publicKey : String
  signature : String

/-- The account's public registration material, as the key tool writes it (`registration` in
the keys file). Every string is base64 from that tool. -/
structure Registration where
  registrationId : Nat
  pniRegistrationId : Nat
  accessKey : String
  aciIdentity : String
  pniIdentity : String
  aciSigned : SignedKey
  pniSigned : SignedKey
  aciKyber : SignedKey
  pniKyber : SignedKey
  /-- One-time prekeys (id, public key), uploaded after registration. -/
  oneTime : List (Nat × String)

/-- Characters that may stand inside a JSON string or a request path here without escaping. -/
def plain (text : String) : Bool :=
  !text.isEmpty && text.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '=' || c == '+' || c == '/' || c == '.')

def phoneNumber (text : String) : Bool :=
  text.length ≥ 8 && text.length ≤ 16 && text.front == '+' && (text.drop 1).all Char.isDigit

def signedKey? (json : Json) : Except String SignedKey := do
  let key : SignedKey := { keyId := ← json.getObjValAs? Nat "keyId", publicKey := ← json.getObjValAs? String "publicKey",
                           signature := ← json.getObjValAs? String "signature" }
  unless plain key.publicKey && plain key.signature do throw "a signed key is not base64"
  pure key

def Registration.ofJson? (json : Json) : Except String Registration := do
  let text (name : String) : Except String String := do
    let value ← json.getObjValAs? String name
    unless plain value do throw s!"{name} is not base64"
    pure value
  let oneTime ← (← json.getObjValAs? (Array Json) "oneTime").toList.mapM fun entry => do
    let key ← entry.getObjValAs? String "publicKey"
    unless plain key do throw "a one-time prekey is not base64"
    pure (← entry.getObjValAs? Nat "keyId", key)
  pure { registrationId := ← json.getObjValAs? Nat "registrationId", pniRegistrationId := ← json.getObjValAs? Nat "pniRegistrationId",
         accessKey := ← text "unidentifiedAccessKey", aciIdentity := ← text "aciIdentityKey", pniIdentity := ← text "pniIdentityKey",
         aciSigned := ← signedKey? (← json.getObjVal? "aciSignedPreKey"), pniSigned := ← signedKey? (← json.getObjVal? "pniSignedPreKey"),
         aciKyber := ← signedKey? (← json.getObjVal? "aciPqLastResortPreKey"),
         pniKyber := ← signedKey? (← json.getObjVal? "pniPqLastResortPreKey"), oneTime }

def signedJson (key : SignedKey) : String :=
  "{\"keyId\":" ++ toString key.keyId ++ ",\"publicKey\":\"" ++ key.publicKey ++ "\",\"signature\":\"" ++ key.signature ++ "\"}"

/-- `POST /v1/verification/session`. -/
def sessionBody (number : String) : String := "{\"number\":\"" ++ number ++ "\"}"
/-- `PATCH /v1/verification/session/{id}`. -/
def captchaBody (captcha : String) : String := "{\"captcha\":\"" ++ captcha ++ "\"}"
/-- `POST /v1/verification/session/{id}/code`. -/
def requestCodeBody (client : String) : String := "{\"transport\":\"sms\",\"client\":\"" ++ client ++ "\"}"
/-- `PUT /v1/verification/session/{id}/code`. -/
def submitCodeBody (code : String) : String := "{\"code\":\"" ++ code ++ "\"}"

/-- `POST /v1/registration`: the body before and after the recovery password's slot (44
characters of base64). The account fetches its messages, accepts sealed sender from anyone
(new users do not know its profile key) and is not discoverable by phone number. -/
def registrationBody (session : String) (r : Registration) : String × String :=
  ("{\"sessionId\":\"" ++ session ++ "\",\"accountAttributes\":{\"fetchesMessages\":true,\"registrationId\":" ++
      toString r.registrationId ++ ",\"pniRegistrationId\":" ++ toString r.pniRegistrationId ++
      ",\"capabilities\":{\"spqr\":true},\"unidentifiedAccessKey\":\"" ++ r.accessKey ++
      "\",\"unrestrictedUnidentifiedAccess\":true,\"discoverableByPhoneNumber\":false,\"recoveryPassword\":\"",
   "\"},\"skipDeviceTransfer\":true,\"aciIdentityKey\":\"" ++ r.aciIdentity ++ "\",\"pniIdentityKey\":\"" ++ r.pniIdentity ++
      "\",\"aciSignedPreKey\":" ++ signedJson r.aciSigned ++ ",\"pniSignedPreKey\":" ++ signedJson r.pniSigned ++
      ",\"aciPqLastResortPreKey\":" ++ signedJson r.aciKyber ++ ",\"pniPqLastResortPreKey\":" ++ signedJson r.pniKyber ++ "}")

/-- `PUT /v2/keys?identity=aci`: the one-time prekeys. -/
def oneTimeBody (r : Registration) : String :=
  "{\"preKeys\":[" ++ ",".intercalate (r.oneTime.map fun (id, key) =>
    "{\"keyId\":" ++ toString id ++ ",\"publicKey\":\"" ++ key ++ "\"}") ++ "],\"pqPreKeys\":[]}"

def ascii (text : String) : List (BitVec 8) := text.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- The Basic credential is base64 of `NUMBER:PASSWORD`. Its whole three-byte groups before the
password are public: returned as base64 text, with the bytes left over (0 to 2), which the
engines encode together with the password. -/
def basic (number : String) : String × List (BitVec 8) :=
  let bytes := ascii (number ++ ":")
  let whole := bytes.length / 3 * 3
  (String.ofList ((Signal.RelayEncoding.base64 ByteAuth.concrete (bytes.take whole)).map (fun b => Char.ofNat b.toNat)),
    bytes.drop whole)

/-- The split of `basic` is the encoding of the whole credential: checked by the controllers on
the number in use, with a stand-in password, before the request is built. -/
def basicConsistent (number : String) : Bool :=
  let (text, tail) := basic number
  let standIn := ascii "abcdefghijklmnopqrstuv"
  Signal.RelayEncoding.base64 ByteAuth.concrete (ascii (number ++ ":") ++ standIn) ==
    ascii text ++ Signal.RelayEncoding.base64 ByteAuth.concrete (tail ++ standIn)

end TlsMpc.Ceremony
