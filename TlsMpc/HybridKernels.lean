import TlsMpc.HybridKdf
import TlsMpc.HybridService

/-!
Worker kernels: one circuit per worker operation, with NAMED input and output
fields. All composition lives here: which bytes of a traffic block are the key,
how a send's inputs are assembled from retained state, how the next state is
selected, which queue slot a control reply reads, and which outputs may be
opened. The runtime binds wires to field names and has no layout knowledge.

An output marked `opened` is the only kind the runtime will open. Everything
else stays private and can only be passed back into another kernel by name.

Input shapes: `.bytes n` is `n` byte variables; `.word` is one 255-bit variable
(a field element exactly as the field-to-Boolean conversion delivers it), seen
by the body as its 32 little-endian bytes. An output may expose only its first
`bits` bits (used to hand a 255-bit word to the Boolean-to-field conversion).

No theorem is stated about a kernel as a whole; the parts carry the refinement
theorems of their modules.
-/
namespace TlsMpc.HybridKernel
open Std.Tactic.BVDecide
open Signal

inductive Shape where
  | bytes (count : Nat)
  | word

def Shape.bits : Shape → Nat
  | .bytes n => 8 * n
  | .word => 255

def Shape.variables : Shape → Nat
  | .bytes n => n
  | .word => 1

structure Output where
  name : String
  bits : Nat
  opened : Bool
  value : List (BVExpr 8)

structure Kernel where
  name : String
  inputs : List (String × Shape)
  outputs : List Output

def lookupFrom (name : String) : List (String × Shape) → Nat → List (BVExpr 8)
  | [], _ => []
  | (field, shape) :: rest, start =>
      if field == name then
        match shape with
        | .bytes count => ByteCircuit.inputBytes start count
        | .word => HybridKdf.wordBytes (.var start)
      else lookupFrom name rest (start + shape.variables)

def lookup (inputs : List (String × Shape)) (name : String) : List (BVExpr 8) := lookupFrom name inputs 0

def priv (name : String) (value : List (BVExpr 8)) : Output := ⟨name, 8 * value.length, false, value⟩
def pub (name : String) (value : List (BVExpr 8)) : Output := ⟨name, 8 * value.length, true, value⟩
def sl (bytes : List (BVExpr 8)) (start count : Nat) : List (BVExpr 8) := (bytes.drop start).take count
def const (n : Nat) : BVExpr 8 := .const (BitVec.ofNat 8 n)
def zeros (count : Nat) : List (BVExpr 8) := List.replicate count (const 0)

/-! Traffic block: secret (32), key (16), iv (12). -/
def blockSecret (block : List (BVExpr 8)) := sl block 0 32
def blockKey (block : List (BVExpr 8)) := sl block 32 16
def blockIv (block : List (BVExpr 8)) := sl block 48 12

/-! ### TLS -/

def tlsDerive : Kernel :=
  let inputs := [("agreement", Shape.word), ("helloHash", .bytes 32)]
  let get := lookup inputs
  let secrets := TlsKdf.handshakeSecretsFast Sha256.symbolic (get "agreement") (get "helloHash")
  { name := "tls-derive", inputs, outputs := [
      priv "clientHandshake" (HybridKdf.trafficBlock secrets.client),
      priv "serverHandshake" (HybridKdf.trafficBlock secrets.server),
      priv "mainSecret" secrets.main] }

/-- Opens authenticated handshake or alert content only. -/
def tlsOpenHandshake (size : Nat) : Kernel :=
  let inputs := [("serverHandshake", Shape.bytes 60), ("sequence", .bytes 8), ("record", .bytes size)]
  let get := lookup inputs
  let block := get "serverHandshake"
  { name := "tls-open-handshake", inputs, outputs := [
      pub "result" (TlsPublicHandshake.openCore Gcm.symbolic ByteAuth.symbolic (blockKey block) (blockIv block)
        (get "sequence") (get "record"))] }

def tlsVerifyFinished : Kernel :=
  let inputs := [("serverHandshake", Shape.bytes 60), ("transcriptHash", .bytes 32), ("message", .bytes 36)]
  let get := lookup inputs
  { name := "tls-verify-finished", inputs, outputs := [
      pub "accepted" [TlsHandshake.verifyHash Sha256.symbolic ByteAuth.symbolic (blockSecret (get "serverHandshake"))
        (get "transcriptHash") (get "message")]] }

def tlsFinish (certificateSize : Nat) : Kernel :=
  let inputs := [("mainSecret", Shape.bytes 32), ("serverHash", .bytes 32), ("clientHandshake", .bytes 60),
    ("clientHash", .bytes 32), ("certificate", .bytes certificateSize)]
  let get := lookup inputs
  let client := get "clientHandshake"
  let application := TlsKdf.applicationSecretsFast Sha256.symbolic (get "mainSecret") (get "serverHash")
  let verifyData := TlsKdf.finished Sha256.symbolic (blockSecret client) (get "clientHash")
  let header : List (BVExpr 8) := [20, 0, 0, 32].map const
  { name := "tls-finish", inputs, outputs := [
      priv "clientApplication" (HybridKdf.trafficBlock application.1),
      priv "serverApplication" (HybridKdf.trafficBlock application.2),
      pub "record" (TlsRecord.sealCore Gcm.symbolic (blockKey client) (blockIv client) (zeros 8)
        (get "certificate" ++ header ++ verifyData) 22 0)] }

/-- KeyUpdate of one direction. -/
def tlsUpdate : Kernel :=
  let inputs := [("traffic", Shape.bytes 60)]
  let get := lookup inputs
  { name := "tls-update", inputs, outputs := [
      priv "traffic" (HybridKdf.trafficBlock
        (TlsKdf.expandLabelFast Sha256.symbolic (blockSecret (get "traffic")) "traffic upd" [] 32))] }

def tlsParserInitial : Kernel :=
  { name := "tls-parser-initial", inputs := [("unused", .bytes 1)], outputs := [priv "parser" (zeros 11)] }

/-- Authenticate, decrypt and classify one application-phase record. -/
def tlsOpenApplication (size : Nat) : Kernel :=
  let inputs := [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8), ("record", .bytes size)]
  let get := lookup inputs
  let block := get "serverApplication"
  let out := TlsPostHandshake.openCore Gcm.symbolic Word64.symbolic ByteAuth.symbolic (get "parser")
    (blockKey block) (blockIv block) (get "sequence") (get "record")
  { name := "tls-open-application", inputs, outputs := [
      pub "event" (sl out 0 2), priv "parser" (sl out 2 11), priv "length" (sl out 13 2), priv "content" (out.drop 15)] }

/-- Seal a private payload of public size. -/
def tlsSeal (size padding : Nat) : Kernel :=
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes size)]
  let get := lookup inputs
  let block := get "clientApplication"
  { name := "tls-seal", inputs, outputs := [
      pub "record" (TlsRecord.sealCore Gcm.symbolic (blockKey block) (blockIv block) (get "sequence") (get "content") 23 padding)] }

/-- Seal a private buffer whose length is private within a public capacity. -/
def tlsSealPrivate (size : Nat) : Kernel :=
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("valid", .bytes 1),
    ("length", .bytes 2), ("content", .bytes size)]
  let get := lookup inputs
  let block := get "clientApplication"
  let out := TlsPrivateSeal.sealCore Gcm.symbolic ByteAuth.symbolic (blockKey block) (blockIv block) (get "sequence")
    (HybridService.at' (get "valid") 0) (HybridService.at' (get "length") 0) (HybridService.at' (get "length") 1) (get "content")
  { name := "tls-seal-private", inputs, outputs := [pub "accepted" (sl out 0 1), pub "record" (out.drop 1)] }

/-- Public TLS control content (KeyUpdate or close_notify) under the private keys. -/
def tlsSealControl (kind size : Nat) : Kernel :=
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes size)]
  let get := lookup inputs
  let block := get "clientApplication"
  { name := "tls-seal-control", inputs, outputs := [
      pub "record" (TlsRecord.sealCore Gcm.symbolic (blockKey block) (blockIv block) (get "sequence") (get "content") kind 0)] }

/-! ### WebSocket receive path -/

def wsInitial : Kernel :=
  let all := HybridService.initialStates
  { name := "ws-initial", inputs := [("unused", .bytes 1)], outputs := [
      priv "upgrade" (sl all 0 180), priv "frame" (sl all 180 26), priv "control" (sl all 206 636),
      priv "responseTemplate" (sl all 842 932)] }

def wsActivity (size : Nat) : Kernel :=
  let inputs := [("valid", Shape.bytes 1), ("length", .bytes 2)]
  let get := lookup inputs
  let out := TlsWebSocketActivity.run ByteAuth.symbolic size (HybridService.at' (get "valid") 0)
    (HybridService.at' (get "length") 0) (HybridService.at' (get "length") 1)
  { name := "ws-activity", inputs, outputs := [pub "accepted" (sl out 0 1), priv "masks" (out.drop 1)] }

def collect (control frameOut byte : List (BVExpr 8)) : List (BVExpr 8) :=
  TlsWebSocketControl.run ByteAuth.symbolic (control ++ sl frameOut 2 1 ++ sl frameOut 6 2 ++ byte)

/-- One byte before the 101 response has completed. `status` is
`[upgradeValid, upgradeCompleted, frameValid]`. -/
def wsUpgradeByte : Kernel :=
  let inputs := [("upgrade", Shape.bytes 180), ("accept", .bytes 28), ("frame", .bytes 26), ("control", .bytes 636),
    ("active", .bytes 1), ("byte", .bytes 1)]
  let get := lookup inputs
  let up := TlsWebSocketUpgrade.runByte ByteAuth.symbolic (get "upgrade" ++ get "accept" ++ get "active" ++ get "byte")
  let frame := TlsWebSocketIdle.run ByteAuth.symbolic HybridService.capacity (get "frame" ++ sl up 2 1 ++ get "byte")
  { name := "ws-upgrade-byte", inputs, outputs := [
      pub "status" (sl up 0 2 ++ sl frame 0 1), priv "upgrade" (up.drop 3), priv "frame" (frame.drop 8),
      priv "control" (collect (get "control") frame (get "byte"))] }

/-- One byte while no response is pending. `status` is `[frameValid]`. -/
def wsIdleByte : Kernel :=
  let inputs := [("frame", Shape.bytes 26), ("control", .bytes 636), ("active", .bytes 1), ("byte", .bytes 1)]
  let get := lookup inputs
  let frame := TlsWebSocketIdle.run ByteAuth.symbolic HybridService.capacity (get "frame" ++ get "active" ++ get "byte")
  { name := "ws-idle-byte", inputs, outputs := [
      pub "status" (sl frame 0 1), priv "frame" (frame.drop 8), priv "control" (collect (get "control") frame (get "byte"))] }

/-- One byte while a response is pending. `status` is
`[frameValid, responseValid, finished, successful]`. -/
def wsResponseByte : Kernel :=
  let inputs := [("frame", Shape.bytes 26), ("control", .bytes 636), ("response", .bytes 932),
    ("active", .bytes 1), ("byte", .bytes 1)]
  let get := lookup inputs
  let frame := TlsWebSocketFrame.runByte ByteAuth.symbolic HybridService.capacity (get "frame" ++ get "active" ++ get "byte")
  let response := TlsChatResponse.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic HybridService.capacity
    (get "response" ++ sl frame 1 1 ++ sl frame 3 1 ++ sl frame 5 1 ++ get "byte")
  { name := "ws-response-byte", inputs, outputs := [
      pub "status" (sl frame 0 1 ++ sl response 0 3), priv "frame" (frame.drop 8),
      priv "control" (collect (get "control") frame (get "byte")), priv "response" (response.drop 6)] }

/-- End of a chunk: the queue's validity, its count and reply kinds (opened),
and the control state with the queue cleared. No gates. -/
def wsControlStatus : Kernel :=
  let inputs := [("control", Shape.bytes 636)]
  let state := lookup inputs "control"
  { name := "ws-control-status", inputs, outputs := [
      pub "valid" (sl state 0 1), pub "queue" (sl state 127 5), priv "control" (sl state 0 127 ++ zeros 509)] }

/-- Masked reply frame for queue slot `index`, as a private buffer. -/
def wsControlReply (index : Nat) : Kernel :=
  let inputs := [("control", Shape.bytes 636), ("mask", .bytes 4)]
  let get := lookup inputs
  let state := get "control"
  let out := TlsWebSocketControl.encode ByteAuth.symbolic
    (sl state 0 1 ++ [const 0] ++ sl state (132 + index) 1 ++ sl state (128 + index) 1 ++ get "mask" ++
      sl state (136 + 125 * index) 125)
  { name := "ws-control-reply", inputs, outputs := [priv "valid" (sl out 0 1), priv "length" (sl out 1 2), priv "content" (out.drop 3)] }

/-! ### Signal service -/

def signalUpgrade (passwordBytes : Nat) : Kernel :=
  let inputs := [("credentials", Shape.bytes (16 + passwordBytes)), ("nonce", .bytes 16)]
  let get := lookup inputs
  { name := "signal-upgrade", inputs, outputs := [
      priv "content" (RelayUpgrade.request ByteAuth.symbolic passwordBytes (get "credentials" ++ get "nonce"))] }

/-! Conversation record: certificate, session block (182 + plaintext capacity),
metadata (57). -/
def conversationBytes (cert size : Nat) : Nat := cert + 182 + size + 57

/-- The recipient's public key as the 255-bit word X25519 uses (top bit dropped),
and the connection's initial request id. No gates. -/
def signalConversationView (cert size : Nat) : Kernel :=
  let inputs := [("conversation", Shape.bytes (conversationBytes cert size))]
  let record := lookup inputs "conversation"
  { name := "signal-conversation-view", inputs, outputs := [
      ⟨"recipient", 255, false, sl record (cert + 150) 32⟩,
      priv "requestId" (sl record (cert + 182 + size + 40) 8)] }

/-- One established sealed-sender text send: text content, message encryption
with SPQR, sealed sender, relay request and masked WebSocket frame, with the
producer status gated by the text's validity. The next conversation record and
request id are selected inside the circuit (unchanged on rejection). `response`
is the response parser state expecting this request's id. -/
def signalSend (cert : Nat) : Kernel :=
  let size := 80
  let inputs := [("conversation", Shape.bytes (conversationBytes cert size)), ("text", .bytes 59), ("requestId", .bytes 8),
    ("ephemeralPublic", .word), ("senderPublic", .word), ("ephemeralAgreement", .word), ("staticAgreement", .word),
    ("mask", .bytes 4), ("responseTemplate", .bytes 932)]
  let get := lookup inputs
  let record := get "conversation"
  let certificate := sl record 0 cert
  let session := sl record cert (182 + size)
  let metadata := sl record (cert + 182 + size) 57
  let text := PrivateTextNotification.build Sha256.symbolic Varint64.symbolic ByteAuth.symbolic (get "text")
  let staged := sl session 0 117 ++ sl text 1 1 ++ sl session 118 64 ++ sl text 2 size
  let staged57 := sl metadata 0 32 ++ sl text 82 8 ++ get "requestId" ++ sl metadata 48 5 ++ get "mask"
  let i : SpqrSend.Input (BVExpr 8) := {
    version := HybridService.at' staged 0, counter := sl staged 1 4, previous := sl staged 5 4, ratchet := sl staged 9 32,
    chainKey := sl staged 41 32, pqChainKey := sl staged 73 32, pqCounter := sl staged 105 4, epoch := sl staged 109 8,
    kind := HybridService.at' staged 117, chunkIndex := [], chunkData := [], sender := sl staged 118 32,
    receiver := sl staged 150 32, plaintext := sl staged 182 size, addresses := [] }
  let p := PrivateConversationService.prepare Aes.symbolic Varint64.symbolic RelayEncoding.decimalSymbolic
    Sha256.symbolic ByteAuth.symbolic false false (get "ephemeralPublic") (get "senderPublic")
    (get "ephemeralAgreement") (get "staticAgreement") certificate staged57 i
  let out := PrivateConversationService.output ByteAuth.symbolic i staged57 p
  let status := [TlsProviderGate.gate ByteAuth.symbolic (HybridService.at' out 0) (HybridService.at' text 0)]
  let next := sl staged 0 1 ++ sl out 33 4 ++ sl staged 5 36 ++ sl out 1 32 ++ sl out 37 32 ++ sl out 69 4 ++ staged.drop 109
  let template := get "responseTemplate"
  { name := "signal-send", inputs, outputs := [
      pub "status" status, priv "conversation" (certificate ++ next ++ metadata), priv "requestId" (sl out 73 8),
      priv "response" (sl template 0 891 ++ get "requestId" ++ template.drop 899),
      priv "valid" status, priv "length" (sl out 81 2), priv "content" (out.drop 83)] }

/-- Kernel named on the command line, with its public shape parameters. -/
def find : List String → Option Kernel
  | ["tls-derive"] => some tlsDerive
  | ["tls-verify-finished"] => some tlsVerifyFinished
  | ["tls-update"] => some tlsUpdate
  | ["tls-parser-initial"] => some tlsParserInitial
  | ["ws-initial"] => some wsInitial
  | ["ws-upgrade-byte"] => some wsUpgradeByte
  | ["ws-idle-byte"] => some wsIdleByte
  | ["ws-response-byte"] => some wsResponseByte
  | ["ws-control-status"] => some wsControlStatus
  | [name, a] =>
      match name, a.toNat? with
      | "tls-open-handshake", some n => if 22 ≤ n && n ≤ 16645 then some (tlsOpenHandshake n) else none
      | "tls-finish", some n => if n ≤ 64 then some (tlsFinish n) else none
      | "tls-open-application", some n => if 22 ≤ n && n ≤ 16406 then some (tlsOpenApplication n) else none
      | "tls-seal-private", some n => if 0 < n && n ≤ 16384 then some (tlsSealPrivate n) else none
      | "ws-activity", some n => if 0 < n && n ≤ 16385 then some (wsActivity n) else none
      | "ws-control-reply", some n => if n < 4 then some (wsControlReply n) else none
      | "signal-upgrade", some n => if n ≤ 256 then some (signalUpgrade n) else none
      | "signal-conversation-view", some n => if n ≤ 1024 then some (signalConversationView n 80) else none
      | "signal-send", some n => if n ≤ 1024 then some (signalSend n) else none
      | _, _ => none
  | [name, a, b] =>
      match name, a.toNat?, b.toNat? with
      | "tls-seal", some n, some pad => if 0 < n && n + 1 + pad ≤ 16385 then some (tlsSeal n pad) else none
      | "tls-seal-control", some kind, some n =>
          if (kind == 21 && n == 2) || (kind == 22 && n == 5) then some (tlsSealControl kind n) else none
      | _, _, _ => none
  | _ => none

end TlsMpc.HybridKernel
