import TlsMpc.HybridKdf
import TlsMpc.HybridService
import TlsMpc.Signal.PrivateService
import TlsMpc.Signal.PrivateDecimal
import TlsMpc.Signal.SpqrSend
import TlsMpc.Signal.SealedSenderV1
import TlsMpc.Sha256Backend
import TlsMpc.Sha256Ripple
import TlsMpc.ModAdd

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
  /-- 0: `opened` decides (public or private). 1 or 2: may be opened to that
  party only (1 = the garbling party, 2 = the evaluating party). -/
  audience : Nat := 0

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

def priv (name : String) (value : List (BVExpr 8)) : Output :=
  { name, bits := 8 * value.length, opened := false, value }
def pub (name : String) (value : List (BVExpr 8)) : Output :=
  { name, bits := 8 * value.length, opened := true, value }
/-- Opened to one party only. -/
def toParty (party : Nat) (name : String) (value : List (BVExpr 8)) : Output :=
  { name, bits := 8 * value.length, opened := false, value, audience := party }
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

/-- Reveal one byte of an authenticated received buffer, chosen by a public
one-hot mask, together with the buffer's length. Policy (which positions may be
asked for) is enforced by each party's public controller; this kernel only
guarantees that nothing but the selected byte and the length is opened. -/
def tlsReveal (size : Nat) : Kernel :=
  let inputs := [("length", Shape.bytes 2), ("content", .bytes size), ("select", .bytes size)]
  let get := lookup inputs
  let picked := ((get "content").zip (get "select")).foldl
    (fun acc pair => ByteAuth.symbolic.xor acc (ByteAuth.symbolic.and pair.1 pair.2)) (const 0)
  { name := "tls-reveal", inputs, outputs := [pub "length" (get "length"), pub "byte" [picked]] }

/-- Public-receive profile, whole buffer at once: the length, and every content
byte below that length (bytes at or beyond it are zero). The runtime opens the
length and then only the byte ranges the controllers ask for; which ranges may
be asked for is the controllers' policy. No selection circuit is needed because
the positions are public. -/
def tlsRevealMasked (size : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let inputs := [("length", Shape.bytes 2), ("content", .bytes size)]
  let get := lookup inputs
  let masks := (TlsWebSocketActivity.run a size (const 255)
    (HybridService.at' (get "length") 0) (HybridService.at' (get "length") 1)).drop 1
  { name := "tls-reveal-masked", inputs, outputs := [
      pub "length" (get "length"),
      pub "bytes" (((get "content").zip masks).map (fun pair => a.and pair.1 pair.2))] }

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

/-- The same request when the credentials are held as two XOR shares, one per
party: neither party alone can open the account's authenticated socket. -/
def signalUpgradeShared (passwordBytes : Nat) : Kernel :=
  let inputs := [("credentialsA", Shape.bytes (16 + passwordBytes)), ("credentialsB", .bytes (16 + passwordBytes)),
    ("nonce", .bytes 16)]
  let get := lookup inputs
  let credentials := List.zipWith ByteAuth.symbolic.xor (get "credentialsA") (get "credentialsB")
  { name := "signal-upgrade-shared", inputs, outputs := [
      priv "content" (RelayUpgrade.request ByteAuth.symbolic passwordBytes (credentials ++ get "nonce"))] }

/-! Conversation record: certificate, session block (182 + plaintext capacity),
metadata (57). -/
def conversationBytes (cert size : Nat) : Nat := cert + 182 + size + 57

/-- The recipient's public key as the 255-bit word X25519 uses (top bit dropped),
and the connection's initial request id. No gates. -/
def signalConversationView (cert size : Nat) : Kernel :=
  let inputs := [("conversation", Shape.bytes (conversationBytes cert size))]
  let record := lookup inputs "conversation"
  { name := "signal-conversation-view", inputs, outputs := [
      { name := "recipient", bits := 255, opened := false, value := sl record (cert + 150) 32 },
      priv "requestId" (sl record (cert + 182 + size + 40) 8)] }

/-- One established sealed-sender text send: text content, message encryption
with SPQR, sealed sender, relay request and masked WebSocket frame, with the
producer status gated by the text's validity. The next conversation record and
request id are selected inside the circuit (unchanged on rejection). `response`
is the response parser state expecting this request's id. -/
def signalSend (cert : Nat) (openRequestId : Bool := false) : Kernel :=
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
  -- With `openRequestId` the id used by this request may be opened, so that the
  -- public controllers can correlate the server's response in the clear.
  { name := if openRequestId then "signal-send-open" else "signal-send", inputs, outputs := [
      pub "status" status, priv "conversation" (certificate ++ next ++ metadata), priv "requestId" (sl out 73 8),
      priv "response" (sl template 0 891 ++ get "requestId" ++ template.drop 899),
      priv "valid" status, priv "length" (sl out 81 2), priv "content" (out.drop 83)] ++
      (if openRequestId then [pub "requestIdUsed" (get "requestId")] else []) }

/-! ### Open-envelope send (privacy policy: only contacts and client keys are secret)

The sealed-sender envelope is what the Signal server receives; it does not
identify the recipient to anyone without the recipient's key, so it may be
opened to the parties. The request around it is then assembled in the clear by
the controllers, and only the fields that identify the contact are formatted
and inserted inside the engines. -/

/-- Session encryption with SPQR and sealed sender, without the relay request.
Opened: the gated status, the envelope with its length (zero unless the status
is 255), and the message timestamp. The next conversation record is selected
inside the circuit. -/
def signalSeal (cert : Nat) : Kernel :=
  let size := 80
  let a := ByteAuth.symbolic
  let inputs := [("conversation", Shape.bytes (conversationBytes cert size)), ("text", .bytes 59),
    ("ephemeralPublic", .word), ("senderPublic", .word), ("ephemeralAgreement", .word), ("staticAgreement", .word)]
  let get := lookup inputs
  let record := get "conversation"
  let certificate := sl record 0 cert
  let session := sl record cert (182 + size)
  let metadata := sl record (cert + 182 + size) 57
  let text := PrivateTextNotification.build Sha256.symbolic Varint64.symbolic a (get "text")
  let staged := sl session 0 117 ++ sl text 1 1 ++ sl session 118 64 ++ sl text 2 size
  let i : SpqrSend.Input (BVExpr 8) := {
    version := HybridService.at' staged 0, counter := sl staged 1 4, previous := sl staged 5 4, ratchet := sl staged 9 32,
    chainKey := sl staged 41 32, pqChainKey := sl staged 73 32, pqCounter := sl staged 105 4, epoch := sl staged 109 8,
    kind := HybridService.at' staged 117, chunkIndex := [], chunkData := [], sender := sl staged 118 32,
    receiver := sl staged 150 32, plaintext := sl staged 182 size, addresses := [] }
  let inner := PrivateSpqrSend.prepare Aes.symbolic Varint64.symbolic Sha256.symbolic a false false i
  let envelope := PrivateSealedSender.boundSeal Aes.symbolic Sha256.symbolic a i.receiver (get "ephemeralPublic")
    (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement") certificate i.sender inner.wire
  -- status, selected state (chain 32, counter 4, pq chain 32, pq counter 4), length 2, data
  let out := PrivateSpqrSend.output a (PrivateSpqrSend.oldState i) ⟨inner.candidateState, envelope⟩
  let status := TlsProviderGate.gate a (HybridService.at' out 0) (HybridService.at' text 0)
  let released := ByteAuth.release a status (out.drop 73)
  let next := sl staged 0 1 ++ sl out 33 4 ++ sl staged 5 36 ++ sl out 1 32 ++ sl out 37 32 ++ sl out 69 4 ++ staged.drop 109
  { name := "signal-seal", inputs, outputs := [
      pub "status" [status], priv "conversation" (certificate ++ next ++ metadata),
      pub "timestamp" (sl text 82 8), pub "length" (sl released 0 2), pub "envelope" (released.drop 2)] }

/-! Public-length variant. Lengths are public under the policy, and the opened
envelope's length already determines the varint widths of the message
counters, so those widths are opened first and the message is built with the
fixed-width definitions (no private-length buffers). -/

def orMask (x y : BVExpr 8) : BVExpr 8 :=
  ByteAuth.symbolic.not (ByteAuth.symbolic.and (ByteAuth.symbolic.not x) (ByteAuth.symbolic.not y))

/-- Flags `value ≥ 2^(7k)` for `k = 1..groups`, as 0/255 bytes, for a big-endian
value: the varint width is one plus the number of set flags. -/
def widthFlags (bigEndian : List (BVExpr 8)) (groups : Nat) : List (BVExpr 8) :=
  let n := bigEndian.length
  let bit (j : Nat) : BVExpr 8 := ByteAuth.symbolic.maskBit (HybridService.at' bigEndian (n - 1 - j / 8)) (j % 8)
  (List.range groups).map (fun k =>
    (List.range (8 * n)).foldl (fun acc j => if 7 * (k + 1) ≤ j then orMask acc (bit j) else acc) (const 0))

/-- Opens the varint widths of the message counter, previous counter, SPQR
epoch and next SPQR counter (as width flags). -/
def signalWidths (cert : Nat) : Kernel :=
  let inputs := [("conversation", Shape.bytes (conversationBytes cert 80))]
  let session := sl (lookup inputs "conversation") cert 262
  { name := "signal-widths", inputs, outputs := [
      pub "counter" (widthFlags (sl session 1 4) 4), pub "previous" (widthFlags (sl session 5 4) 4),
      pub "epoch" (widthFlags (sl session 109 8) 9),
      pub "index" (widthFlags (ChainSend.nextCounter Sha256.symbolic ByteAuth.symbolic (sl session 105 4)) 4)] }

/-- `signalSeal` with public varint widths: the fixed-width message and
sealed-sender definitions. The status additionally requires the counters to
have exactly the stated widths. The envelope has a public length.

`classes` (built text only) is the message's size class: its padded content is
`PrivateTextNotification.paddedBytes classes` bytes (80 per class, as Signal
pads), and the text input is the `builtBytes classes` bytes that
`PrivateTextNotification.buildSized _ classes` returns. The envelope's length
is a function of the certificate size, the four widths and the class alone, so
an observer of the envelope size learns the class (the length of the message's
Content plus terminator rounded up to a multiple of 80 bytes) and nothing finer
about the text. Class 1 is the circuit this kernel was before it had classes.
The conversation record keeps its layout: its 80-byte plaintext slot holds the
first block of the content. -/
def signalSealFixed (cert counterWidth previousWidth epochWidth indexWidth : Nat) (builtText : Bool := false)
    (classes : Nat := 1) : Kernel :=
  let size := 80
  let content := if builtText then PrivateTextNotification.paddedBytes classes else size
  let a := ByteAuth.symbolic
  let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
  let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
  let inputs := [("conversation", Shape.bytes (conversationBytes cert size)),
    ("text", .bytes (if builtText then PrivateTextNotification.builtBytes classes else 59)),
    ("ephemeralPublic", .word), ("senderPublic", .word), ("ephemeralAgreement", .word), ("staticAgreement", .word)]
  let get := lookup inputs
  let record := get "conversation"
  let certificate := sl record 0 cert
  let session := sl record cert (182 + size)
  let metadata := sl record (cert + 182 + size) 57
  -- `builtText`: the caller supplies the output of `PrivateTextNotification.buildSized` for
  -- this class (validity byte, kind, `content` padded content bytes, timestamp). Used when the
  -- message text is public and the controllers build the content in the clear with that definition.
  let text := if builtText then get "text"
    else PrivateTextNotification.build Sha256.symbolic Varint64.symbolic a (get "text")
  let staged := sl session 0 117 ++ sl text 1 1 ++ sl session 118 64 ++ sl text 2 size
  let i : SpqrSend.Input (BVExpr 8) := {
    version := HybridService.at' staged 0, counter := sl staged 1 4, previous := sl staged 5 4, ratchet := sl staged 9 32,
    chainKey := sl staged 41 32, pqChainKey := sl staged 73 32, pqCounter := sl staged 105 4, epoch := sl staged 109 8,
    kind := HybridService.at' staged 117, chunkIndex := [], chunkData := [], sender := sl staged 118 32,
    receiver := sl staged 150 32, plaintext := sl text 2 content, addresses := [] }
  -- SHA-256 backend with a one-AND-per-bit adder, proved equal to addition (TlsMpc/Sha256Ripple.lean).
  let sha := Sha256Ripple.ops
  let accepted := SpqrSend.acceptedMask Varint64.symbolic sha a shape pqShape i
  let p := SpqrSend.prepare Aes.symbolic Varint64.symbolic sha a shape pqShape i
  let sealed := SealedSenderV1.boundSeal Aes.symbolic sha a i.receiver (get "ephemeralPublic")
    (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement") certificate p.wire i.sender
  let status := TlsProviderGate.gate a (TlsProviderGate.gate a accepted (HybridService.at' sealed 0)) (HybridService.at' text 0)
  let choose := fun next old => ChainSend.selectState a status next old
  let next := sl staged 0 1 ++ choose p.nextCounter i.counter ++ sl staged 5 36 ++ choose p.nextChainKey i.chainKey ++
    choose p.nextPqChainKey i.pqChainKey ++ choose p.nextPqCounter i.pqCounter ++ staged.drop 109
  { name := if builtText then "signal-seal-built" else "signal-seal-fixed", inputs, outputs := [
      pub "status" [status], priv "conversation" (certificate ++ next ++ metadata),
      pub "timestamp" (sl text (2 + content) 8), pub "envelope" (ByteAuth.release a status (sealed.drop 1))] }

/-- MEASUREMENT ONLY, never run by the worker: prefixes of `signalSealFixed`, to
count gates per stage. Stage 0 outputs the built text content; stage 1 also the
session-encrypted message and next state; stage 2 the acceptance mask as well.
The full kernel adds sealed sender on top of stage 1. -/
def signalSealProbe (stage cert counterWidth previousWidth epochWidth indexWidth : Nat) : Kernel :=
  let size := 80
  let a := ByteAuth.symbolic
  let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
  let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
  let inputs := [("conversation", Shape.bytes (conversationBytes cert size)), ("text", .bytes 59)]
  let get := lookup inputs
  let record := get "conversation"
  let session := sl record cert (182 + size)
  let text := PrivateTextNotification.build Sha256.symbolic Varint64.symbolic a (get "text")
  let staged := sl session 0 117 ++ sl text 1 1 ++ sl session 118 64 ++ sl text 2 size
  let i : SpqrSend.Input (BVExpr 8) := {
    version := HybridService.at' staged 0, counter := sl staged 1 4, previous := sl staged 5 4, ratchet := sl staged 9 32,
    chainKey := sl staged 41 32, pqChainKey := sl staged 73 32, pqCounter := sl staged 105 4, epoch := sl staged 109 8,
    kind := HybridService.at' staged 117, chunkIndex := [], chunkData := [], sender := sl staged 118 32,
    receiver := sl staged 150 32, plaintext := sl staged 182 size, addresses := [] }
  let sha := Sha256Ripple.ops
  let p := SpqrSend.prepare Aes.symbolic Varint64.symbolic sha a shape pqShape i
  let accepted := SpqrSend.acceptedMask Varint64.symbolic sha a shape pqShape i
  { name := "signal-seal-probe", inputs, outputs :=
      [pub "text" text] ++
      (if stage ≥ 1 then [pub "wire" p.wire, pub "state" (p.nextCounter ++ p.nextChainKey ++ p.nextPqChainKey ++ p.nextPqCounter)] else []) ++
      (if stage ≥ 2 then [pub "accepted" [accepted]] else []) }

/-- A decimal number in a fixed-width slot, padded with spaces (valid JSON
whitespace), so that its digit count stays private. -/
def paddedDecimal (number : BVExpr 64) (width : Nat) : BVExpr 8 × List (BVExpr 8) :=
  let a := ByteAuth.symbolic
  let buffer := PrivateDecimal.encode RelayEncoding.decimalSymbolic a number
  (a.and buffer.valid (ByteAuth.zeroMask a (HybridService.at' buffer.data width)),
   (buffer.data.take width).map (fun byte => TlsInner.select a (ByteAuth.zeroMask a byte) (a.const 32) byte))

/-- Seal the relay request. `frame` is the complete masked WebSocket frame built
in the clear, with zero bytes in four slots; this kernel formats the recipient
UUID (36), the access key in base64 (24), the device id (3) and the
registration id (10) from the private conversation record, applies the public
WebSocket mask, inserts them at the given offsets, and seals the TLS record. -/
def signalRequestSeal (cert size uuidAt keyAt deviceAt registrationAt : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8),
    ("conversation", .bytes (conversationBytes cert 80)), ("frame", .bytes size), ("mask", .bytes 4)]
  let get := lookup inputs
  let metadata := sl (get "conversation") (cert + 262) 57
  let device := paddedDecimal (RelayRequest.word Varint64.symbolic a metadata 48 1) 3
  let registration := paddedDecimal (RelayRequest.word Varint64.symbolic a metadata 49 4) 10
  let slots : List (Nat × List (BVExpr 8)) := [(uuidAt, RelayEncoding.uuid a (sl metadata 0 16)),
    (keyAt, RelayEncoding.base64 a (sl metadata 16 16)), (deviceAt, device.2), (registrationAt, registration.2)]
  let secretAt (index : Nat) : Option (BVExpr 8) := slots.findSome? (fun slot =>
    if slot.1 ≤ index && index < slot.1 + slot.2.length then some (HybridService.at' slot.2 (index - slot.1)) else none)
  let plaintext := (get "frame").zipIdx.map (fun pair => match secretAt pair.2 with
    | some secret => a.xor pair.1 (a.xor secret (HybridService.at' (get "mask") ((pair.2 - 8) % 4)))
    | none => pair.1)
  let valid := a.and device.1 registration.1
  let block := get "clientApplication"
  { name := "signal-request-seal", inputs, outputs := [
      pub "accepted" [valid],
      pub "record" (ByteAuth.release a valid
        (TlsRecord.sealCore Gcm.symbolic (blockKey block) (blockIv block) (get "sequence") plaintext 23 0))] }

/-! ### AES-GCM with shared GHASH key powers

Design and security argument: `handshake_backend/EmpHybridWork/GHASH_SHARES.md`
and `TlsMpc/GhashShares.lean`. The engines compute only AES (the CTR keystream
and the per-record pad) and combine or check the two parties' locally computed
halves of the tag polynomial. -/

def xorBytes (x y : List (BVExpr 8)) : List (BVExpr 8) := Aes.addRoundKey Gcm.symbolic.aes x y

def gcmExpanded (traffic : List (BVExpr 8)) : List (BVExpr 8) :=
  Aes.expandKey Gcm.symbolic.aes 4 10 (blockKey traffic)

/-- The per-record pad `AES_K(J0)`. -/
def gcmPad (traffic sequence : List (BVExpr 8)) : List (BVExpr 8) :=
  Aes.encryptExpanded Gcm.symbolic.aes 10 (gcmExpanded traffic)
    (TlsRecord.nonce Gcm.symbolic (blockIv traffic) sequence ++ Gcm.encodeNat Gcm.symbolic 4 1)

/-- Shares of `H = AES_K(0)`: the garbling party supplies a private mask and
keeps it as its share; `H ⊕ mask` is opened to the evaluating party only. -/
def gcmKeyShare : Kernel :=
  let inputs := [("traffic", Shape.bytes 60), ("mask", .bytes 16)]
  let get := lookup inputs
  let h := Aes.encryptExpanded Gcm.symbolic.aes 10 (gcmExpanded (get "traffic")) (Gcm.zeros Gcm.symbolic 16)
  { name := "gcm-key-share", inputs, outputs := [toParty 2 "masked" (xorBytes h (get "mask"))] }

/-- Product of two shared field elements, re-shared the same way. -/
def gcmMultiply : Kernel :=
  let inputs := [("leftA", Shape.bytes 16), ("leftB", .bytes 16), ("rightA", .bytes 16), ("rightB", .bytes 16),
    ("mask", .bytes 16)]
  let get := lookup inputs
  let g := Gcm.symbolic
  let product := Ghash.multiply g.field (g.pack (xorBytes (get "leftA") (get "leftB")))
    (g.pack (xorBytes (get "rightA") (get "rightB")))
  { name := "gcm-multiply", inputs, outputs := [toParty 2 "masked" (xorBytes (g.unpack product) (get "mask"))] }

/-- The tag of a record being sealed: pad ⊕ both halves. -/
def gcmTag : Kernel :=
  let inputs := [("pad", Shape.bytes 16), ("halfA", .bytes 16), ("halfB", .bytes 16)]
  let get := lookup inputs
  { name := "gcm-tag", inputs, outputs := [pub "tag" (xorBytes (xorBytes (get "pad") (get "halfA")) (get "halfB"))] }

/-- The private acceptance mask of a received record: 255 exactly when
pad ⊕ both halves equals the received tag. -/
def gcmCheck : Kernel :=
  let inputs := [("traffic", Shape.bytes 60), ("sequence", .bytes 8), ("halfA", .bytes 16), ("halfB", .bytes 16),
    ("tag", .bytes 16)]
  let get := lookup inputs
  let expected := xorBytes (xorBytes (gcmPad (get "traffic") (get "sequence")) (get "halfA")) (get "halfB")
  { name := "gcm-check", inputs, outputs := [priv "accepted" [ByteAuth.equalMask ByteAuth.symbolic expected (get "tag")]] }

/-- `signalRequestSeal` without the tag: the record header and ciphertext are
opened and the pad stays private for `gcmTag`. -/
def signalRequestCtr (cert size uuidAt keyAt deviceAt registrationAt : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8),
    ("conversation", .bytes (conversationBytes cert 80)), ("frame", .bytes size), ("mask", .bytes 4)]
  let get := lookup inputs
  let metadata := sl (get "conversation") (cert + 262) 57
  let device := paddedDecimal (RelayRequest.word Varint64.symbolic a metadata 48 1) 3
  let registration := paddedDecimal (RelayRequest.word Varint64.symbolic a metadata 49 4) 10
  let slots : List (Nat × List (BVExpr 8)) := [(uuidAt, RelayEncoding.uuid a (sl metadata 0 16)),
    (keyAt, RelayEncoding.base64 a (sl metadata 16 16)), (deviceAt, device.2), (registrationAt, registration.2)]
  let secretAt (index : Nat) : Option (BVExpr 8) := slots.findSome? (fun slot =>
    if slot.1 ≤ index && index < slot.1 + slot.2.length then some (HybridService.at' slot.2 (index - slot.1)) else none)
  let plaintext := (get "frame").zipIdx.map (fun pair => match secretAt pair.2 with
    | some secret => a.xor pair.1 (a.xor secret (HybridService.at' (get "mask") ((pair.2 - 8) % 4)))
    | none => pair.1)
  let valid := a.and device.1 registration.1
  let block := get "clientApplication"
  let inner := TlsRecord.inner g plaintext 23 0
  let ciphertext := Gcm.ctr g (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "sequence")) inner
  { name := "signal-request-ctr", inputs, outputs := [
      pub "accepted" [valid], pub "header" (TlsRecord.header g (inner.length + 16)),
      pub "ciphertext" (ByteAuth.release a valid ciphertext), priv "pad" (gcmPad block (get "sequence"))] }

/-- `tlsSeal` / `tlsSealControl` without the tag: header and ciphertext are
opened, the pad stays private for `gcmTag`. -/
def tlsSealCtr (kind size padding : Nat) : Kernel :=
  let g := Gcm.symbolic
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes size)]
  let get := lookup inputs
  let block := get "clientApplication"
  let inner := TlsRecord.inner g (get "content") kind padding
  { name := "tls-seal-ctr", inputs, outputs := [
      pub "header" (TlsRecord.header g (inner.length + 16)),
      pub "ciphertext" (Gcm.ctr g (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "sequence")) inner),
      priv "pad" (gcmPad block (get "sequence"))] }

/-- `tlsSealPrivate` without the tag. The ciphertext is released only when the
buffer is accepted. -/
def tlsSealPrivateCtr (size : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("valid", .bytes 1),
    ("length", .bytes 2), ("content", .bytes size)]
  let get := lookup inputs
  let block := get "clientApplication"
  let built := TlsPrivateSeal.build a (HybridService.at' (get "length") 0) (HybridService.at' (get "length") 1) 0 (get "content")
  let accepted := a.and (ByteAuth.eqMask a (HybridService.at' (get "valid") 0) (a.const 255)) built.valid
  let ciphertext := Gcm.ctr g (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "sequence")) built.bytes
  { name := "tls-seal-private-ctr", inputs, outputs := [
      pub "accepted" [accepted], pub "header" (TlsRecord.header g (size + 17)),
      pub "ciphertext" (ByteAuth.release a accepted ciphertext), priv "pad" (gcmPad block (get "sequence"))] }

/-! ### Per-contact state at rest

A contact's record is stored as ciphertext held by both computation nodes
(each uses its own copy, so one node cannot substitute or roll it back). The
key exists only as a secret-shared scalar on the database nodes, delivered to
the two computation nodes as additive shares modulo `2^255 − 19` (the share
field of the database and the field of the field engine).
The public check value (one AES block under the key) detects a wrong key,
whether from a bad database share or a party altering its own share. -/

/-- The field of the stored per-contact scalars. -/
def shareModulus : Nat := 2 ^ 255 - 19

/-- The record key from the two parties' additive shares of the stored scalar:
`SHA-256("CONTACT_STATE_KEY_V1" ‖ scalar)`, laid out as a traffic block. -/
def contactKey : Kernel :=
  let inputs := [("shareA", Shape.bytes 32), ("shareB", .bytes 32)]
  let get := lookup inputs
  let scalar := ModAdd.modAddBytes shareModulus (get "shareA") (get "shareB")
  let label := "CONTACT_STATE_KEY_V1".toUTF8.toList.map (fun byte => const byte.toNat)
  let digest := Sha256.hash Sha256Ripple.ops (label ++ scalar)
  { name := "contact-key", inputs, outputs := [priv "traffic" (zeros 32 ++ sl digest 0 28)] }

/-- The key check value: the pad for the reserved version `2^64 − 1`. -/
def contactCheck (traffic : List (BVExpr 8)) : List (BVExpr 8) :=
  gcmPad traffic (List.replicate 8 (const 255))

/-- Encrypt a record under its key for a public version number (never reused,
never `2^64 − 1`). Opens the ciphertext and the key check value. -/
def contactSeal (size : Nat) : Kernel :=
  let g := Gcm.symbolic
  let inputs := [("traffic", Shape.bytes 60), ("version", .bytes 8), ("content", .bytes size)]
  let get := lookup inputs
  let block := get "traffic"
  { name := "contact-seal", inputs, outputs := [
      pub "ciphertext" (Gcm.ctr g (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "version")) (get "content")),
      pub "check" (contactCheck block)] }

/-- Decrypt a stored record. `accepted` is 255 exactly when the key matches the
stored check value; the content is zero otherwise. -/
def contactOpen (size : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := [("traffic", Shape.bytes 60), ("version", .bytes 8), ("ciphertext", .bytes size), ("check", .bytes 16)]
  let get := lookup inputs
  let block := get "traffic"
  let accepted := ByteAuth.equalMask a (contactCheck block) (get "check")
  let content := Gcm.ctr g (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "version")) (get "ciphertext")
  { name := "contact-open", inputs, outputs := [
      pub "accepted" [accepted], priv "content" (ByteAuth.release a accepted content)] }

/-- `tlsOpenApplication` with the tag check supplied as the private mask from
`gcmCheck`: CTR decryption, header check, inner parsing and classification. -/
def tlsOpenApplicationCtr (size : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
    ("record", .bytes size), ("accepted", .bytes 1)]
  let get := lookup inputs
  let block := get "serverApplication"
  let wire := get "record"
  let ciphertext := TlsReceive.ciphertext wire
  let plaintext := Gcm.ctr g (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "sequence")) ciphertext
  let headerValid := ByteAuth.equalMask a (wire.take 5) (TlsRecord.header g (ciphertext.length + 16))
  let parsed := TlsReceive.releaseOpened a headerValid ⟨HybridService.at' (get "accepted") 0, plaintext⟩
  let out := TlsPostHandshake.core Word64.symbolic a (get "parser") parsed
  { name := "tls-open-application-ctr", inputs, outputs := [
      pub "event" (sl out 0 2), priv "parser" (sl out 2 11), priv "length" (sl out 13 2), priv "content" (out.drop 15)] }

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
  | ["gcm-key-share"] => some gcmKeyShare
  | ["gcm-multiply"] => some gcmMultiply
  | ["gcm-tag"] => some gcmTag
  | ["gcm-check"] => some gcmCheck
  | ["contact-key"] => some contactKey
  | [name, a] =>
      match name, a.toNat? with
      | "tls-open-handshake", some n => if 22 ≤ n && n ≤ 16645 then some (tlsOpenHandshake n) else none
      | "tls-finish", some n => if n ≤ 64 then some (tlsFinish n) else none
      | "tls-open-application", some n => if 22 ≤ n && n ≤ 16406 then some (tlsOpenApplication n) else none
      | "tls-seal-private", some n => if 0 < n && n ≤ 16384 then some (tlsSealPrivate n) else none
      | "contact-seal", some n => if 0 < n && n ≤ 16384 then some (contactSeal n) else none
      | "contact-open", some n => if 0 < n && n ≤ 16384 then some (contactOpen n) else none
      | "tls-seal-private-ctr", some n => if 0 < n && n ≤ 16384 then some (tlsSealPrivateCtr n) else none
      | "ws-activity", some n => if 0 < n && n ≤ 16385 then some (wsActivity n) else none
      | "ws-control-reply", some n => if n < 4 then some (wsControlReply n) else none
      | "signal-upgrade", some n => if n ≤ 256 then some (signalUpgrade n) else none
      | "signal-upgrade-shared", some n => if n ≤ 256 then some (signalUpgradeShared n) else none
      | "signal-conversation-view", some n => if n ≤ 1024 then some (signalConversationView n 80) else none
      | "signal-send", some n => if n ≤ 1024 then some (signalSend n) else none
      | "signal-send-open", some n => if n ≤ 1024 then some (signalSend n true) else none
      | "signal-seal", some n => if n ≤ 1024 then some (signalSeal n) else none
      | "signal-widths", some n => if n ≤ 1024 then some (signalWidths n) else none
      | "tls-reveal", some n => if 0 < n && n ≤ 16385 then some (tlsReveal n) else none
      | "tls-reveal-masked", some n => if 0 < n && n ≤ 16385 then some (tlsRevealMasked n) else none
      | "tls-open-application-ctr", some n => if 22 ≤ n && n ≤ 16406 then some (tlsOpenApplicationCtr n) else none
      | _, _ => none
  | [name, a, b] =>
      match name, a.toNat?, b.toNat? with
      | "tls-seal", some n, some pad => if 0 < n && n + 1 + pad ≤ 16385 then some (tlsSeal n pad) else none
      | "signal-seal-probe", some stage, some cert =>
          if stage ≤ 2 && cert ≤ 1024 then some (signalSealProbe stage cert 1 1 1 1) else none
      | "tls-seal-control", some kind, some n =>
          if (kind == 21 && n == 2) || (kind == 22 && n == 5) then some (tlsSealControl kind n) else none
      | _, _, _ => none
  | ["tls-seal-ctr", kind, size, padding] =>
      match kind.toNat?, size.toNat?, padding.toNat? with
      | some kind, some n, some pad =>
          if (kind == 23 && 0 < n && n + 1 + pad ≤ 16385) || (pad == 0 && ((kind == 21 && n == 2) || (kind == 22 && n == 5)))
          then some (tlsSealCtr kind n pad) else none
      | _, _, _ => none
  | ["signal-seal-fixed", cert, counterWidth, previousWidth, epochWidth, indexWidth] =>
      match cert.toNat?, counterWidth.toNat?, previousWidth.toNat?, epochWidth.toNat?, indexWidth.toNat? with
      | some cert, some cw, some pw, some ew, some iw =>
          if cert ≤ 1024 && 1 ≤ cw && cw ≤ 5 && 1 ≤ pw && pw ≤ 5 && 1 ≤ ew && ew ≤ 10 && 1 ≤ iw && iw ≤ 5 then
            some (signalSealFixed cert cw pw ew iw) else none
      | _, _, _, _, _ => none
  -- Built public text: the second parameter is the size class (80 padded content bytes each).
  | ["signal-seal-built", cert, classes, counterWidth, previousWidth, epochWidth, indexWidth] =>
      match cert.toNat?, classes.toNat?, counterWidth.toNat?, previousWidth.toNat?, epochWidth.toNat?, indexWidth.toNat? with
      | some cert, some classes, some cw, some pw, some ew, some iw =>
          if cert ≤ 1024 && 1 ≤ classes && classes ≤ 4 &&
              1 ≤ cw && cw ≤ 5 && 1 ≤ pw && pw ≤ 5 && 1 ≤ ew && ew ≤ 10 && 1 ≤ iw && iw ≤ 5 then
            some (signalSealFixed cert cw pw ew iw true classes) else none
      | _, _, _, _, _, _ => none
  | ["signal-request-seal", cert, size, uuidAt, keyAt, deviceAt, registrationAt] =>
      match cert.toNat?, size.toNat?, uuidAt.toNat?, keyAt.toNat?, deviceAt.toNat?, registrationAt.toNat? with
      | some cert, some size, some u, some k, some d, some r =>
          if cert ≤ 1024 && 0 < size && size ≤ 16384 && 8 ≤ u && u + 36 ≤ size && 8 ≤ k && k + 24 ≤ size &&
              8 ≤ d && d + 3 ≤ size && 8 ≤ r && r + 10 ≤ size then
            some (signalRequestSeal cert size u k d r) else none
      | _, _, _, _, _, _ => none
  | ["signal-request-ctr", cert, size, uuidAt, keyAt, deviceAt, registrationAt] =>
      match cert.toNat?, size.toNat?, uuidAt.toNat?, keyAt.toNat?, deviceAt.toNat?, registrationAt.toNat? with
      | some cert, some size, some u, some k, some d, some r =>
          if cert ≤ 1024 && 0 < size && size ≤ 16384 && 8 ≤ u && u + 36 ≤ size && 8 ≤ k && k + 24 ≤ size &&
              8 ≤ d && d + 3 ≤ size && 8 ≤ r && r + 10 ≤ size then
            some (signalRequestCtr cert size u k d r) else none
      | _, _, _, _, _, _ => none
  | _ => none

end TlsMpc.HybridKernel
