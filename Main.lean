import Lean
import TlsMpc
import TlsMpc.Signal.Unpad
import TlsMpc.Signal.Export
import TlsMpc.TlsPostHandshake
import TlsMpc.TlsApplicationRoute

/-!
Native export tool. All protocol expressions and compiler passes live in Lean.
The JSON transport is unverified; each output is parsed back and compared before
it is emitted. Theorems in Artifact/TlsLayout cover the numeric artifact itself.
-/

open TlsMpc
open Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-boolean-v1"
  name : String
  input_bits : Nat
  outputs : List Boolean.Artifact.Block
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def imageOf (name : String) (description : String) (outputs : List (Boolean.Expr inputs)) : Image :=
  { name, input_bits := inputs, outputs := Boolean.Artifact.exportProgram outputs,
    input_description := description }

structure DagImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def dagImageOfWidths (name : String) (widths : Array Nat) (description : String)
    (bytes : List (BVExpr 8)) : DagImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name, input_bits := widths.foldl (· + ·) 0, input_widths := widths,
    nodes := AigExport.exportNodes circuit.aig, outputs, input_description := description }

def dagImageOf (name : String) (inputBytes : Nat) (description : String)
    (bytes : List (BVExpr 8)) : DagImage :=
  dagImageOfWidths name (Array.replicate inputBytes 8) description bytes

def emitJson [Lean.ToJson α] [Lean.FromJson α] [BEq α] (image : α) : IO Unit := do
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := α) with
  | .error message => throw (IO.userError s!"export round-trip failed: {message}")
  | .ok decoded =>
      unless decoded == image do throw (IO.userError "export round-trip changed the artifact")
  (← IO.getStdout).putStrLn serialized

def releaseCircuit (size : Nat) : List (Boolean.Expr (1 + size)) :=
  List.ofFn (fun (i : Fin size) =>
    Authenticated.releaseBit (.input ⟨0, by omega⟩) (.input ⟨i.val + 1, by omega⟩))

def number (text : String) : IO Nat :=
  match text.toNat? with
  | some value => pure value
  | none => throw (IO.userError "expected a nonnegative decimal integer")

def checkSize (content padding : Nat) : IO Unit := do
  if content + 1 + padding > 16385 then
    throw (IO.userError "TLSInnerPlaintext exceeds the TLS 1.3 limit")

def fieldNodeJson : FieldDag.Node → Lean.Json
  | .input i => Lean.Json.mkObj [("op", Lean.toJson "input"), ("index", Lean.toJson i)]
  | .const n => Lean.Json.mkObj [("op", Lean.toJson "const"), ("value", Lean.toJson (toString n))]
  | .bin op a b => Lean.Json.mkObj [("op", Lean.toJson (match op with
      | .add => "add" | .sub => "sub" | .mul => "mul")),
      ("left", Lean.toJson a), ("right", Lean.toJson b)]

structure FieldImage where
  format : String := "tls-mpc-field-dag-v1"
  name : String := "x25519"
  modulus : String := toString FieldDag.modulus
  input_count : Nat := 257
  bit_inputs : Array Nat := (List.range 256).toArray
  nodes : Array Lean.Json
  outputs : Array Nat
  input_description : String := "256 secret scalar bits in LSB order, then secret u-coordinate field element; scalar clamping inside circuit; canonical little-endian u input masks bit255 before field reduction; output remains a secret field element; TLS rejects zero; public-key release is separate"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  if ← Signal.Export.tryRun args then return
  match args with
  | ["x25519-field"] =>
      match FieldDag.compile X25519.expr with
      | none => throw (IO.userError "X25519 field compilation failed its verified translation validator")
      | some artifact =>
          emitJson ({ nodes := artifact.nodes.toArray.map fieldNodeJson
                      outputs := #[artifact.output] } : FieldImage)
  | ["tls-route-application", size] =>
      let size ← number size
      if size == 0 || size > 1024 then
        throw (IO.userError "TLS application route accepts buffer capacity 1..1024")
      emitJson (dagImageOf "tls-route-application" (15+size)
        "11-byte shared parser state then authenticated TLSReceive result; open ONLY event/request2; event5 means rerun full post-handshake parser on ORIGINAL shared input, discard all route output; otherwise state11 and length2/buffer stay shared"
        (TlsApplicationRoute.core Signal.Word64.symbolic ByteAuth.symbolic
          (ByteCircuit.inputBytes 0 11) (ByteCircuit.inputBytes 11 (4+size))))
  | ["tls-open-application-record", size] =>
      let size ← number size
      if size < 22 || size > 1045 then
        throw (IO.userError "TLS application record export accepts 22..1045 wire bytes")
      emitJson (dagImageOf "tls-open-application-record" (47+size)
        "11-byte secret parser state, key16,IV12,sequence8,wire; only output event/request2 may be opened; next state11 and application length2/buffer stay shared"
        (TlsPostHandshake.openCore Gcm.symbolic Signal.Word64.symbolic ByteAuth.symbolic
          (ByteCircuit.inputBytes 0 11) (ByteCircuit.inputBytes 11 16)
          (ByteCircuit.inputBytes 27 12) (ByteCircuit.inputBytes 39 8) (ByteCircuit.inputBytes 47 size)))
  | ["tls-post-handshake", size] =>
      let size ← number size
      if size == 0 || size > 1024 then
        throw (IO.userError "TLS post-handshake export accepts buffer capacity 1..1024")
      emitJson (dagImageOf "tls-post-handshake" (15+size)
        "11-byte secret parser state then authenticated TLSReceive result (status,type,length2,buffer); output event/request2 may be opened, next state11 and application length2/buffer MUST stay shared"
        (TlsPostHandshake.core Signal.Word64.symbolic ByteAuth.symbolic
          (ByteCircuit.inputBytes 0 11) (ByteCircuit.inputBytes 11 (4+size))))
  | ["tls-parse-inner", size] =>
      let size ← number size
      if size == 0 || size > 1024 then
        throw (IO.userError "TLS inner-parser export accepts 1..1024 secret bytes")
      emitJson (dagImageOf "tls-parse-inner" size
        "TLSInnerPlaintext; output secret acceptance (255/0), type, two-byte content length, fixed-size content buffer; rejection zeros all outputs; authentication is separate"
        (TlsInnerParallel.decode ByteAuth.symbolic (ByteCircuit.inputBytes 0 size)))
  | ["tls-open-record", size] =>
      let size ← number size
      if size < 22 || size > 1045 then
        throw (IO.userError "TLS full-record export accepts 22..1045 wire bytes (1..1024 ciphertext bytes)")
      emitJson (dagImageOf "tls-open-record" (36 + size)
        "16-byte AES key, 12-byte IV, 8-byte reserved sequence, complete TLSCiphertext record including header and tag; output secret acceptance, type, two-byte content length, fixed-size content buffer; header/tag/type failure zeros all outputs; connection state policy remains caller's responsibility"
        (TlsReceive.openCore Gcm.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)
          (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8) (ByteCircuit.inputBytes 36 size)))
  | ["tls-open-handshake-record", size] =>
      let size ← number size
      if size < 22 || size > 16645 then
        throw (IO.userError "TLS handshake wire size must be 22..16645")
      emitJson (dagImageOf "tls-open-handshake-record" (36 + size)
        "16-byte server handshake key, 12-byte IV, 8-byte sequence, complete record; only authenticated handshake/alert metadata may be released; application data is zeroed inside the circuit"
        (TlsPublicHandshake.openCore Gcm.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)
          (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8) (ByteCircuit.inputBytes 36 size)))
  | ["tls-seal-record", kind, contentSize, padding] =>
      let kind ← number kind
      let contentSize ← number contentSize
      let padding ← number padding
      checkSize contentSize padding
      unless kind == 21 || kind == 22 || kind == 23 do
        throw (IO.userError "protected TLS content type must be alert (21), handshake (22), or application_data (23)")
      if kind != 23 && contentSize == 0 then
        throw (IO.userError "empty handshake/alert records are forbidden")
      if contentSize + padding > 1024 then
        throw (IO.userError "TLS record export resource limit is 1024 content plus padding bytes")
      emitJson (dagImageOf "tls-seal-record" (36 + contentSize)
        "16-byte AES key, 12-byte IV, 8-byte reserved sequence in network order, content; output complete TLSCiphertext record"
        (TlsRecord.sealCore Gcm.symbolic (ByteCircuit.inputBytes 0 16)
          (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8)
          (ByteCircuit.inputBytes 36 contentSize) kind padding))
  | ["tls-open-inner", contentSize] =>
      let contentSize ← number contentSize
      if contentSize == 0 || contentSize > 1024 then
        throw (IO.userError "TLS inner-opening export accepts 1..1024 ciphertext bytes plus a separate 16-byte tag")
      emitJson (dagImageOf "tls-open-inner" (52 + contentSize)
        "16-byte AES key, 12-byte IV, 8-byte sequence, ciphertext, 16-byte tag; caller checks canonical public header; output secret acceptance byte then TLSInnerPlaintext, zeroed on rejection; inner type/padding still require validation"
        (TlsRecord.openInner Gcm.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)
          (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8)
          (ByteCircuit.inputBytes 36 contentSize) (ByteCircuit.inputBytes (36 + contentSize) 16)).bytes)
  | ["gcm-open", aadSize, contentSize] =>
      let aadSize ← number aadSize
      let contentSize ← number contentSize
      if aadSize > 1024 || contentSize > 1024 then
        throw (IO.userError "GCM export resource limit is 1024 bytes per AAD/content input")
      emitJson (dagImageOf "gcm-open" (44 + aadSize + contentSize)
        "16-byte AES key, 12-byte nonce, AAD, ciphertext, 16-byte tag; output secret acceptance byte (255 or 0) then plaintext, zeroed on rejection"
        (GcmOpen.openCore Gcm.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)
          (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 aadSize)
          (ByteCircuit.inputBytes (28 + aadSize) contentSize)
          (ByteCircuit.inputBytes (28 + aadSize + contentSize) 16)).bytes)
  | ["gcm-seal", aadSize, contentSize] =>
      let aadSize ← number aadSize
      let contentSize ← number contentSize
      if aadSize > 1024 || contentSize > 1024 then
        throw (IO.userError "GCM export resource limit is 1024 bytes per AAD/content input")
      emitJson (dagImageOf "gcm-seal" (28 + aadSize + contentSize)
        "16-byte AES key, 12-byte nonce, AAD, content; output ciphertext followed by 16-byte tag"
        (Gcm.sealCore Gcm.symbolic (ByteCircuit.inputBytes 0 16)
          (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 aadSize)
          (ByteCircuit.inputBytes (28 + aadSize) contentSize)).bytes)
  | ["aes128-block"] =>
      emitJson (dagImageOf "aes128-block" 32
        "16-byte AES key then 16-byte plaintext block; output 16-byte ciphertext, all in standard byte order"
        (Aes.encryptCore Aes.symbolic 4 10 (ByteCircuit.inputBytes 0 16) (ByteCircuit.inputBytes 16 16)))
  | ["aes256-block"] =>
      emitJson (dagImageOf "aes256-block" 48
        "32-byte AES key then 16-byte plaintext block; output 16-byte ciphertext, all in standard byte order"
        (Aes.encryptCore Aes.symbolic 8 14 (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 16)))
  | ["aes128-decrypt-block"] =>
      emitJson (dagImageOf "aes128-decrypt-block" 32
        "16-byte AES key then 16-byte ciphertext block; output 16-byte plaintext, all in standard byte order"
        (AesInverse.decryptCore AesInverse.symbolic 4 10 (ByteCircuit.inputBytes 0 16) (ByteCircuit.inputBytes 16 16)))
  | ["aes256-decrypt-block"] =>
      emitJson (dagImageOf "aes256-decrypt-block" 48
        "32-byte AES key then 16-byte ciphertext block; output 16-byte plaintext, all in standard byte order"
        (AesInverse.decryptCore AesInverse.symbolic 8 14 (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 16)))
  | ["sha256", size] =>
      let size ← number size
      if size > 4096 then throw (IO.userError "SHA-256 export resource limit is 4096 bytes")
      emitJson (dagImageOf "sha256" size "message bytes in network order"
        (Sha256.hash Sha256.symbolic (ByteCircuit.inputBytes 0 size)))
  | ["hmac-sha256", keySize, messageSize] =>
      let keySize ← number keySize
      let messageSize ← number messageSize
      if keySize > 4096 || messageSize > 4096 then
        throw (IO.userError "HMAC export resource limit is 4096 bytes per input")
      emitJson (dagImageOf "hmac-sha256" (keySize + messageSize)
        "key bytes followed by message bytes, all in network order"
        (Sha256.hmac Sha256.symbolic (ByteCircuit.inputBytes 0 keySize)
          (ByteCircuit.inputBytes keySize messageSize)))
  | ["hkdf-sha256", saltSize, ikmSize, infoSize, outSize] =>
      let saltSize ← number saltSize
      let ikmSize ← number ikmSize
      let infoSize ← number infoSize
      let outSize ← number outSize
      if saltSize > 4096 || ikmSize > 4096 || infoSize > 4096 || outSize > 128 then
        throw (IO.userError "HKDF export limits: 4096 input bytes per value, 128 output bytes")
      let salt := ByteCircuit.inputBytes 0 saltSize
      let ikm := ByteCircuit.inputBytes saltSize ikmSize
      let info := ByteCircuit.inputBytes (saltSize + ikmSize) infoSize
      let prk := TlsKdf.extract Sha256.symbolic salt ikm
      emitJson (dagImageOf "hkdf-sha256" (saltSize + ikmSize + infoSize)
        "salt, IKM, info bytes; output is PRK followed by OKM, all in network order"
        (prk ++ TlsKdf.expandFast Sha256.symbolic prk info outSize))
  | ["tls-expand-label", label, contextSize, outSize] =>
      let contextSize ← number contextSize
      let outSize ← number outSize
      if label.isEmpty || label.utf8ByteSize > 249 || contextSize > 255 || outSize > 128 then
        throw (IO.userError "invalid TLS label/context size, or export output exceeds 128 bytes")
      if label.toUTF8.data.any (fun byte => byte.toNat > 127) then
        throw (IO.userError "TLS label must be ASCII")
      emitJson (dagImageOf "tls-expand-label" (32 + contextSize)
        "32-byte secret followed by context bytes; output in network order"
        (TlsKdf.expandLabelFast Sha256.symbolic (ByteCircuit.inputBytes 0 32) label
          (ByteCircuit.inputBytes 32 contextSize) outSize))
  | ["tls-handshake-secrets"] =>
      let secrets := TlsKdf.handshakeSecretsFast Sha256.symbolic
        (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)
      emitJson (dagImageOf "tls-handshake-secrets" 64
        "ECDHE result then hello transcript hash; output handshake, client/server handshake traffic, main secrets"
        (secrets.handshake ++ secrets.client ++ secrets.server ++ secrets.main))
  | ["tls-application-secrets"] =>
      let secrets := TlsKdf.applicationSecretsFast Sha256.symbolic
        (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)
      emitJson (dagImageOf "tls-application-secrets" 64
        "main secret then server-Finished transcript hash; output client then server application traffic secrets"
        (secrets.1 ++ secrets.2))
  | ["tls-traffic-keys"] =>
      let keys := TlsKdf.trafficKeysFast Sha256.symbolic (ByteCircuit.inputBytes 0 32)
      emitJson (dagImageOf "tls-traffic-keys" 32
        "32-byte traffic secret; output 16-byte AES key followed by 12-byte IV" (keys.1 ++ keys.2))
  | ["tls-finished"] =>
      emitJson (dagImageOf "tls-finished" 64
        "32-byte traffic secret then 32-byte transcript hash; output 32-byte verify_data"
        (TlsKdf.finished Sha256.symbolic (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)))
  | ["tls-verify-finished"] =>
      emitJson (dagImageOf "tls-verify-finished" 100
        "32-byte traffic secret, 32-byte correctly assembled transcript hash, complete 36-byte received Finished message; output secret acceptance (255/0); certificate/signature and connection-state validation are separate"
        [TlsHandshake.verifyHash Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 32)
          (ByteCircuit.inputBytes 32 32) (ByteCircuit.inputBytes 64 36)])
  | ["tls-verify-finished-transcript", size] =>
      let size ← number size
      if size > 4096 then throw (IO.userError "TLS transcript export resource limit is 4096 bytes")
      emitJson (dagImageOf "tls-verify-finished-transcript" (68 + size)
        "32-byte traffic secret, complete encoded handshake transcript excluding this Finished and record headers, received Finished (36 bytes); output secret acceptance; transcript ordering, certificate/signature and connection-state validation are separate"
        [TlsHandshake.verifyTranscript Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 32)
          (ByteCircuit.inputBytes 32 size) (ByteCircuit.inputBytes (32 + size) 36)])
  | ["tls-retry-transcript-hash", helloSize, retrySize, followingSize] =>
      let helloSize ← number helloSize
      let retrySize ← number retrySize
      let followingSize ← number followingSize
      if helloSize > 4096 || retrySize > 4096 || followingSize > 4096 then
        throw (IO.userError "TLS retry transcript export resource limit is 4096 bytes per input")
      emitJson (dagImageOf "tls-retry-transcript-hash" (helloSize + retrySize + followingSize)
        "complete ClientHello1 encoding, HelloRetryRequest encoding, following encoded handshakes; output SHA256(message_hash framing of SHA256(ClientHello1) || retry || following); parsing, negotiation and transcript ordering are separate"
        (TlsHandshake.retryHash Sha256.symbolic (ByteCircuit.inputBytes 0 helloSize)
          (ByteCircuit.inputBytes helloSize retrySize) (ByteCircuit.inputBytes (helloSize + retrySize) followingSize)))
  | ["tls-update-traffic"] =>
      emitJson (dagImageOf "tls-update-traffic" 32
        "32-byte traffic secret; output next 32-byte traffic secret"
        (TlsKdf.updateTraffic Sha256.symbolic (ByteCircuit.inputBytes 0 32)))
  | ["signal-derive-keys"] =>
      let step := Signal.Symmetric.deriveFast Sha256.symbolic
        (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)
      emitJson (dagImageOf "signal-derive-keys" 64
        "32-byte chain key then 32-byte SPQR salt; output next chain key, cipher key, MAC key, IV"
        step.bytes)
  | ["signal-cbc-encrypt", size] =>
      let size ← number size
      if size > 1024 then throw (IO.userError "Signal CBC export resource limit is 1024 plaintext bytes")
      emitJson (dagImageOf "signal-cbc-encrypt" (48 + size)
        "32-byte AES key, 16-byte IV, plaintext; output AES256-CBC ciphertext with full PKCS7 padding"
        (Signal.Cbc.encryptCore Aes.symbolic (ByteCircuit.inputBytes 0 32)
          (ByteCircuit.inputBytes 32 16) (ByteCircuit.inputBytes 48 size)))
  | ["signal-cbc-open", size] =>
      let size ← number size
      if size == 0 || size > 1024 || size % 16 != 0 then
        throw (IO.userError "Signal CBC opening requires 16..1024 ciphertext bytes, a multiple of 16")
      emitJson (dagImageOf "signal-cbc-open" (48 + size)
        "32-byte AES key, 16-byte IV, ciphertext; output secret acceptance, eight-byte content length, fixed-size plaintext buffer; strict PKCS7 rejection zeros all outputs; MAC authentication is separate"
        (Signal.CbcOpen.openCore AesInverse.symbolic ByteAuth.symbolic
          (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 16) (ByteCircuit.inputBytes 48 size)))
  | ["signal-message-mac", size] =>
      let size ← number size
      if size > 1024 then throw (IO.userError "Signal MAC export resource limit is 1024 message-content bytes")
      emitJson (dagImageOf "signal-message-mac" (96 + size)
        "32-byte MAC key, sender raw identity key (32), receiver raw identity key (32), serialized message content; output eight-byte Signal MAC including identity serialization prefixes"
        (Signal.MessageMac.tag Sha256.symbolic (ByteCircuit.inputBytes 0 32)
          (ByteCircuit.inputBytes 32 32) (ByteCircuit.inputBytes 64 32) (ByteCircuit.inputBytes 96 size)))
  | ["signal-open-span", wireSize, ciphertextOffset, ciphertextSize, addressesOffset] =>
      let wireSize ← number wireSize
      let ciphertextOffset ← number ciphertextOffset
      let ciphertextSize ← number ciphertextSize
      let addressesOffset ← if addressesOffset == "none" then pure none else some <$> number addressesOffset
      let layout : Signal.Receive.Layout := ⟨ciphertextOffset, ciphertextSize, addressesOffset⟩
      let addressSize := if addressesOffset.isSome then 36 else 0
      if wireSize > 1024 || !(decide (layout.valid wireSize addressSize)) then
        throw (IO.userError "invalid Signal serialized-span layout or wire input exceeds 1024 bytes")
      emitJson (dagImageOf "signal-open-span" (144 + wireSize + addressSize)
        "cipher key (32), IV (16), MAC key (32), raw sender and receiver identity keys (32 each), one serialized wire message including final eight-byte MAC, optional expected addresses (36); output secret acceptance, eight-byte length and fixed-size plaintext buffer; rejection zeros all fields; caller must establish protobuf field offsets/presence inside MPC before general use"
        (Signal.Receive.openCore AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic layout
          (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 16) (ByteCircuit.inputBytes 48 32)
          (ByteCircuit.inputBytes 80 32) (ByteCircuit.inputBytes 112 32) (ByteCircuit.inputBytes 144 wireSize)
          (ByteCircuit.inputBytes (144 + wireSize) addressSize)))
  | ["signal-clamp"] =>
      emitJson (dagImageOf "signal-clamp" 32
        "32 scalar bytes in their original order; output applies Curve25519 clamp masks without field reduction"
        (Signal.Clamp.symbolic (ByteCircuit.inputBytes 0 32)))
  | ["signal-unpad16"] =>
      emitJson (dagImageOf "signal-unpad16" 16
        "16 secret padded bytes; output secret acceptance mask, retained length, and 16 retained-or-zero bytes"
        (Signal.Unpad.decode ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)))
  | ["signal-service-id"] =>
      emitJson (dagImageOfWidths "signal-service-id" (#[1] ++ Array.replicate 16 8)
        "secret ACI/PNI kind bit, then 16 secret UUID bytes; output fixed-width 17-byte service identifier"
        (Signal.ServiceId.symbolic (.var 0) (ByteCircuit.inputBytes 1 16)))
  | ["signal-service-id-kind"] =>
      emitJson (dagImageOf "signal-service-id-kind" 1
        "one secret tag byte; output secret acceptance byte (1 or 0), then original tag; valid tags 0 and 1"
        (Signal.Tag.symbolic [0, 1] (.var 0)))
  | ["signal-ciphertext-message-type"] =>
      emitJson (dagImageOf "signal-ciphertext-message-type" 1
        "one secret tag byte; output secret acceptance byte (1 or 0), then original tag; valid tags 2, 3, 7 and 8"
        (Signal.Tag.symbolic [2, 3, 7, 8] (.var 0)))
  | _ => emitSmall args
where
 emitSmall (args : List String) : IO Unit := do
  let image ← match args with
    | ["tls-nonce"] => pure (imageOf "tls-nonce"
        "96 IV bits, then 64 sequence bits, each least-significant bit first; output is network bit order"
        Tls13.nonceCircuit)
    | ["tls-inner", size, padding] => do
        let size ← number size
        let padding ← number padding
        checkSize size padding
        pure (imageOf "tls-inner" "content in network bit order; public content type is application_data (23)"
          (Tls13.innerCircuit size 23 padding))
    | ["tls-header", size, padding] => do
        let size ← number size
        let padding ← number padding
        checkSize size padding
        pure (imageOf "tls-header" "no secret inputs; public AES-GCM tag length is 16 bytes"
          (Tls13.headerCircuit (size + 1 + padding + 16)))
    | ["authenticated-release", size] => do
        let size ← number size
        if size > 16384 then throw (IO.userError "release buffer too large")
        pure (imageOf "authenticated-release" "one validity bit, then the content in network bit order"
          (releaseCircuit (8 * size)))
    | _ => throw (IO.userError
        "usage: emit_mpc signal-keccak MODE INPUT OUTPUT | signal-mlkem arithmetic|cbd|noise ETA | signal-mlkem-ntt forward|inverse|multiply | signal-mlkem-poly add|sub | signal-mlkem-encoding MODE WIDTH | signal-mlkem-sample sample|matrix COUNT PAIRS | signal-kem-wire MODE VARIANT | signal-receiver-store lookup|replace|insert CHAINS SKIPS | signal-retained-receive|signal-session-receive JUMP CHAINS SKIPS SIZE | signal-bounded-receive JUMP CAPACITY SIZE | signal-receive-advance|signal-receive-committed JUMP CAPACITY | signal-skipped-receive CAPACITY SIZE | signal-skipped-consume|signal-skipped-insert CAPACITY | signal-protobuf-parse|signal-protobuf-receive|signal-chain-receive SIZE | signal-pqxdh none|present | signal-serialize|signal-send|signal-chain-send SIZE PQ_SIZE COUNTER_WIDTH PREVIOUS_WIDTH none|present | signal-spqr-chain | signal-spqr-message EPOCH_WIDTH INDEX_WIDTH CHUNK_WIDTH none|present | signal-spqr-send SIZE COUNTER_WIDTH PREVIOUS_WIDTH EPOCH_WIDTH INDEX_WIDTH CHUNK_WIDTH none|present none|present | signal-spqr-decode|signal-spqr-decode-at|signal-spqr-parse SIZE | signal-spqr-epoch-new | signal-spqr-epoch-add | signal-dh-ratchet | signal-ratchet-step | signal-new-ratchet-receive JUMP CAPACITY SIZE | signal-dh-field | tls-route-application CAPACITY | tls-post-handshake CAPACITY | tls-open-application-record WIRE_SIZE | tls-parse-inner SIZE | tls-open-record WIRE_SIZE | tls-verify-finished | tls-verify-finished-transcript SIZE | tls-retry-transcript-hash HELLO_SIZE RETRY_SIZE FOLLOWING_SIZE | aes128-decrypt-block | aes256-decrypt-block | signal-cbc-open SIZE | signal-message-mac SIZE | signal-open-span WIRE_SIZE CT_OFFSET CT_SIZE ADDR_OFFSET_OR_none | tls-seal-record KIND CONTENT_SIZE PADDING | tls-open-inner CIPHERTEXT_SIZE | gcm-seal AAD_SIZE CONTENT_SIZE | gcm-open AAD_SIZE CONTENT_SIZE | aes128-block | aes256-block | sha256 SIZE | hmac-sha256 KEY_SIZE MESSAGE_SIZE | hkdf-sha256 SALT_SIZE IKM_SIZE INFO_SIZE OUTPUT_SIZE | tls-expand-label LABEL CONTEXT_SIZE OUTPUT_SIZE | tls-handshake-secrets | tls-application-secrets | tls-traffic-keys | tls-finished | tls-update-traffic | signal-derive-keys | signal-cbc-encrypt SIZE | signal-clamp | signal-unpad16 | signal-service-id | signal-service-id-kind | signal-ciphertext-message-type | tls-nonce | tls-inner SIZE PADDING | tls-header SIZE PADDING | authenticated-release SIZE")
  emitJson image
