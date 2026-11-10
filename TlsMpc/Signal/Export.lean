import TlsMpc.Signal.KemWire
import TlsMpc.Signal.MlKemPoly
import TlsMpc.Signal.SessionReceive
import Lean
import TlsMpc.Signal.SpqrSend
import TlsMpc.Signal.SpqrParseSpec
import TlsMpc.Signal.SpqrEpoch
import TlsMpc.Signal.DhRatchet
import TlsMpc.Signal.ChainReceive
import TlsMpc.Signal.Pqxdh
import TlsMpc.Signal.SkippedReceive
import TlsMpc.Signal.BoundedReceive

/-! Unverified root-CLI transport for completed Signal circuit components.
No host-side secret computation or session-state mutation occurs here. Compiler
proofs and actual-Rust refinements retain their separately documented scopes. -/
namespace TlsMpc.Signal.Export
open Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def imageOf (name : String) (inputs : Nat) (description : String) (bytes : List (BVExpr 8)) : Image :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name, input_bits := 8 * inputs, input_widths := Array.replicate inputs 8,
    nodes := AigExport.exportNodes circuit.aig, outputs, input_description := description }

def emit [Lean.ToJson A] [Lean.FromJson A] [BEq A] (image : A) : IO Unit := do
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := A) with
  | .error message => throw (IO.userError s!"export round-trip failed: {message}")
  | .ok decoded => unless decoded == image do throw (IO.userError "export round-trip changed artifact")
  (← IO.getStdout).putStrLn serialized

def number (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected a nonnegative decimal integer")

def presence (text : String) : IO Bool :=
  match text with
  | "none" => pure false
  | "present" => pure true
  | _ => throw (IO.userError "presence must be none or present")

def fieldNode : FieldDag.Node → Lean.Json
  | .input i => Lean.Json.mkObj [("op", Lean.toJson "input"), ("index", Lean.toJson i)]
  | .const n => Lean.Json.mkObj [("op", Lean.toJson "const"), ("value", Lean.toJson (toString n))]
  | .bin op a b => Lean.Json.mkObj [("op", Lean.toJson (match op with
      | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div")),
      ("left", Lean.toJson a), ("right", Lean.toJson b)]

structure FieldImage where
  format : String := "tls-mpc-field-dag-v1"
  name : String := "x25519"
  modulus : String := toString FieldDag.modulus
  input_count : Nat := 257
  bit_inputs : Array Nat := (List.range 256).toArray
  nodes : Array Lean.Json
  outputs : Array Nat
  input_description : String := "secret scalar bits256 then peer u field element; clamping inside circuit; shared canonical field output feeds Signal KDF via private conversion; actual dalek/full session equivalence remains separate"
  deriving Lean.ToJson, Lean.FromJson, BEq

def slotInputs (start count : Nat) : List (SkippedKeys.Slot (BVExpr 8)) :=
  (List.range count).map (fun i => ({
    valid := .var (start + 69 * i)
    key := fun j => .var (start + 69 * i + 1 + j.val)
    counter := fun j => .var (start + 69 * i + 33 + j.val)
    seed := fun j => .var (start + 69 * i + 37 + j.val) } : SkippedKeys.Slot (BVExpr 8)))

def receiverEntryInput (start skips : Nat) : ReceiverStore.Entry (BVExpr 8) skips :=
  ⟨.var start,fun i => .var (start+1+i.val),fun i => .var (start+33+i.val),fun i => .var (start+65+i.val),
    fun i => ⟨.var (start+69+69*i.val),fun j => .var (start+70+69*i.val+j.val),
      fun j => .var (start+102+69*i.val+j.val),fun j => .var (start+106+69*i.val+j.val)⟩⟩

/-- Returns false only for modes/argument shapes owned by the existing root CLI. -/
def tryRun (args : List String) : IO Bool := do
  match args with
  | ["signal-keccak", mode, size, count] =>
      let size ← number size
      let count ← number count
      if size > 4096 || count > 4096 then throw (IO.userError "Keccak sizes at most4096")
      let (rate, delimiter) ← match mode with
        | "sha3-256" => if count == 32 then pure (136,6) else throw (IO.userError "SHA3-256 output32")
        | "sha3-512" => if count == 64 then pure (72,6) else throw (IO.userError "SHA3-512 output64")
        | "shake128" => pure (168,31)
        | "shake256" => pure (136,31)
        | _ => throw (IO.userError "Keccak mode")
      emit (imageOf s!"signal-keccak-{mode}-{size}-{count}" size "shared Keccak input and digest; public lengths; actual Rust refinement separate"
        (Keccak.hash Keccak.symbolic rate delimiter count (ByteCircuit.inputBytes 0 size)))
      return true
  | ["signal-mlkem", mode, eta] =>
      let eta ← number eta
      unless eta == 2 || eta == 3 do throw (IO.userError "eta2or3")
      unless mode == "arithmetic" || mode == "cbd" || mode == "noise" do throw (IO.userError "ML-KEM arithmetic mode")
      let size := if mode == "arithmetic" then 4 else if mode == "cbd" then 64*eta else 33
      let raw := ByteCircuit.inputBytes 0 size
      let bytes := if mode == "arithmetic" then
          MlKemArithmetic.arithmeticBytes MlKemArithmetic.symbolic Sha256.symbolic
            (Sha256.symbolic.pack (.const 0) (.const 0) (OpenResult.get ByteAuth.symbolic raw 1) (OpenResult.get ByteAuth.symbolic raw 0))
            (Sha256.symbolic.pack (.const 0) (.const 0) (OpenResult.get ByteAuth.symbolic raw 3) (OpenResult.get ByteAuth.symbolic raw 2))
        else if mode == "cbd" then MlKemArithmetic.cbdBytes MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic eta 256 raw
        else MlKemArithmetic.noise MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic Keccak.symbolic eta raw
      emit (imageOf s!"signal-mlkem-{mode}-{eta}" size "shared canonical arithmetic/CBD/noise; public eta; complete KEM composition separate" bytes)
      return true
  | ["signal-mlkem-ntt", mode] =>
      let operation ← match mode with
        | "forward" => pure MlKemNtt.Operation.forward
        | "inverse" => pure MlKemNtt.Operation.inverse
        | "multiply" => pure MlKemNtt.Operation.multiply
        | _ => throw (IO.userError "NTT operation")
      let size := if mode == "multiply" then 1024 else 512
      emit (imageOf s!"signal-mlkem-ntt-{mode}" size "shared canonical LE16 polynomials; forward/inverse/quadratic multiplication"
        (MlKemNtt.run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic operation (ByteCircuit.inputBytes 0 size)))
      return true
  | ["signal-mlkem-poly", mode] =>
      unless mode == "add" || mode == "sub" do throw (IO.userError "polynomial add/sub")
      emit (imageOf s!"signal-mlkem-poly-{mode}" 1024 "shared pair of canonical LE16 polynomials"
        (MlKemPoly.run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic (mode == "sub") (ByteCircuit.inputBytes 0 1024)))
      return true
  | ["signal-mlkem-encoding", mode, width] =>
      let width ← number width
      unless width > 0 && width ≤ 12 do throw (IO.userError "width1..12")
      let operation ← match mode with
        | "encode" => pure MlKemEncoding.Operation.encode
        | "decode" => pure MlKemEncoding.Operation.decode
        | "compress" => pure MlKemEncoding.Operation.compress
        | "decompress" => pure MlKemEncoding.Operation.decompress
        | _ => throw (IO.userError "encoding operation")
      let size := if mode == "encode" || mode == "compress" then 512 else 32*width
      emit (imageOf s!"signal-mlkem-encoding-{mode}-{width}" size "shared LE16 or packed coefficients; compression input canonical0..3328"
        (MlKemEncoding.run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic operation width (ByteCircuit.inputBytes 0 size)))
      return true
  | ["signal-mlkem-sample", mode, count, pairs] =>
      let count ← number count
      let pairs ← number pairs
      unless count ≤ 256 && pairs ≤ 336 do throw (IO.userError "sampling count256,pairs336")
      unless mode == "sample" || mode == "matrix" do throw (IO.userError "sampling mode")
      let size := if mode == "sample" then 3*pairs else 34
      let raw := ByteCircuit.inputBytes 0 size
      let bytes := if mode == "sample" then MlKemSample.run Word64.symbolic ByteAuth.symbolic count pairs raw
        else MlKemSample.matrix Word64.symbolic ByteAuth.symbolic Keccak.symbolic count pairs raw
      emit (imageOf s!"signal-mlkem-sample-{mode}-{count}-{pairs}" size "shared bounded rejection sample; status0 and zeros on budget exhaustion" bytes)
      return true
  | ["signal-kem-wire", mode, variant] =>
      let profile ← match variant with
        | "kyber768" => pure KemWire.Profile.kyber768
        | "kyber1024" => pure KemWire.Profile.kyber1024
        | "mlkem1024" => pure KemWire.Profile.mlkem1024
        | _ => throw (IO.userError "Signal KEM profile")
      let operation ← match mode with
        | "keygen" => pure MlKem.Operation.keygen
        | "encapsulate" => pure MlKem.Operation.encapsulate
        | "decapsulate" => pure MlKem.Operation.decapsulate
        | _ => throw (IO.userError "KEM operation")
      let payload := match operation with
        | .keygen => KemWire.secretSize profile+KemWire.publicSize profile
        | .encapsulate => KemWire.ciphertextSize profile+32
        | .decapsulate => 32
      emit (imageOf s!"signal-kem-wire-{mode}-{variant}" (3+payload) "shared header2,status1,candidate payload; typed framing and rejection gate"
        (KemWire.finishBytes ByteAuth.symbolic profile operation (ByteCircuit.inputBytes 0 (3+payload))))
      return true
  | [mode, size, pqSize, cw, pw, addresses] =>
      unless mode == "signal-serialize" || mode == "signal-send" || mode == "signal-chain-send" do return false
      let size ← number size
      let pqSize ← number pqSize
      let cw ← number cw
      let pw ← number pw
      let hasAddresses ← presence addresses
      let shape : Serialization.Shape := ⟨cw, pw, hasAddresses⟩
      unless shape.valid do throw (IO.userError "counter widths must be 1..5")
      if size > 1024 || pqSize > 1024 then throw (IO.userError "Signal payload sizes must be at most 1024")
      let addressSize := if hasAddresses then 36 else 0
      let co := ByteCircuit.inputBytes 1 4
      let previous := ByteCircuit.inputBytes 5 4
      let ratchet := ByteCircuit.inputBytes 9 32
      if mode == "signal-serialize" then
        emit (imageOf mode (41 + size + pqSize + addressSize)
          "secret version1,counterBE4,previousBE4,ratchet32,ciphertext,PQ,addresses0/36; output secret status then content; public sizes/widths/address presence; rejection zeros all bytes; complete actual Rust constructor refinement remains open"
          (Serialization.encodeCore Sha256.symbolic ByteAuth.symbolic shape (.var 0) co previous ratchet
            (ByteCircuit.inputBytes 41 size) (ByteCircuit.inputBytes (41 + size) pqSize)
            (ByteCircuit.inputBytes (41 + size + pqSize) addressSize)))
      else if mode == "signal-send" then
        emit (imageOf mode (185 + size + pqSize + addressSize)
          "secret version1,counterBE4,previousBE4,ratchet32,cipherKey32,IV16,macKey32,sender32,receiver32,plaintext,PQ,addresses0/36; output status and complete Signal wire; derived keys supplied; session/RustCrypto wrapper obligations separate"
          (Send.sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape (.var 0) co previous ratchet
            (ByteCircuit.inputBytes 41 32) (ByteCircuit.inputBytes 73 16) (ByteCircuit.inputBytes 89 32)
            (ByteCircuit.inputBytes 121 32) (ByteCircuit.inputBytes 153 32)
            (ByteCircuit.inputBytes 185 size) (ByteCircuit.inputBytes (185 + size) pqSize)
            (ByteCircuit.inputBytes (185 + size + pqSize) addressSize)))
      else
        emit (imageOf mode (170 + size + pqSize + addressSize)
          "secret version1,counterBE4,previousBE4,ratchet32,chainKey32,PQpresent0/1,PQkey32,sender32,receiver32,plaintext,PQ,addresses0/36; output status,nextChain32,nextCounter4,Signal wire; rejection preserves old chain and zeros wire; atomic state and full Rust refinement separate"
          (ChainSend.sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape (.var 0) (.var 73)
            co previous ratchet (ByteCircuit.inputBytes 41 32) (ByteCircuit.inputBytes 74 32)
            (ByteCircuit.inputBytes 106 32) (ByteCircuit.inputBytes 138 32)
            (ByteCircuit.inputBytes 170 size) (ByteCircuit.inputBytes (170 + size) pqSize)
            (ByteCircuit.inputBytes (170 + size + pqSize) addressSize)))
      return true
  | ["signal-spqr-chain"] =>
      emit (imageOf "signal-spqr-chain" 36
        "secret chainKey32,counterBE4; output status,nextChain32,nextCounter4,messageKey32; overflow preserves old state and zeroes message key; selected epoch precondition and full HKDF wrapper refinement remain separate"
        (SpqrChain.stepCore Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 4)))
      return true
  | ["signal-spqr-message", ew, iw, kw, chunk] =>
      let ew ← number ew
      let iw ← number iw
      let kw ← number kw
      let hasChunk ← presence chunk
      let shape : SpqrMessage.Shape := ⟨ew, iw, kw, hasChunk⟩
      unless shape.valid do throw (IO.userError "invalid SPQR epoch/index/chunk width profile")
      emit (imageOf "signal-spqr-message" (if hasChunk then 47 else 13)
        "secret epochBE8,indexBE4,kind1,optional chunkIndexBE2+chunkData32; output status and SPQR V1 wire; public encoded widths/chunk presence; only selected varint actual-Rust refinement accepted"
        (SpqrMessage.encodeCore Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape
          (Varint64.pack Varint64.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 8))
          (Varint.pack Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 8 4)) (.var 12)
          (ByteCircuit.inputBytes 13 (if hasChunk then 2 else 0))
          (ByteCircuit.inputBytes 15 (if hasChunk then 32 else 0))))
      return true
  | ["signal-spqr-send", size, cw, pw, ew, iw, kw, chunk, addresses] =>
      let size ← number size
      let cw ← number cw
      let pw ← number pw
      let ew ← number ew
      let iw ← number iw
      let kw ← number kw
      let hasChunk ← presence chunk
      let hasAddresses ← presence addresses
      let shape : Serialization.Shape := ⟨cw, pw, hasAddresses⟩
      let pqShape : SpqrMessage.Shape := ⟨ew, iw, kw, hasChunk⟩
      unless shape.valid ∧ pqShape.valid do throw (IO.userError "invalid public varint-width profile")
      if size > 1024 then throw (IO.userError "Signal plaintext is limited to 1024 bytes")
      let chunkSize := if hasChunk then 34 else 0
      let addressSize := if hasAddresses then 36 else 0
      let input : SpqrSend.Input (BVExpr 8) := {
        version := .var 0, counter := ByteCircuit.inputBytes 1 4,
        previous := ByteCircuit.inputBytes 5 4, ratchet := ByteCircuit.inputBytes 9 32,
        chainKey := ByteCircuit.inputBytes 41 32, pqChainKey := ByteCircuit.inputBytes 73 32,
        pqCounter := ByteCircuit.inputBytes 105 4, epoch := ByteCircuit.inputBytes 109 8,
        kind := .var 117, chunkIndex := ByteCircuit.inputBytes 118 (if hasChunk then 2 else 0),
        chunkData := ByteCircuit.inputBytes 120 (if hasChunk then 32 else 0),
        sender := ByteCircuit.inputBytes (118 + chunkSize) 32,
        receiver := ByteCircuit.inputBytes (150 + chunkSize) 32,
        plaintext := ByteCircuit.inputBytes (182 + chunkSize) size,
        addresses := ByteCircuit.inputBytes (182 + chunkSize + size) addressSize }
      emit (imageOf "signal-spqr-send" (182 + chunkSize + size + addressSize)
        "all secret: version1,SignalCounter4,previous4,ratchet32,SignalChain32,SPQRChain32,SPQRCounter4,epoch8,kind1,chunk0/34,sender32,receiver32,plaintext,addresses0/36; output status,nextSignalChain32,counter4,nextSPQRChain32,counter4,wire; already selected active epoch/payload; full state/Rust refinement and commit remain separate"
        (SpqrSend.sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape input))
      return true
  | ["signal-skipped-receive", count, size] =>
      let count ← number count
      let size ← number size
      if count > 64 || size > 512 then throw (IO.userError "maximum capacity64/wire512")
      emit (imageOf "signal-skipped-receive" (133 + 69 * count + size)
        "secret PQpresence1,PQkey32,sender32,receiver32,expectedAddresses36,slots69N,wire; output status,nextStore,lengthBE8,plaintext; deletion commits only on authenticated receive; seed records only"
        (SkippedReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
          (.var 0) (ByteCircuit.inputBytes 1 32) (ByteCircuit.inputBytes 33 32) (ByteCircuit.inputBytes 65 32)
          (ByteCircuit.inputBytes (133 + 69 * count) size) (ByteCircuit.inputBytes 97 36) (slotInputs 133 count)))
      return true
  | ["signal-bounded-receive", jump, count, size] =>
      let jump ← number jump
      let count ← number count
      let size ← number size
      if jump > 16 || count > 64 || size > 512 then throw (IO.userError "maximum jump16/capacity64/wire512")
      emit (imageOf "signal-bounded-receive" (201 + 69 * count + size)
        "secret PQpresence1,ratchet32,chain32,currentCounter4,PQkey32,sender32,receiver32,addresses36,slots69N,wire; output status,nextChain32,nextCounter4,nextStore,lengthBE8,plaintext; bounded future/skipped transaction; unknownDH/SPQR transitions separate"
        (BoundedReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
          jump (.var 0) (fun i => .var (1 + i.val)) (fun i => .var (33 + i.val)) (fun i => .var (65 + i.val))
          (slotInputs 201 count) (ByteCircuit.inputBytes 69 32) (ByteCircuit.inputBytes 101 32) (ByteCircuit.inputBytes 133 32)
          (ByteCircuit.inputBytes (201 + 69 * count) size) (ByteCircuit.inputBytes 165 36)))
      return true
  | [mode, jump, count] =>
      unless mode == "signal-receive-advance" || mode == "signal-receive-committed" do return false
      let jump ← number jump
      let count ← number count
      if jump > 16 || count > 64 then throw (IO.userError "maximum jump16/capacity64")
      let offset := if mode == "signal-receive-committed" then 1 else 0
      let ratchet := fun (i : Fin 32) => BVExpr.var (offset + i.val)
      let chain := fun (i : Fin 32) => BVExpr.var (offset + 32 + i.val)
      let current := Varint.pack Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes (offset + 64) 4)
      let target := Varint.pack Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes (offset + 68) 4)
      let slots := slotInputs (offset + 72) count
      let selected := if offset == 1 then ReceiveAdvance.committed Sha256.symbolic ByteAuth.symbolic jump (.var 0) ratchet chain current target slots
        else ReceiveAdvance.advance Sha256.symbolic ByteAuth.symbolic jump ratchet chain current target slots
      emit (imageOf s!"{mode}-{jump}-{count}" (offset + 72 + 69 * count)
        "secret optionalauth1,ratchet32,chain32,currentBE4,targetBE4,slots69N; output status,seed32,nextChain32,nextCounter4,nextStore; bounded future derivation with intermediate seeds; complete session separate"
        (ReceiveAdvance.bytes selected))
      return true
  | ["signal-skipped-consume", count] =>
      let count ← number count
      if count > 64 then throw (IO.userError "maximum skipped capacity64")
      emit (imageOf s!"signal-skipped-consume-{count}" (37 + 69 * count)
        "secret auth1,ratchet32,counter4,slots69N; output status,seed32,nextStore; auth must255; first match; failure preserves store"
        (SkippedKeys.consumeBytes ByteAuth.symbolic (.var 0) (fun i => .var (1 + i.val))
          (fun i => .var (33 + i.val)) (slotInputs 37 count)))
      return true
  | ["signal-skipped-insert", count] =>
      let count ← number count
      if count > 64 then throw (IO.userError "maximum skipped capacity64")
      emit (imageOf s!"signal-skipped-insert-{count}" (68 + 69 * count)
        "secret ratchet32,counter4,seed32,slots69N; output newest-first slots69N; oldest evicted"
        (SkippedKeys.storeBytes (SkippedKeys.insertFront ByteAuth.symbolic
          (fun i => .var i.val) (fun i => .var (32 + i.val)) (fun i => .var (36 + i.val)) (slotInputs 68 count))))
      return true
  | ["signal-pqxdh", optional] =>
      let present ← presence optional
      let optionalBytes := if present then 32 else 0
      emit (imageOf ("signal-pqxdh-" ++ optional) (128 + optionalBytes)
        "secret DH1,DH2,DH3,optionalDH4,KyberSS; output root32,chain32,PQR32; KDF component only; Kyber production/identity/prekey validation/full Rust refinement separate"
        (Pqxdh.deriveCore Sha256.symbolic (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)
          (ByteCircuit.inputBytes 64 32) (ByteCircuit.inputBytes 96 optionalBytes)
          (ByteCircuit.inputBytes (96 + optionalBytes) 32)))
      return true
  | ["signal-protobuf-parse", size] =>
      let size ← number size
      if size > 512 then throw (IO.userError "Signal parser supports wire lengths0..512")
      emit (imageOf "signal-protobuf-parse" size
        "secret original wire; output secret status,ratchet32,counters4+4,ciphertext/PQ/address body-relative spans; zeros90 bytes on rejection; general protobuf parse; actual whole-Prost refinement separate"
        (ProtoParse.parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 size)))
      return true
  | ["signal-protobuf-receive", size] =>
      let size ← number size
      if size > 512 then throw (IO.userError "Signal receive supports wire lengths0..512")
      emit (imageOf "signal-protobuf-receive" (180 + size)
        "secret cipherKey32,IV16,macKey32,sender32,receiver32,expectedAddresses36,wire; output status,lengthBE8,paddedplaintext; secret general protobuf layout and exact original-wire authentication; session key selection/commit separate"
        (ProtoReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
          (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 16) (ByteCircuit.inputBytes 48 32)
          (ByteCircuit.inputBytes 80 32) (ByteCircuit.inputBytes 112 32) (ByteCircuit.inputBytes 180 size)
          (ByteCircuit.inputBytes 144 36)))
      return true
  | ["signal-chain-receive", size] =>
      let size ← number size
      if size > 512 then throw (IO.userError "Signal chain receive supports wire lengths0..512")
      emit (imageOf "signal-chain-receive" (201 + size)
        "secret PQpresence1,ratchet32,counter4,chain32,PQkey32,sender32,receiver32,expectedAddresses36,wire; output status,nextChain32,nextCounter4,lengthBE8,plaintext; rejection preserves chain/counter; selected in-order chain only"
        (ChainReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
          (.var 0) (ByteCircuit.inputBytes 1 32) (ByteCircuit.inputBytes 33 4) (ByteCircuit.inputBytes 37 32)
          (ByteCircuit.inputBytes 69 32) (ByteCircuit.inputBytes 101 32) (ByteCircuit.inputBytes 133 32)
          (ByteCircuit.inputBytes 201 size) (ByteCircuit.inputBytes 165 36)))
      return true
  | [mode, size] =>
      unless mode == "signal-spqr-decode" || mode == "signal-spqr-decode-at" || mode == "signal-spqr-parse" do return false
      let size ← number size
      if size > 256 then throw (IO.userError "SPQR parser/decoder export supports wire lengths 0..256")
      if mode == "signal-spqr-decode" then
        emit (imageOf mode size
          "shared bytes; output status255/0,count0..10,valueBE8; rejection zeros10 bytes; accepted actual SPQR varint refinement, including noncanonical/tenth-byte truncation"
          (VarintDecode.Spqr.decodeCore VarintDecode.Spqr.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 size)))
      else if mode == "signal-spqr-decode-at" then
        emit (imageOf mode (8 + size)
          "secret offsetBE8 then wire; output status,newOffsetBE8,valueBE8; rejection preserves offset/zeros value; accepted actual SPQR varint refinement; host indices public"
          (SpqrDecodeAt.decodeCore VarintDecode.Spqr.symbolic ByteAuth.symbolic
            (ByteCircuit.inputBytes 8 size) (ByteCircuit.inputBytes 0 8)))
      else
        emit (imageOf mode size
          "secret V1 wire; only length public; output status,epoch8,index4,kind1,hasChunk0/1,chunkIndex2,data32; all49 bytes zero on rejection; full actual Rust parser refinement remains open; no KEM/state mutation"
          (SpqrParse.parseCore VarintDecode.Spqr.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 size)))
      return true
  | ["signal-spqr-epoch-new"] =>
      emit (imageOf "signal-spqr-epoch-new" 33
        "secret direction0=A2B/1=B2A,initialKey32; output status,root32,epoch8,sendKey32,counter4,recvKey32,counter4; invalid direction zeros113 bytes; KEM/links persistence/full Rust refinement remain separate"
        (SpqrEpoch.newCore Sha256.symbolic ByteAuth.symbolic (.var 0) (ByteCircuit.inputBytes 1 32)))
      return true
  | ["signal-spqr-epoch-add"] =>
      emit (imageOf "signal-spqr-epoch-add" 81
        "secret direction1,root32,currentEpoch8,proposedEpoch8,epochSecret32; output status,root32,epoch8,sendKey32,counter4,recvKey32,counter4; consecutive nonoverflowing check; reject preserves root/epoch,zeros candidate chains; KEM/links commit/full Rust refinement remain separate"
        (SpqrEpoch.addCore SpqrEpoch.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic (.var 0)
          (ByteCircuit.inputBytes 1 32) (ByteCircuit.inputBytes 33 8)
          (ByteCircuit.inputBytes 41 8) (ByteCircuit.inputBytes 49 32)))
      return true
  | ["signal-receiver-store", operation, capacity, skips] =>
      let capacity ← number capacity
      let skips ← number skips
      if capacity > 5 || skips > 64 then throw (IO.userError "receiver store bounds:5chains,64skips")
      let op ← match operation with
        | "lookup" => pure ReceiverStore.Operation.lookup
        | "replace" => pure ReceiverStore.Operation.replace
        | "insert" => pure ReceiverStore.Operation.insert
        | _ => throw (IO.userError "expected lookup,replace,insert")
      let width := 69+69*skips
      let old := (List.range capacity).map (fun i => receiverEntryInput (33+(i+1)*width) skips)
      emit (imageOf s!"signal-receiver-store-{operation}-{capacity}-{skips}" (33+(capacity+1)*width)
        "shared auth1,ratchet32,nextEntry,oldEntries; entry valid1/key32/chain32/counter4/skipped69N; first match and authenticated replace/append-oldest-evict; no disclosures"
        (ReceiverStore.run ByteAuth.symbolic op (.var 0) (fun i => .var (1+i.val)) (receiverEntryInput 33 skips) old))
      return true
  | [mode, jump, chains, skips, size] =>
      unless mode == "signal-retained-receive" || mode == "signal-session-receive" do return false
      let jump ← number jump
      let chains ← number chains
      let skips ← number skips
      let size ← number size
      if jump > 16 || chains > 5 || skips > 64 || size > 512 then throw (IO.userError "receive bounds:jump16,chains5,skips64,wire512")
      if mode == "signal-session-receive" && chains == 0 then throw (IO.userError "session requires at least one receiver slot")
      let width := 69+69*skips
      if mode == "signal-retained-receive" then
        let old := (List.range chains).map (fun i => receiverEntryInput (133+i*width) skips)
        emit (imageOf mode (133+chains*width+size)
          "shared PQpresence1,PQkey32,sender32,receiver32,addresses36,retainedEntries,wire; status,nextEntries,length8,plaintext; secret first-match retained chain and authenticated update"
          (RetainedReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump (.var 0) old
            (ByteCircuit.inputBytes 1 32) (ByteCircuit.inputBytes 33 32) (ByteCircuit.inputBytes 65 32)
            (ByteCircuit.inputBytes (133+chains*width) size) (ByteCircuit.inputBytes 97 36)))
      else
        let oldSender : RatchetStep.State (BVExpr 8) := ⟨ByteCircuit.inputBytes 1 32,ByteCircuit.inputBytes 33 32,
          ByteCircuit.inputBytes 65 32,ByteCircuit.inputBytes 97 32,ByteCircuit.inputBytes 129 4,ByteCircuit.inputBytes 133 4⟩
        let old := (List.range chains).map (fun i => receiverEntryInput (429+i*width) skips)
        emit (imageOf mode (429+chains*width+size)
          "shared PQpresence1,oldSenderState136,freshPair64,agreements64,remote32,PQkey32,sender32,receiver32,addresses36,retainedEntries,wire; status,nextSenderState,nextEntries,length8,plaintext; secret classical session transaction, external SPQR key and mixed X25519 provenance"
          (SessionReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump (.var 0) oldSender old
            (ByteCircuit.inputBytes 137 32) (ByteCircuit.inputBytes 169 32) (ByteCircuit.inputBytes 201 32) (ByteCircuit.inputBytes 233 32)
            (ByteCircuit.inputBytes 265 32) (ByteCircuit.inputBytes 297 32) (ByteCircuit.inputBytes 329 32) (ByteCircuit.inputBytes 361 32)
            (ByteCircuit.inputBytes (429+chains*width) size) (ByteCircuit.inputBytes 393 36)))
      return true
  | ["signal-ratchet-step"] =>
      let old : RatchetStep.State (BVExpr 8) := ⟨ByteCircuit.inputBytes 1 32, ByteCircuit.inputBytes 33 32,
        ByteCircuit.inputBytes 65 32, ByteCircuit.inputBytes 97 32, ByteCircuit.inputBytes 129 4, ByteCircuit.inputBytes 133 4⟩
      emit (imageOf "signal-ratchet-step" 265
        "shared auth1,oldSenderState136,freshPrivate32,freshPublic32,receiveAgreement32,sendAgreement32; status,nextSenderState136,receiverChain32,counter4; two-half step and rollback; agreement/pair provenance external"
        (RatchetStep.step Sha256.symbolic ByteAuth.symbolic (.var 0) old
          (ByteCircuit.inputBytes 137 32) (ByteCircuit.inputBytes 169 32) (ByteCircuit.inputBytes 201 32) (ByteCircuit.inputBytes 233 32)))
      return true
  | ["signal-new-ratchet-receive", jump, count, size] =>
      let jump ← number jump
      let count ← number count
      let size ← number size
      if jump > 16 || count > 64 || size > 512 then throw (IO.userError "new ratchet bounds: jump16,capacity64,wire512")
      let old : RatchetStep.State (BVExpr 8) := ⟨ByteCircuit.inputBytes 1 32, ByteCircuit.inputBytes 33 32,
        ByteCircuit.inputBytes 65 32, ByteCircuit.inputBytes 97 32, ByteCircuit.inputBytes 129 4, ByteCircuit.inputBytes 133 4⟩
      emit (imageOf "signal-new-ratchet-receive" (429 + size)
        "shared PQpresence1,oldSenderState136,freshPrivate32,freshPublic32,receiveAgreement32,sendAgreement32,remote32,PQkey32,sender32,receiver32,addresses36,wire; authenticated two-half first-message transaction; pair/agreement provenance and retained-session selection external"
        (NewRatchetReceive.openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump count (.var 0) old
          (ByteCircuit.inputBytes 137 32) (ByteCircuit.inputBytes 169 32) (ByteCircuit.inputBytes 201 32) (ByteCircuit.inputBytes 233 32)
          (ByteCircuit.inputBytes 265 32) (ByteCircuit.inputBytes 297 32) (ByteCircuit.inputBytes 329 32) (ByteCircuit.inputBytes 361 32)
          (ByteCircuit.inputBytes 429 size) (ByteCircuit.inputBytes 393 36)))
      return true
  | ["signal-dh-ratchet"] =>
      emit (imageOf "signal-dh-ratchet" 64
        "secret root32,canonical shared X25519 agreement32; output status,newRoot32,newChain32,counter4; zero agreement retains old root and zeros chain; actual dalek/HKDF wrappers and complete DH state transition remain separate"
        (DhRatchet.createCore Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32)))
      return true
  | ["signal-dh-field"] =>
      match FieldDag.compile X25519.expr with
      | none => throw (IO.userError "X25519 field compilation failed translation validation")
      | some artifact => emit ({nodes := artifact.nodes.toArray.map fieldNode, outputs := #[artifact.output]} : FieldImage)
      return true
  | _ => return false

end TlsMpc.Signal.Export
