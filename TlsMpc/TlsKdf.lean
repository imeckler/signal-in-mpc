import TlsMpc.ByteCircuit

/-!
SHA-256 HKDF (RFC 5869 §2) and TLS 1.3 key derivation (RFC 9846 §§4.5.3,
7.1–7.3). This is the TLS_AES_128_GCM_SHA256 profile. The transcript hashes and
ECDHE result are secret byte inputs; this does not authenticate a handshake or
implement ECDHE. `expand` and `expandLabel` reject invalid public lengths.
Internal `*Core` functions have public preconditions enforced by their callers.
-/

namespace TlsMpc.TlsKdf

open Std.Tactic.BVDecide Sha256

def zeros (o : Ops B W) (n : Nat) : List B := List.replicate n (o.byteConst 0)

def extract (o : Ops B W) (salt ikm : List B) : List B :=
  hmac o (if salt.isEmpty then zeros o 32 else salt) ikm

def expandBlocks (o : Ops B W) (prk info : List B) : Nat → Nat → List B → List B
  | 0, _, _ => []
  | n + 1, counter, previous =>
      let current := hmac o prk (previous ++ info ++ [o.byteConst counter])
      current ++ expandBlocks o prk info n (counter + 1) current

def expandCore (o : Ops B W) (prk info : List B) (length : Nat) : List B :=
  (expandBlocks o prk info ((length + 31) / 32) 1 []).take length

def expand (o : Ops B W) (prk info : List B) (length : Nat) : Option (List B) :=
  if length ≤ 255 * 32 then some (expandCore o prk info length) else none

def ascii (text : String) : List Nat := text.toUTF8.data.toList.map UInt8.toNat

/-- RFC 9846 HkdfLabel, including its two-byte length and both vector lengths. -/
def labelInfo (o : Ops B W) (label : List Nat) (context : List B) (length : Nat) : List B :=
  [o.byteConst (length / 256), o.byteConst length, o.byteConst (6 + label.length)] ++
    (ascii "tls13 " ++ label).map o.byteConst ++ [o.byteConst context.length] ++ context

def expandLabelCore (o : Ops B W) (secret : List B) (label : String)
    (context : List B) (length : Nat) : List B :=
  expandCore o secret (labelInfo o (ascii label) context length) length

def expandLabel (o : Ops B W) (secret : List B) (label : List Nat)
    (context : List B) (length : Nat) : Option (List B) :=
  if 1 ≤ label.length ∧ label.length ≤ 249 ∧ context.length ≤ 255 ∧
      (∀ byte ∈ label, byte < 256) ∧ length ≤ 255 * 32 then
    some (expandCore o secret (labelInfo o label context length) length)
  else none

/-- `transcriptHash` has 32 bytes. The empty transcript is hashed, not represented
by an empty context. Traffic key/IV labels instead use the empty context. -/
def deriveSecret (o : Ops B W) (secret : List B) (label : String)
    (transcriptHash : List B) : List B :=
  expandLabelCore o secret label transcriptHash 32

structure HandshakeSecrets (B : Type) where
  handshake : List B
  client : List B
  server : List B
  main : List B

def HandshakeSecrets.map (f : B → B') (s : HandshakeSecrets B) : HandshakeSecrets B' :=
  ⟨s.handshake.map f, s.client.map f, s.server.map f, s.main.map f⟩

/-- No PSK: ECDHE result and ClientHello..ServerHello transcript hash are 32 bytes. -/
def handshakeSecrets (o : Ops B W) (ecdhe helloHash : List B) : HandshakeSecrets B :=
  let early := extract o (zeros o 32) (zeros o 32)
  let emptyHash := hash o []
  let handshake := extract o (deriveSecret o early "derived" emptyHash) ecdhe
  ⟨handshake, deriveSecret o handshake "c hs traffic" helloHash,
    deriveSecret o handshake "s hs traffic" helloHash,
    extract o (deriveSecret o handshake "derived" emptyHash) (zeros o 32)⟩

def applicationSecrets (o : Ops B W) (mainSecret serverFinishedHash : List B) : List B × List B :=
  (deriveSecret o mainSecret "c ap traffic" serverFinishedHash,
    deriveSecret o mainSecret "s ap traffic" serverFinishedHash)

def trafficKeys (o : Ops B W) (trafficSecret : List B) : List B × List B :=
  (expandLabelCore o trafficSecret "key" [] 16, expandLabelCore o trafficSecret "iv" [] 12)

def finished (o : Ops B W) (trafficSecret transcriptHash : List B) : List B :=
  hmac o (expandLabelCore o trafficSecret "finished" [] 32) transcriptHash

def updateTraffic (o : Ops B W) (trafficSecret : List B) : List B :=
  expandLabelCore o trafficSecret "traffic upd" [] 32

theorem expandBlocks_length (o : Ops B W) (prk info : List B) (n counter : Nat) (previous : List B) :
    (expandBlocks o prk info n counter previous).length = 32 * n := by
  induction n generalizing counter previous with
  | zero => rfl
  | succ n ih => simp only [expandBlocks, List.length_append, hmac_length, ih]; omega

theorem expandCore_length (o : Ops B W) (prk info : List B) (length : Nat) :
    (expandCore o prk info length).length = length := by
  simp only [expandCore, List.length_take, expandBlocks_length]
  omega

theorem expand_exhausted (o : Ops B W) (prk info : List B) (length : Nat)
    (h : 255 * 32 < length) : expand o prk info length = none := by
  simp [expand, Nat.not_le_of_gt h]

section Refinement

variable {a : Ops B W} {b : Ops B' W'} {fb : B → B'} {fw : W → W'}
variable (h : Hom a b fb fw)
include h

theorem zeros_map (n : Nat) : (zeros a n).map fb = zeros b n := by
  simp [zeros, h.byteConst]

theorem extract_map (salt ikm : List B) :
    (extract a salt ikm).map fb = extract b (salt.map fb) (ikm.map fb) := by
  simp only [extract, hmac_map h, List.isEmpty_map]
  split <;> simp [zeros_map h]

theorem expandBlocks_map (prk info : List B) (n counter : Nat) (previous : List B) :
    (expandBlocks a prk info n counter previous).map fb =
      expandBlocks b (prk.map fb) (info.map fb) n counter (previous.map fb) := by
  induction n generalizing counter previous with
  | zero => rfl
  | succ n ih =>
      simp only [expandBlocks, List.map_append, hmac_map h, List.map_cons, List.map_nil,
        h.byteConst, ih]

theorem expandCore_map (prk info : List B) (length : Nat) :
    (expandCore a prk info length).map fb = expandCore b (prk.map fb) (info.map fb) length := by
  simp only [expandCore, List.map_take, expandBlocks_map h, List.map_nil]

theorem expand_map (prk info : List B) (length : Nat) :
    (expand a prk info length).map (List.map fb) = expand b (prk.map fb) (info.map fb) length := by
  simp only [expand]
  split <;> simp [expandCore_map h]

theorem labelInfo_map (label : List Nat) (context : List B) (length : Nat) :
    (labelInfo a label context length).map fb = labelInfo b label (context.map fb) length := by
  simp [labelInfo, List.map_map, Function.comp_def, h.byteConst]

theorem expandLabelCore_map (secret : List B) (label : String) (context : List B) (length : Nat) :
    (expandLabelCore a secret label context length).map fb =
      expandLabelCore b (secret.map fb) label (context.map fb) length := by
  simp only [expandLabelCore, expandCore_map h, labelInfo_map h]

theorem expandLabel_map (secret : List B) (label : List Nat) (context : List B) (length : Nat) :
    (expandLabel a secret label context length).map (List.map fb) =
      expandLabel b (secret.map fb) label (context.map fb) length := by
  simp only [expandLabel, List.length_map]
  split <;> simp [expandCore_map h, labelInfo_map h]

theorem deriveSecret_map (secret : List B) (label : String) (transcript : List B) :
    (deriveSecret a secret label transcript).map fb =
      deriveSecret b (secret.map fb) label (transcript.map fb) := by
  exact expandLabelCore_map h secret label transcript 32

theorem handshakeSecrets_map (ecdhe helloHash : List B) :
    (handshakeSecrets a ecdhe helloHash).map fb =
      handshakeSecrets b (ecdhe.map fb) (helloHash.map fb) := by
  simp only [handshakeSecrets, HandshakeSecrets.map, extract_map h,
    deriveSecret_map h, zeros_map h, hash_map h, List.map_nil]

theorem trafficKeys_map (secret : List B) :
    ((trafficKeys a secret).1.map fb, (trafficKeys a secret).2.map fb) =
      trafficKeys b (secret.map fb) := by
  simp only [trafficKeys, expandLabelCore_map h, List.map_nil]

theorem applicationSecrets_map (secret transcript : List B) :
    ((applicationSecrets a secret transcript).1.map fb,
      (applicationSecrets a secret transcript).2.map fb) =
      applicationSecrets b (secret.map fb) (transcript.map fb) := by
  simp only [applicationSecrets, deriveSecret_map h]

theorem finished_map (secret transcript : List B) :
    (finished a secret transcript).map fb = finished b (secret.map fb) (transcript.map fb) := by
  simp only [finished, hmac_map h, expandLabelCore_map h, List.map_nil]

theorem updateTraffic_map (secret : List B) :
    (updateTraffic a secret).map fb = updateTraffic b (secret.map fb) := by
  simp only [updateTraffic, expandLabelCore_map h, List.map_nil]

end Refinement

theorem compiled_expandLabel_correct (secret context : List (BVExpr 8)) (label : String)
    (length : Nat) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (expandLabelCore symbolic secret label context length).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (expandLabelCore symbolic secret label context length))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (expandLabelCore symbolic secret label context length))).vec.get index hi)) =
    (ByteCircuit.joinValue (expandLabelCore concrete (secret.map (BVExpr.eval assign)) label
      (context.map (BVExpr.eval assign)) length)).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expandLabelCore_map (evaluationHom assign)]

end TlsMpc.TlsKdf
