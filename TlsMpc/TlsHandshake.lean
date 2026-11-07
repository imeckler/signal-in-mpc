import TlsMpc.TlsKdf
import TlsMpc.ByteAuth

/-!
TLS 1.3 transcript and Finished computations for SHA-256, RFC 9846 sections
4.1 and 4.5.3. Transcript bytes contain complete handshake encodings (including
their four-byte headers), excluding record headers and the Finished being
verified. Parsing, transcript ordering, certificate/signature validation and
connection state are separate obligations. The verifier returns a SECRET
255/0 mask; a successful Finished alone does not authenticate a server.
-/

namespace TlsMpc.TlsHandshake
open Std.Tactic.BVDecide

def frame (s : Sha256.Ops B W) (kind : Nat) (body : List B) : List B :=
  [s.byteConst kind, s.byteConst (body.length / 65536),
    s.byteConst (body.length / 256), s.byteConst body.length] ++ body

def frameChecked (s : Sha256.Ops B W) (kind : Nat) (body : List B) : Option (List B) :=
  if kind < 256 ∧ body.length < 2 ^ 24 then some (frame s kind body) else none

/-- The replacement of ClientHello1 by the synthetic message_hash handshake
encoding is mandatory in a HelloRetryRequest transcript. Inputs are complete
ClientHello1 and HelloRetryRequest encodings, followed by later handshakes. -/
def retryTranscript (s : Sha256.Ops B W) (clientHello1 retry following : List B) : List B :=
  frame s 254 (Sha256.hash s clientHello1) ++ retry ++ following

def retryHash (s : Sha256.Ops B W) (clientHello1 retry following : List B) : List B :=
  Sha256.hash s (retryTranscript s clientHello1 retry following)

def finishedMessage (s : Sha256.Ops B W) (secret transcriptHash : List B) : List B :=
  frame s 20 (TlsKdf.finished s secret transcriptHash)

def verifyHash (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (secret transcriptHash receivedMessage : List B) : B :=
  ByteAuth.equalMask a (finishedMessage s secret transcriptHash) receivedMessage

def verifyTranscript (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (secret transcript receivedMessage : List B) : B :=
  verifyHash s a secret (Sha256.hash s transcript) receivedMessage

def verifyChecked (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (secret transcript receivedMessage : List B) : Option B :=
  if secret.length = 32 ∧ transcript.length < 2 ^ 61 ∧ receivedMessage.length = 36 then
    some (verifyTranscript s a secret transcript receivedMessage)
  else none

def spec (secret transcript receivedMessage : List (BitVec 8)) : BitVec 8 :=
  if finishedMessage Sha256.concrete secret (Sha256.hash Sha256.concrete transcript) = receivedMessage
  then 255 else 0

theorem frame_length (s : Sha256.Ops B W) (kind : Nat) (body : List B) :
    (frame s kind body).length = body.length + 4 := by simp [frame]

theorem finishedMessage_length (s : Sha256.Ops B W) (secret transcriptHash : List B) :
    (finishedMessage s secret transcriptHash).length = 36 := by
  simp [finishedMessage, frame_length, TlsKdf.finished, Sha256.hmac_length]

theorem retryTranscript_prefix (s : Sha256.Ops B W) (clientHello1 retry following : List B) :
    retryTranscript s clientHello1 retry following =
      [s.byteConst 254, s.byteConst 0, s.byteConst 0, s.byteConst 32] ++
        Sha256.hash s clientHello1 ++ retry ++ following := by
  simp only [retryTranscript, frame, Sha256.hash_length]

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {fb : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' fb fw) (ha : ByteAuth.Hom a a' fb)
include hs

theorem frame_map (kind : Nat) (body : List B) :
    (frame s kind body).map fb = frame s' kind (body.map fb) := by
  simp [frame, hs.byteConst]

theorem frameChecked_map (kind : Nat) (body : List B) :
    (frameChecked s kind body).map (List.map fb) = frameChecked s' kind (body.map fb) := by
  simp only [frameChecked, List.length_map]
  split <;> simp_all [frame_map hs]

theorem retryTranscript_map (clientHello1 retry following : List B) :
    (retryTranscript s clientHello1 retry following).map fb =
      retryTranscript s' (clientHello1.map fb) (retry.map fb) (following.map fb) := by
  simp only [retryTranscript, List.map_append, frame_map hs, Sha256.hash_map hs]

theorem retryHash_map (clientHello1 retry following : List B) :
    (retryHash s clientHello1 retry following).map fb =
      retryHash s' (clientHello1.map fb) (retry.map fb) (following.map fb) := by
  simp only [retryHash, Sha256.hash_map hs, retryTranscript_map hs]

theorem finishedMessage_map (secret transcriptHash : List B) :
    (finishedMessage s secret transcriptHash).map fb =
      finishedMessage s' (secret.map fb) (transcriptHash.map fb) := by
  simp only [finishedMessage, frame_map hs, TlsKdf.finished_map hs]

include ha

theorem verifyHash_map (secret transcriptHash receivedMessage : List B) :
    fb (verifyHash s a secret transcriptHash receivedMessage) =
      verifyHash s' a' (secret.map fb) (transcriptHash.map fb) (receivedMessage.map fb) := by
  simp only [verifyHash, ByteAuth.equalMask_map ha, finishedMessage_map hs]

theorem verifyTranscript_map (secret transcript receivedMessage : List B) :
    fb (verifyTranscript s a secret transcript receivedMessage) =
      verifyTranscript s' a' (secret.map fb) (transcript.map fb) (receivedMessage.map fb) := by
  simp only [verifyTranscript, verifyHash_map hs ha, Sha256.hash_map hs]

theorem verifyChecked_map (secret transcript receivedMessage : List B) :
    (verifyChecked s a secret transcript receivedMessage).map fb =
      verifyChecked s' a' (secret.map fb) (transcript.map fb) (receivedMessage.map fb) := by
  simp only [verifyChecked, List.length_map]
  split <;> simp_all [verifyTranscript_map hs ha]

end Refinement

theorem verifyHash_value (secret transcriptHash receivedMessage : List (BitVec 8)) :
    verifyHash Sha256.concrete ByteAuth.concrete secret transcriptHash receivedMessage =
      if finishedMessage Sha256.concrete secret transcriptHash = receivedMessage then 255 else 0 :=
  ByteAuth.equalMask_value _ _

theorem verifyTranscript_correct (secret transcript receivedMessage : List (BitVec 8)) :
    verifyTranscript Sha256.concrete ByteAuth.concrete secret transcript receivedMessage =
      spec secret transcript receivedMessage := verifyHash_value _ _ _

theorem reject_wrong_finished (secret transcript receivedMessage : List (BitVec 8))
    (bad : finishedMessage Sha256.concrete secret (Sha256.hash Sha256.concrete transcript) ≠ receivedMessage) :
    verifyTranscript Sha256.concrete ByteAuth.concrete secret transcript receivedMessage = 0 := by
  rw [verifyTranscript_correct]
  simp only [spec, if_neg bad]

theorem compiled_verifyHash_correct (secret transcriptHash receivedMessage : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (verifyHash Sha256.symbolic ByteAuth.symbolic secret transcriptHash receivedMessage)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (verifyHash Sha256.symbolic ByteAuth.symbolic secret transcriptHash receivedMessage)).vec.get index hi)) =
    (if finishedMessage Sha256.concrete (secret.map (BVExpr.eval assign))
          (transcriptHash.map (BVExpr.eval assign)) = receivedMessage.map (BVExpr.eval assign)
      then (255 : BitVec 8) else 0).getLsbD index := by
  rw [AigExport.compile_correct, verifyHash_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign),
    verifyHash_value]

theorem compiled_retryHash_correct (clientHello1 retry following : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (retryHash Sha256.symbolic clientHello1 retry following).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (retryHash Sha256.symbolic clientHello1 retry following))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (retryHash Sha256.symbolic clientHello1 retry following))).vec.get index hi)) =
    (ByteCircuit.joinValue (retryHash Sha256.concrete (clientHello1.map (BVExpr.eval assign))
      (retry.map (BVExpr.eval assign)) (following.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, retryHash_map (Sha256.evaluationHom assign)]

theorem compiled_verifyTranscript_correct (secret transcript receivedMessage : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (verifyTranscript Sha256.symbolic ByteAuth.symbolic secret transcript receivedMessage)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (verifyTranscript Sha256.symbolic ByteAuth.symbolic secret transcript receivedMessage)).vec.get index hi)) =
    (spec (secret.map (BVExpr.eval assign)) (transcript.map (BVExpr.eval assign))
      (receivedMessage.map (BVExpr.eval assign))).getLsbD index := by
  rw [AigExport.compile_correct,
    verifyTranscript_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign), verifyTranscript_correct]

end TlsMpc.TlsHandshake
