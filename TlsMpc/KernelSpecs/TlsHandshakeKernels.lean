import TlsMpc.HybridKernels

/-!
Kernel-level specifications of the TLS 1.3 handshake kernels without one so far:
`tls-derive`, `tls-verify-finished`, `tls-finish` and `tls-open-handshake`
(`HybridKernel.tlsDerive`, `tlsVerifyFinished`, `tlsFinish`, `tlsOpenHandshake`).

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `trafficBlock_eval`: a traffic block evaluates to secret ‖ key ‖ IV with key and IV the
  RFC 8446 `HKDF-Expand-Label(secret, "key"/"iv", "", 16/12)` (`TlsKdf.trafficKeys`).
* `tlsDerive_spec`: the three private outputs are the client and server handshake traffic
  blocks and the main secret of `TlsKdf.handshakeSecrets` (the RFC 8446 key schedule without
  PSK) on the 32 little-endian bytes of the agreement word and the hello transcript hash.
* `tlsVerifyFinished_spec`: the opened `accepted` byte is 255 exactly when the received
  message equals the server Finished message (`TlsHandshake.finishedMessage`: header 20 ‖
  HMAC(finished_key, transcript hash)) under the server handshake traffic secret, else 0.
* `tlsFinish_spec`: the two private application traffic blocks are those of
  `TlsKdf.applicationSecrets`, and the opened `record` is `TlsRecord.sealCore` (AES-128-GCM,
  sequence 0, content type 22) of certificate ‖ Finished(client handshake secret, client hash)
  under the client handshake key and IV.
* `tlsOpenHandshake_spec`: the opened `result` is `TlsPublicHandshake.gate` of the RFC
  opening `TlsReceive.spec` of the record under the server handshake key and IV;
  `tlsOpenHandshake_application_zero`: when the opening's content type is 23 (application
  data) the opened result is all zero — the refusal path.

The reference functions are the repository's transcriptions (`TlsKdf`, `TlsRecord`,
`TlsReceive.spec`); no test vectors are checked here.
-/
namespace TlsMpc.KernelSpecs.TlsHandshake
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup lookupFrom pub priv sl)

/-- A traffic block on values: secret ‖ key ‖ IV. -/
def trafficBlockValue (secret : List (BitVec 8)) : List (BitVec 8) :=
  secret ++ (TlsKdf.trafficKeys Sha256.concrete secret).1 ++ (TlsKdf.trafficKeys Sha256.concrete secret).2

theorem trafficBlock_eval (assign : BVExpr.Assignment) (secret : List (BVExpr 8)) :
    (HybridKdf.trafficBlock secret).map (BVExpr.eval assign) = trafficBlockValue (secret.map (BVExpr.eval assign)) := by
  have hkeys := TlsKdf.trafficKeys_map (Sha256.evaluationHom assign) secret
  simp only [HybridKdf.trafficBlock, TlsKdf.trafficKeysFast_correct, List.map_append, trafficBlockValue, ← hkeys]

/-! ### tls-derive -/

def deriveInputs : List (String × Shape) := [("agreement", Shape.word), ("helloHash", .bytes 32)]

theorem tlsDerive_spec (assign : BVExpr.Assignment) :
    let get := fun name => (lookup deriveInputs name).map (BVExpr.eval assign)
    let secrets := TlsKdf.handshakeSecrets Sha256.concrete (get "agreement") (get "helloHash")
    HybridKernel.tlsDerive.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [trafficBlockValue secrets.client, trafficBlockValue secrets.server, secrets.main] := by
  intro get secrets
  have h := TlsKdf.handshakeSecrets_map (Sha256.evaluationHom assign) (lookup deriveInputs "agreement")
    (lookup deriveInputs "helloHash")
  have hc := congrArg TlsKdf.HandshakeSecrets.client h
  have hs := congrArg TlsKdf.HandshakeSecrets.server h
  have hm := congrArg TlsKdf.HandshakeSecrets.main h
  simp only [TlsKdf.HandshakeSecrets.map, deriveInputs] at hc hs hm
  simp only [HybridKernel.tlsDerive, priv, List.map_cons, List.map_nil, TlsKdf.handshakeSecretsFast_correct,
    trafficBlock_eval]
  rw [hc, hs, hm]
  rfl

/-! ### tls-verify-finished -/

def verifyInputs : List (String × Shape) :=
  [("serverHandshake", Shape.bytes 60), ("transcriptHash", .bytes 32), ("message", .bytes 36)]

theorem tlsVerifyFinished_spec (assign : BVExpr.Assignment) :
    let get := fun name => (lookup verifyInputs name).map (BVExpr.eval assign)
    HybridKernel.tlsVerifyFinished.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[if TlsHandshake.finishedMessage Sha256.concrete ((get "serverHandshake").take 32) (get "transcriptHash") =
          get "message" then 255 else 0]] := by
  intro get
  have h := TlsHandshake.verifyHash_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)
    (HybridKernel.blockSecret (lookup verifyInputs "serverHandshake")) (lookup verifyInputs "transcriptHash")
    (lookup verifyInputs "message")
  show [[BVExpr.eval assign (TlsHandshake.verifyHash Sha256.symbolic ByteAuth.symbolic
      (HybridKernel.blockSecret (lookup verifyInputs "serverHandshake")) (lookup verifyInputs "transcriptHash")
      (lookup verifyInputs "message"))]] = _
  rw [h, TlsHandshake.verifyHash_value]
  simp only [HybridKernel.blockSecret, sl, List.map_take, List.drop_zero, get]

/-! ### tls-finish -/

def finishInputs (certificateSize : Nat) : List (String × Shape) :=
  [("mainSecret", Shape.bytes 32), ("serverHash", .bytes 32), ("clientHandshake", .bytes 60),
    ("clientHash", .bytes 32), ("certificate", .bytes certificateSize)]

theorem tlsFinish_spec (certificateSize : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (finishInputs certificateSize) name).map (BVExpr.eval assign)
    let application := TlsKdf.applicationSecrets Sha256.concrete (get "mainSecret") (get "serverHash")
    let client := get "clientHandshake"
    (HybridKernel.tlsFinish certificateSize).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [trafficBlockValue application.1, trafficBlockValue application.2,
        TlsRecord.sealCore Gcm.concrete ((client.drop 32).take 16) ((client.drop 48).take 12) (List.replicate 8 0)
          (get "certificate" ++ [20, 0, 0, 32] ++
            TlsKdf.finished Sha256.concrete (client.take 32) (get "clientHash")) 22 0] := by
  intro get application client
  have happ := TlsKdf.applicationSecrets_map (Sha256.evaluationHom assign)
    (lookup (finishInputs certificateSize) "mainSecret") (lookup (finishInputs certificateSize) "serverHash")
  have h1 := congrArg Prod.fst happ
  have h2 := congrArg Prod.snd happ
  simp only at h1 h2
  have hseal := TlsRecord.sealCore_map (Gcm.evaluationHom assign)
    (HybridKernel.blockKey (lookup (finishInputs certificateSize) "clientHandshake"))
    (HybridKernel.blockIv (lookup (finishInputs certificateSize) "clientHandshake")) (HybridKernel.zeros 8)
    (lookup (finishInputs certificateSize) "certificate" ++ [20, 0, 0, 32].map HybridKernel.const ++
      TlsKdf.finished Sha256.symbolic (HybridKernel.blockSecret (lookup (finishInputs certificateSize) "clientHandshake"))
        (lookup (finishInputs certificateSize) "clientHash")) 22 0
  have zeros : (HybridKernel.zeros 8).map (BVExpr.eval assign) = List.replicate 8 0 := by
    simp only [HybridKernel.zeros, List.map_replicate]
    rfl
  have header : ([20, 0, 0, 32].map HybridKernel.const).map (BVExpr.eval assign) = [20, 0, 0, 32] := rfl
  show [(HybridKdf.trafficBlock (TlsKdf.applicationSecretsFast Sha256.symbolic
        (lookup (finishInputs certificateSize) "mainSecret") (lookup (finishInputs certificateSize) "serverHash")).1).map
        (BVExpr.eval assign),
      (HybridKdf.trafficBlock (TlsKdf.applicationSecretsFast Sha256.symbolic
        (lookup (finishInputs certificateSize) "mainSecret") (lookup (finishInputs certificateSize) "serverHash")).2).map
        (BVExpr.eval assign),
      (TlsRecord.sealCore Gcm.symbolic
        (HybridKernel.blockKey (lookup (finishInputs certificateSize) "clientHandshake"))
        (HybridKernel.blockIv (lookup (finishInputs certificateSize) "clientHandshake")) (HybridKernel.zeros 8)
        (lookup (finishInputs certificateSize) "certificate" ++ [20, 0, 0, 32].map HybridKernel.const ++
          TlsKdf.finished Sha256.symbolic (HybridKernel.blockSecret (lookup (finishInputs certificateSize) "clientHandshake"))
            (lookup (finishInputs certificateSize) "clientHash")) 22 0).map (BVExpr.eval assign)] = _
  rw [TlsKdf.applicationSecretsFast_correct, trafficBlock_eval, trafficBlock_eval, h1, h2, hseal]
  simp only [List.map_append, zeros, header, TlsKdf.finished_map (Sha256.evaluationHom assign), HybridKernel.blockKey, HybridKernel.blockIv,
    HybridKernel.blockSecret, sl, List.map_take, List.map_drop, List.drop_zero, application, client, get]

/-! ### tls-open-handshake -/

def openInputs (size : Nat) : List (String × Shape) :=
  [("serverHandshake", Shape.bytes 60), ("sequence", .bytes 8), ("record", .bytes size)]

theorem tlsOpenHandshake_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (openInputs size) name).map (BVExpr.eval assign)
    let block := get "serverHandshake"
    (HybridKernel.tlsOpenHandshake size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [TlsPublicHandshake.gate ByteAuth.concrete
        (TlsReceive.spec ((block.drop 32).take 16) ((block.drop 48).take 12) (get "sequence") (get "record"))] := by
  intro get block
  have hkey : ((HybridKernel.blockKey (lookup (openInputs size) "serverHandshake")).map (BVExpr.eval assign)).length = 16 := by
    simp [HybridKernel.blockKey, sl, openInputs, lookup, lookupFrom, ByteCircuit.inputBytes]
  show [(TlsPublicHandshake.openCore Gcm.symbolic ByteAuth.symbolic
      (HybridKernel.blockKey (lookup (openInputs size) "serverHandshake"))
      (HybridKernel.blockIv (lookup (openInputs size) "serverHandshake"))
      (lookup (openInputs size) "sequence") (lookup (openInputs size) "record")).map (BVExpr.eval assign)] = _
  unfold TlsPublicHandshake.openCore
  rw [TlsPublicHandshake.gate_map (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_correct _ _ _ _ hkey]
  simp only [HybridKernel.blockKey, HybridKernel.blockIv, sl, List.map_take, List.map_drop, block, get]

/-- The refusal path: when the opened record's content type is application data (23), the
opened `result` is all zero. -/
theorem tlsOpenHandshake_application_zero (size : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (openInputs size) name).map (BVExpr.eval assign)
    let block := get "serverHandshake"
    let parsed := TlsReceive.spec ((block.drop 32).take 16) ((block.drop 48).take 12) (get "sequence") (get "record")
    parsed[1]?.getD 0 = 23 →
      (HybridKernel.tlsOpenHandshake size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
        [List.replicate parsed.length 0] := by
  intro get block parsed kind
  rw [tlsOpenHandshake_spec, TlsPublicHandshake.application_not_released _ kind]

#print axioms trafficBlock_eval
#print axioms tlsDerive_spec
#print axioms tlsVerifyFinished_spec
#print axioms tlsFinish_spec
#print axioms tlsOpenHandshake_spec
#print axioms tlsOpenHandshake_application_zero

end TlsMpc.KernelSpecs.TlsHandshake
