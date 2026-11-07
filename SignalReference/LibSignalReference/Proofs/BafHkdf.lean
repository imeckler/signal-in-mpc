import LibSignalReference.External.BafRFC5869
import TlsMpc.TlsKdf

/-!
The independently developed BAF RFC 5869 specification is instantiated with our
concrete SHA-256 HMAC, not an opaque cryptographic model. These equalities connect
its octet-list specification to our implementation and numeric circuit artifact.
They do not establish equivalence to the RustCrypto HMAC/HKDF wrappers.
-/

namespace LibSignalReference.Proofs.BafHkdf

open TlsMpc

def encode (bytes : List (BitVec 8)) : List UInt8 := bytes.map (fun b => ⟨b⟩)
def decode (bytes : List UInt8) : List (BitVec 8) := bytes.map UInt8.toBitVec

@[simp] theorem decode_encode (bytes : List (BitVec 8)) : decode (encode bytes) = bytes := by
  simp [encode, decode, List.map_map, Function.comp_def]

@[simp] theorem encode_decode (bytes : List UInt8) : encode (decode bytes) = bytes := by
  simp [encode, decode, List.map_map, Function.comp_def]

def sha256 : Baf.HKDF.HashFunction where
  HashLen := 32
  HashLen_pos := by decide
  HMAC key message := encode (Sha256.hmac Sha256.concrete (decode key) (decode message))
  HMAC_length key message := by simp [encode, Sha256.hmac_length]

theorem hmac_eq (key message : List (BitVec 8)) :
    sha256.HMAC (encode key) (encode message) = encode (Sha256.hmac Sha256.concrete key message) := by
  simp [sha256]

theorem decode_T_succ (prk info : List UInt8) (offset : Nat) :
    decode (Baf.HKDF.T sha256 prk info (offset + 1)) =
      Sha256.hmac Sha256.concrete (decode prk)
        (decode (Baf.HKDF.T sha256 prk info offset) ++ decode info ++
          [BitVec.ofNat 8 (offset + 1)]) := by
  change decode (encode (Sha256.hmac Sha256.concrete (decode prk)
    (decode (Baf.HKDF.T sha256 prk info offset ++ info ++ [UInt8.ofNat (offset + 1)])))) = _
  rw [decode_encode]
  simp only [decode, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem expandBlocks_eq (prk info : List UInt8) (n offset : Nat) :
    TlsKdf.expandBlocks Sha256.concrete (decode prk) (decode info) n (offset + 1)
      (decode (Baf.HKDF.T sha256 prk info offset)) =
      decode ((List.range n).flatMap (fun i => Baf.HKDF.T sha256 prk info (offset + i + 1))) := by
  induction n generalizing offset with
  | zero => simp [TlsKdf.expandBlocks, decode]
  | succ n ih =>
    rw [TlsKdf.expandBlocks]
    change Sha256.hmac Sha256.concrete _ _ ++ _ = _
    have step := decode_T_succ prk info offset
    change decode (Baf.HKDF.T sha256 prk info (offset + 1)) =
      Sha256.hmac Sha256.concrete (decode prk)
        (decode (Baf.HKDF.T sha256 prk info offset) ++ decode info ++
          [Sha256.concrete.byteConst (offset + 1)]) at step
    rw [← step, ih]
    simp [List.range_succ_eq_map, decode, List.map_flatMap, List.flatMap_map,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem expandCore_eq (prk info : List (BitVec 8)) (length : Nat) :
    TlsKdf.expandCore Sha256.concrete prk info length =
      decode (Baf.HKDF.Expand sha256 (encode prk) (encode info) length) := by
  have h := expandBlocks_eq (encode prk) (encode info) ((length + 31) / 32) 0
  rw [decode_encode, decode_encode] at h
  simp only [Nat.zero_add] at h
  change TlsKdf.expandBlocks Sha256.concrete prk info ((length + 31) / 32) 1 [] =
    decode ((List.range ((length + 31) / 32)).flatMap
      (fun i => Baf.HKDF.T sha256 (encode prk) (encode info) (i + 1))) at h
  rw [TlsKdf.expandCore, h]
  have hn : Baf.HKDF.N sha256 length = (length + 31) / 32 := by
    simp only [Baf.HKDF.N, sha256]
    congr 1
  simp only [Baf.HKDF.Expand, hn, decode, List.map_take]

/-- An empty salt denotes the RFC's omitted salt in our byte-list API. -/
theorem extract_eq (salt ikm : List (BitVec 8)) :
    TlsKdf.extract Sha256.concrete salt ikm =
      decode (Baf.HKDF.Extract sha256
        (if salt.isEmpty then none else some (encode salt)) (encode ikm)) := by
  simp only [TlsKdf.extract]
  split
  · simp only [Baf.HKDF.Extract, Option.getD_none, sha256, decode_encode]
    congr 1
  · simp only [Baf.HKDF.Extract, Option.getD_some, sha256, decode_encode]

theorem expand_eq (prk info : List (BitVec 8)) (length : Nat)
    (valid : length ≤ 255 * 32) :
    TlsKdf.expand Sha256.concrete prk info length =
      some (decode (Baf.HKDF.Expand sha256 (encode prk) (encode info) length)) := by
  simp only [TlsKdf.expand, valid, if_true, expandCore_eq]

theorem compiled_expandCore_refines
    (prk info : List (Std.Tactic.BVDecide.BVExpr 8))
    (length : Nat) (assign : Std.Tactic.BVDecide.BVExpr.Assignment)
    (index : Nat)
    (hi : index < 8 * (TlsKdf.expandCore Sha256.symbolic prk info length).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (TlsKdf.expandCore Sha256.symbolic prk info length))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (TlsKdf.expandCore Sha256.symbolic prk info length))).vec.get index hi)) =
    (ByteCircuit.joinValue (decode (Baf.HKDF.Expand sha256
      (encode (prk.map (Std.Tactic.BVDecide.BVExpr.eval assign)))
      (encode (info.map (Std.Tactic.BVDecide.BVExpr.eval assign))) length))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    TlsKdf.expandCore_map (Sha256.evaluationHom assign), expandCore_eq]

end LibSignalReference.Proofs.BafHkdf
