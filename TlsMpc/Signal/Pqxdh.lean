import TlsMpc.TlsKdfPrepared

/-! PQXDH handshake key derivation from secret DH and Kyber agreement outputs.
The presence of an optional one-time DH agreement is public shape information.
All agreement bytes and all derived keys remain shared. This implements the
pinned libsignal input order and KDF label; it does not implement agreement,
KEM decapsulation, identity/signature validation, or their error handling.
Actual Rust HKDF/wrapper equivalence is a separate reference obligation. -/
namespace TlsMpc.Signal.Pqxdh
open Std.Tactic.BVDecide

def label : List Nat := TlsKdf.ascii "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"

/-- `oneTime` is empty or a 32-byte agreement according to the public profile. -/
def secretInput (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B) : List B :=
  List.replicate 32 (s.byteConst 255) ++ dh1 ++ dh2 ++ dh3 ++ oneTime ++ kem

def validShape (dh1 dh2 dh3 oneTime kem : List B) : Prop :=
  dh1.length = 32 ∧ dh2.length = 32 ∧ dh3.length = 32 ∧
    (oneTime.length = 0 ∨ oneTime.length = 32) ∧ kem.length = 32

instance (dh1 dh2 dh3 oneTime kem : List B) : Decidable (validShape dh1 dh2 dh3 oneTime kem) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Root key32 || chain key32 || initial PQR key32, exactly the HKDF split. -/
def deriveCore (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B) : List B :=
  let input := secretInput s dh1 dh2 dh3 oneTime kem
  TlsKdf.expandFast s (TlsKdf.extract s [] input) (label.map s.byteConst) 96

def deriveChecked (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B) : Option (List B) :=
  if validShape dh1 dh2 dh3 oneTime kem then some (deriveCore s dh1 dh2 dh3 oneTime kem) else none

/-- Ratchet initialization layout: root32 || chain32 || counterBE4 || PQR32. -/
def initialState (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B) : List B :=
  let keys := deriveCore s dh1 dh2 dh3 oneTime kem
  keys.take 64 ++ List.replicate 4 (s.byteConst 0) ++ keys.drop 64

theorem secretInput_length (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B)
    (h : validShape dh1 dh2 dh3 oneTime kem) :
    (secretInput s dh1 dh2 dh3 oneTime kem).length = 160 + oneTime.length := by
  rcases h with ⟨h1,h2,h3,_,hk⟩
  simp [secretInput, h1,h2,h3,hk]; omega

theorem deriveCore_length (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B) :
    (deriveCore s dh1 dh2 dh3 oneTime kem).length = 96 := by
  simp [deriveCore, TlsKdf.expandFast_correct, TlsKdf.expandCore_length]

theorem initialState_length (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem : List B) :
    (initialState s dh1 dh2 dh3 oneTime kem).length = 100 := by
  simp [initialState, deriveCore_length]

/-- Explicit HKDF-SHA256 recurrence: zero-salt extraction and three blocks. -/
def specification (dh1 dh2 dh3 oneTime kem : List (BitVec 8)) : List (BitVec 8) :=
  let input := List.replicate 32 (255 : BitVec 8) ++ dh1 ++ dh2 ++ dh3 ++ oneTime ++ kem
  let prk := Sha256.hmac Sha256.concrete (List.replicate 32 0) input
  let info := label.map (BitVec.ofNat 8)
  let t1 := Sha256.hmac Sha256.concrete prk (info ++ [1])
  let t2 := Sha256.hmac Sha256.concrete prk (t1 ++ info ++ [2])
  let t3 := Sha256.hmac Sha256.concrete prk (t2 ++ info ++ [3])
  t1 ++ t2 ++ t3

theorem deriveCore_specification (dh1 dh2 dh3 oneTime kem : List (BitVec 8)) :
    deriveCore Sha256.concrete dh1 dh2 dh3 oneTime kem = specification dh1 dh2 dh3 oneTime kem := by
  simp only [deriveCore, TlsKdf.expandFast_correct, TlsKdf.expandCore, TlsKdf.expandBlocks,
    TlsKdf.extract, List.isEmpty_nil, if_true, TlsKdf.zeros, secretInput,
    specification, List.nil_append, List.append_nil]
  change List.take 96 _ = _
  rw [List.take_of_length_le]
  · simp only [List.append_assoc]
    rfl
  · simp [Sha256.hmac_length]

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {f : B → B'} {fw : W → W'}
  (hs : Sha256.Hom s s' f fw)
include hs

theorem secretInput_map (dh1 dh2 dh3 oneTime kem : List B) :
    (secretInput s dh1 dh2 dh3 oneTime kem).map f =
      secretInput s' (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f) := by
  simp [secretInput, hs.byteConst]

theorem deriveCore_map (dh1 dh2 dh3 oneTime kem : List B) :
    (deriveCore s dh1 dh2 dh3 oneTime kem).map f =
      deriveCore s' (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f) := by
  simp only [deriveCore, TlsKdf.expandFast_correct, TlsKdf.expandCore_map hs,
    TlsKdf.extract_map hs, List.map_nil, secretInput_map hs, List.map_map,
    Function.comp_def, hs.byteConst]

theorem deriveChecked_map (dh1 dh2 dh3 oneTime kem : List B) :
    (deriveChecked s dh1 dh2 dh3 oneTime kem).map (List.map f) =
      deriveChecked s' (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f) := by
  simp only [deriveChecked, validShape, List.length_map]
  split <;> simp [deriveCore_map hs]

theorem initialState_map (dh1 dh2 dh3 oneTime kem : List B) :
    (initialState s dh1 dh2 dh3 oneTime kem).map f =
      initialState s' (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f) := by
  simp only [initialState, List.map_append, List.map_take, List.map_drop,
    List.map_replicate, hs.byteConst, deriveCore_map hs]
end Refinement

theorem compiled_deriveCore_specification (dh1 dh2 dh3 oneTime kem : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (deriveCore Sha256.symbolic dh1 dh2 dh3 oneTime kem).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (deriveCore Sha256.symbolic dh1 dh2 dh3 oneTime kem))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (deriveCore Sha256.symbolic dh1 dh2 dh3 oneTime kem))).vec.get index hi)) =
      (ByteCircuit.joinValue (specification (dh1.map (BVExpr.eval assign))
        (dh2.map (BVExpr.eval assign)) (dh3.map (BVExpr.eval assign))
        (oneTime.map (BVExpr.eval assign)) (kem.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, deriveCore_map (Sha256.evaluationHom assign),
    deriveCore_specification]

theorem compiled_initialState_correct (dh1 dh2 dh3 oneTime kem : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (initialState Sha256.symbolic dh1 dh2 dh3 oneTime kem).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (initialState Sha256.symbolic dh1 dh2 dh3 oneTime kem))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (initialState Sha256.symbolic dh1 dh2 dh3 oneTime kem))).vec.get index hi)) =
      (ByteCircuit.joinValue (initialState Sha256.concrete (dh1.map (BVExpr.eval assign))
        (dh2.map (BVExpr.eval assign)) (dh3.map (BVExpr.eval assign))
        (oneTime.map (BVExpr.eval assign)) (kem.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, initialState_map (Sha256.evaluationHom assign)]

end TlsMpc.Signal.Pqxdh
