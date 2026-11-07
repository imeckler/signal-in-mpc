import TlsMpc.TlsKdfPrepared

/-!
Lean implementation of the symmetric derivation in pinned libsignal keys.rs.

The all-input theorems here prove compilation of this Lean specification to the
Boolean/AIG artifact. They do NOT yet prove equivalence to the RustCrypto
dependencies of libsignal: the actual Charon/Aeneas extraction and its blockers
are recorded in SignalReference. No opaque crypto model is imported here.

Chain keys, message seeds, post-quantum salts, derived keys and next chain keys
are secret bytes. The caller supplies a 32-byte SPQR salt, selected inside MPC:
32 zero bytes when no SPQR key is present, otherwise the SPQR message key.
This is key derivation only; counter checks, state commit, SPQR, AES and message
authentication must be composed before a complete send operation is available.
-/

namespace TlsMpc.Signal.Symmetric

open Std.Tactic.BVDecide Sha256

structure Material (B : Type) where
  cipherKey : List B
  macKey : List B
  iv : List B

def Material.map (f : B → B') (m : Material B) : Material B' :=
  ⟨m.cipherKey.map f, m.macKey.map f, m.iv.map f⟩

def Material.bytes (m : Material B) : List B := m.cipherKey ++ m.macKey ++ m.iv

def messageSeed (o : Ops B W) (chainKey : List B) : List B :=
  hmac o chainKey [o.byteConst 1]

def nextChainKey (o : Ops B W) (chainKey : List B) : List B :=
  hmac o chainKey [o.byteConst 2]

def messageMaterial (o : Ops B W) (seed pqSalt : List B) : Material B :=
  let prk := TlsKdf.extract o pqSalt seed
  let output := TlsKdf.expandCore o prk ((TlsKdf.ascii "WhisperMessageKeys").map o.byteConst) 80
  ⟨output.take 32, (output.drop 32).take 32, (output.drop 64).take 16⟩

structure Step (B : Type) where
  nextChainKey : List B
  material : Material B

def Step.map (f : B → B') (s : Step B) : Step B' :=
  ⟨s.nextChainKey.map f, s.material.map f⟩

def Step.bytes (s : Step B) : List B := s.nextChainKey ++ s.material.bytes

def derive (o : Ops B W) (chainKey pqSalt : List B) : Step B :=
  ⟨nextChainKey o chainKey, messageMaterial o (messageSeed o chainKey) pqSalt⟩

/-- Sharing prepared HMAC states is essential for practical symbolic export. -/
def messageMaterialFast (o : Ops B W) (seed pqSalt : List B) : Material B :=
  let prk := TlsKdf.extract o pqSalt seed
  let output := TlsKdf.expandFast o prk ((TlsKdf.ascii "WhisperMessageKeys").map o.byteConst) 80
  ⟨output.take 32, (output.drop 32).take 32, (output.drop 64).take 16⟩

theorem messageMaterialFast_correct (o : Ops B W) (seed salt : List B) :
    messageMaterialFast o seed salt = messageMaterial o seed salt := by
  simp only [messageMaterialFast, messageMaterial, TlsKdf.expandFast_correct]

def deriveFast (o : Ops B W) (chainKey pqSalt : List B) : Step B :=
  let prepared := HmacPrepared.prepare o chainKey
  let seed := HmacPrepared.run o prepared [o.byteConst 1]
  let next := HmacPrepared.run o prepared [o.byteConst 2]
  ⟨next, messageMaterialFast o seed pqSalt⟩

theorem deriveFast_correct (o : Ops B W) (chainKey salt : List B) :
    deriveFast o chainKey salt = derive o chainKey salt := by
  simp only [deriveFast, derive, HmacPrepared.run_prepare,
    messageMaterialFast_correct, messageSeed, nextChainKey]

theorem messageMaterial_lengths (o : Ops B W) (seed pqSalt : List B) :
    (messageMaterial o seed pqSalt).cipherKey.length = 32 ∧
    (messageMaterial o seed pqSalt).macKey.length = 32 ∧
    (messageMaterial o seed pqSalt).iv.length = 16 := by
  simp [messageMaterial, TlsKdf.expandCore_length]

theorem derive_bytes_length (o : Ops B W) (chainKey pqSalt : List B) :
    (derive o chainKey pqSalt).bytes.length = 112 := by
  simp [derive, Step.bytes, Material.bytes, nextChainKey, hmac_length,
    (messageMaterial_lengths o (messageSeed o chainKey) pqSalt).1,
    (messageMaterial_lengths o (messageSeed o chainKey) pqSalt).2.1,
    (messageMaterial_lengths o (messageSeed o chainKey) pqSalt).2.2]

section Refinement

variable {a : Ops B W} {b : Ops B' W'} {fb : B → B'} {fw : W → W'}
variable (h : Hom a b fb fw)
include h

theorem messageSeed_map (key : List B) :
    (messageSeed a key).map fb = messageSeed b (key.map fb) := by
  simp [messageSeed, hmac_map h, h.byteConst]

theorem nextChainKey_map (key : List B) :
    (nextChainKey a key).map fb = nextChainKey b (key.map fb) := by
  simp [nextChainKey, hmac_map h, h.byteConst]

theorem messageMaterial_map (seed salt : List B) :
    (messageMaterial a seed salt).map fb =
      messageMaterial b (seed.map fb) (salt.map fb) := by
  simp [messageMaterial, Material.map, TlsKdf.expandCore_map h,
    TlsKdf.extract_map h, List.map_map, Function.comp_def, h.byteConst]

theorem derive_map (key salt : List B) :
    (derive a key salt).map fb = derive b (key.map fb) (salt.map fb) := by
  simp only [derive, Step.map, messageMaterial_map h, messageSeed_map h, nextChainKey_map h]

theorem derive_bytes_map (key salt : List B) :
    (derive a key salt).bytes.map fb = (derive b (key.map fb) (salt.map fb)).bytes := by
  have hm := derive_map h key salt
  have hb := congrArg Step.bytes hm
  simpa [Step.bytes, Step.map, Material.bytes, Material.map] using hb

end Refinement

theorem compiled_derive_correct (chainKey salt : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (derive symbolic chainKey salt).bytes.length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (derive symbolic chainKey salt).bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (derive symbolic chainKey salt).bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (derive concrete (chainKey.map (BVExpr.eval assign))
      (salt.map (BVExpr.eval assign))).bytes).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, derive_bytes_map (evaluationHom assign)]

theorem compiled_deriveFast_correct (chainKey salt : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (deriveFast symbolic chainKey salt).bytes.length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (deriveFast symbolic chainKey salt).bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (deriveFast symbolic chainKey salt).bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (derive concrete (chainKey.map (BVExpr.eval assign))
      (salt.map (BVExpr.eval assign))).bytes).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, deriveFast_correct,
    derive_bytes_map (evaluationHom assign)]

end TlsMpc.Signal.Symmetric
