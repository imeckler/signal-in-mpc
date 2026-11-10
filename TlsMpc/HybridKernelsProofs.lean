import TlsMpc.HybridKernels

/-!
Theorems about worker kernels as wholes (TlsMpc/HybridKernels.lean).

* `compiled_correct`: for EVERY kernel, each exported gate-level output bit
  equals the corresponding bit of the kernel's Lean definition evaluated on the
  inputs. (The JSON transport, the lowering to the flat gate list and the
  runtime are outside this statement.)
* `tlsUpdate_spec`: the KeyUpdate kernel returns the RFC traffic-secret update
  of the secret held in the block, followed by the key and IV derived from that
  new secret.
* `tlsOpenApplication_spec`: the application-receive kernel's four fields are
  the stated slices of the post-handshake parser applied to the RFC record
  opening under the key and IV held in the server block; in particular the two
  opened bytes are the first two bytes of that parser's output.
* `tlsOpenApplication_event_private`: for an authenticated application-data
  record, those two opened bytes do not depend on the record's content.
-/
namespace TlsMpc.HybridKernel
open Std.Tactic.BVDecide
open Signal

/-- All output bytes of a kernel, in field order. -/
def Kernel.bytes (k : Kernel) : List (BVExpr 8) := k.outputs.flatMap (·.value)

theorem compiled_correct (k : Kernel) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  ByteCircuit.compile_bytes_correct k.bytes assign index hi

theorem sl_map (f : α → β) (bytes : List α) (start count : Nat) :
    ((bytes.drop start).take count).map f = ((bytes.map f).drop start).take count := by
  simp [List.map_take, List.map_drop]

/-! ### KeyUpdate -/

/-- The traffic secret held in a block: its first 32 bytes. -/
def secretOf (block : List (BitVec 8)) : List (BitVec 8) := (block.drop 0).take 32

theorem tlsUpdate_spec (assign : BVExpr.Assignment) :
    let block := (ByteCircuit.inputBytes 0 60).map (BVExpr.eval assign)
    let next := TlsKdf.updateTraffic Sha256.concrete (secretOf block)
    tlsUpdate.bytes.map (BVExpr.eval assign) =
      next ++ (TlsKdf.trafficKeys Sha256.concrete next).1 ++ (TlsKdf.trafficKeys Sha256.concrete next).2 := by
  intro block next
  have hsecret : (blockSecret (ByteCircuit.inputBytes 0 60)).map (BVExpr.eval assign) = secretOf block := by
    simp only [blockSecret, sl, secretOf, block, sl_map]
  have hnext : (TlsKdf.expandLabelFast Sha256.symbolic (blockSecret (ByteCircuit.inputBytes 0 60)) "traffic upd" [] 32).map
      (BVExpr.eval assign) = next := by
    rw [TlsKdf.expandLabelFast_correct]
    have h := TlsKdf.updateTraffic_map (Sha256.evaluationHom assign) (blockSecret (ByteCircuit.inputBytes 0 60))
    simp only [TlsKdf.updateTraffic] at h
    rw [h, hsecret]
    rfl
  have hkeys := TlsKdf.trafficKeys_map (Sha256.evaluationHom assign)
    (TlsKdf.expandLabelFast Sha256.symbolic (blockSecret (ByteCircuit.inputBytes 0 60)) "traffic upd" [] 32)
  rw [hnext] at hkeys
  show (List.flatMap (·.value) tlsUpdate.outputs).map (BVExpr.eval assign) = _
  simp only [tlsUpdate, lookup, lookupFrom, priv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    HybridKdf.trafficBlock, TlsKdf.trafficKeysFast_correct, List.map_append, hnext, beq_self_eq_true, ↓reduceIte]
  rw [← hkeys]

/-! ### Application receive -/

/-- What the application-receive kernel computes, on values: the post-handshake
parser applied to the RFC opening of the record under the block's key and IV. -/
def openApplicationSpec (parser block sequence record : List (BitVec 8)) : List (BitVec 8) :=
  TlsPostHandshake.core Word64.concrete ByteAuth.concrete parser
    (TlsReceive.spec ((block.drop 32).take 16) ((block.drop 48).take 12) sequence record)

theorem tlsOpenApplication_spec (size : Nat) (assign : BVExpr.Assignment) :
    let value := fun start count => (ByteCircuit.inputBytes start count).map (BVExpr.eval assign)
    let spec := openApplicationSpec (value 0 11) (value 11 60) (value 71 8) (value 79 size)
    (tlsOpenApplication size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [(spec.drop 0).take 2, (spec.drop 2).take 11, (spec.drop 13).take 2, spec.drop 15] := by
  intro value spec
  have hcore : (TlsPostHandshake.openCore Gcm.symbolic Word64.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 11)
      (blockKey (ByteCircuit.inputBytes 11 60)) (blockIv (ByteCircuit.inputBytes 11 60))
      (ByteCircuit.inputBytes 71 8) (ByteCircuit.inputBytes 79 size)).map (BVExpr.eval assign) = spec := by
    unfold TlsPostHandshake.openCore
    rw [TlsPostHandshake.core_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign),
      TlsReceive.openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
      TlsReceive.openCore_correct _ _ _ _ (by simp [blockKey, sl, ByteCircuit.inputBytes])]
    simp only [blockKey, blockIv, sl, sl_map]
    rfl
  have hparser : lookup [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
      ("record", .bytes size)] "parser" = ByteCircuit.inputBytes 0 11 := by simp [lookup, lookupFrom]
  have hblock : lookup [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
      ("record", .bytes size)] "serverApplication" = ByteCircuit.inputBytes 11 60 := by
    simp [lookup, lookupFrom, Shape.variables]
  have hsequence : lookup [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
      ("record", .bytes size)] "sequence" = ByteCircuit.inputBytes 71 8 := by
    simp [lookup, lookupFrom, Shape.variables]
  have hrecord : lookup [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
      ("record", .bytes size)] "record" = ByteCircuit.inputBytes 79 size := by
    simp [lookup, lookupFrom, Shape.variables]
  simp only [tlsOpenApplication, priv, pub, List.map_cons, List.map_nil, hparser, hblock, hsequence, hrecord]
  simp only [sl, sl_map, List.map_drop, hcore]

/-- The opened event bytes of an authenticated application-data record are the
same for any two contents of equal length (same parser state and metadata). -/
theorem tlsOpenApplication_event_private (parser : TlsPostHandshake.State (BitVec 8) (BitVec 64))
    (status high low : BitVec 8) (xs ys : List (BitVec 8)) (h : xs.length = ys.length) :
    (TlsPostHandshake.process Word64.concrete ByteAuth.concrete parser (status :: 23 :: high :: low :: xs)).take 2 =
    (TlsPostHandshake.process Word64.concrete ByteAuth.concrete parser (status :: 23 :: high :: low :: ys)).take 2 :=
  TlsPostHandshake.process_application_event_independent parser status high low xs ys h

#print axioms compiled_correct
#print axioms tlsUpdate_spec
#print axioms tlsOpenApplication_spec
#print axioms tlsOpenApplication_event_private

end TlsMpc.HybridKernel
