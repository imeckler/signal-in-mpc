import TlsMpc.Signal.RatchetStep
import TlsMpc.Signal.BoundedReceive

/-! First-message transaction for an externally selected new DH ratchet. Both
shared agreements and the fresh sender key pair must be justified by the mixed
X25519 stage. The new receiver starts at counter zero with an empty bounded
skipped-key store. The parsed remote key/counter select its bounded seed; the
original wire bytes are authenticated before either sender/root state or new
receiver state is released. Selecting an unknown ratchet among retained chains,
fresh randomness, persistent commit and SPQR evolution remain separate. -/
namespace TlsMpc.Signal.NewRatchetReceive
open Std.Tactic.BVDecide

def finish (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old : RatchetStep.State B)
    (newPrivate newPublic receiveAgreement sendAgreement remote opened : List B) : List B :=
  let updated := RatchetStep.step s a (OpenResult.get a opened 0) old newPrivate newPublic receiveAgreement sendAgreement
  let status := OpenResult.get a updated 0
  updated.take (1 + old.bytes.length) ++ ByteAuth.release a status (remote ++ opened.drop 1)

/-- A failed first message preserves all old sender/root bytes and releases no
new receiver state or plaintext. Capacity and maxJump are public circuit bounds. -/
def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump capacity : Nat) (present : B)
    (old : RatchetStep.State B) (newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected : List B) : List B :=
  let (_,receiving,_) := RatchetStep.derive s old.root receiveAgreement sendAgreement
  let opened := BoundedReceive.openCore d o aes s a maxJump present
    (ReceiveAdvance.listBytes a remote) (ReceiveAdvance.listBytes a receiving) (fun _ => a.const 0)
    (List.replicate capacity (SkippedKeys.empty a)) pqKey sender receiver wire expected
  finish s a old newPrivate newPublic receiveAgreement sendAgreement remote opened

section
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hd ho he hs ha in
theorem openCore_map (maxJump capacity : Nat) (present : B) (old : RatchetStep.State B)
    (newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected : List B) :
    (openCore d o aes s a maxJump capacity present old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected).map f =
      openCore d' o' aes' s' a' maxJump capacity (f present) (old.map f)
        (newPrivate.map f) (newPublic.map f) (receiveAgreement.map f) (sendAgreement.map f) (remote.map f)
        (pqKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  simp only [openCore, finish, List.map_append, List.map_take, RatchetStep.step_map hs ha,
    OpenResult.get_map ha, ByteAuth.release_map ha, List.map_drop,
    BoundedReceive.openCore_map hd ho he hs ha, RatchetStep.derive,
    DhRatchet.materialFast_map hs, List.map_drop, List.map_take, ReceiveAdvance.listBytes_map ha,
    List.map_replicate, SkippedKeys.empty_map ha, RatchetStep.State.map,
    RatchetStep.State.bytes, List.length_append, List.length_map]
  simp only [Function.comp_def, ha.const]
end

theorem finish_reject (old : RatchetStep.State (BitVec 8))
    (newPrivate newPublic receiveAgreement sendAgreement remote opened : List (BitVec 8))
    (h : OpenResult.get ByteAuth.concrete opened 0 ≠ 255) :
    finish Sha256.concrete ByteAuth.concrete old newPrivate newPublic receiveAgreement sendAgreement remote opened =
      0 :: old.bytes ++ List.replicate (remote.length + (opened.drop 1).length) 0 := by
  simp only [finish, RatchetStep.step_reject _ _ _ _ _ _ h]
  have hz : OpenResult.get ByteAuth.concrete (0 :: (old.bytes ++ List.replicate 36 0)) 0 = 0 := rfl
  rw [hz, ByteAuth.release_reject]
  simp only [List.length_append]
  congr 1
  rw [Nat.add_comm 1, List.take_succ_cons]
  congr 1
  exact List.take_left

theorem compiled_openCore_correct (maxJump capacity : Nat) (present : BVExpr 8) (old : RatchetStep.State (BVExpr 8))
    (newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected : List (BVExpr 8))
    (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump capacity present old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump capacity present old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump capacity present old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected))).vec.get bit hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        maxJump capacity (BVExpr.eval assign present) (old.map (BVExpr.eval assign))
        (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign))
        (receiveAgreement.map (BVExpr.eval assign)) (sendAgreement.map (BVExpr.eval assign)) (remote.map (BVExpr.eval assign))
        (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
        (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.NewRatchetReceive
