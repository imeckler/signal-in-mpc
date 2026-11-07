import TlsMpc.Signal.ProtoReceive
import TlsMpc.Signal.ChainSend

/-! Transactional in-order receive on an already-selected receiving chain.
Keys and identity/counter matching are computed inside MPC. State advances only
when parsing, original-wire authentication, address, padding, ratchet-key and
counter checks all pass. Skipped/future counters and new DH ratchets are separate
session-selection branches; this operation never silently accepts those. -/
namespace TlsMpc.Signal.ChainReceive
open Std.Tactic.BVDecide

def identityMask (a : ByteAuth.Ops B) (parsed ratchet counter : List B) : B :=
  a.and (ByteAuth.equalMask a ((parsed.drop 1).take 32) ratchet)
    (ByteAuth.equalMask a ((parsed.drop 33).take 4) counter)

def finish (a : ByteAuth.Ops B) (accepted : B) (nextKey nextCounter oldKey oldCounter opened : List B) : List B :=
  accepted :: (ChainSend.selectState a accepted nextKey oldKey ++
    ChainSend.selectState a accepted nextCounter oldCounter ++ ByteAuth.release a accepted (opened.drop 1))

def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (present : B)
    (ratchet counter chainKey pqKey sender receiver wire expected : List B) : List B :=
  let parsed := ProtoParse.parseCore d o a wire
  let derived := Symmetric.deriveFast s chainKey (ChainSend.salt a present pqKey)
  let opened := ProtoReceive.openCore d o aes s a derived.material.cipherKey derived.material.iv derived.material.macKey sender receiver wire expected
  let accepted := a.and (OpenResult.get a opened 0)
    (a.and (identityMask a parsed ratchet counter) (a.and (ChainSend.flagMask a present) (ChainSend.counterMask a counter)))
  finish a accepted derived.nextChainKey (ChainSend.nextCounter s a counter) chainKey counter opened

def openChecked (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (present : B)
    (ratchet counter chainKey pqKey sender receiver wire expected : List B) : Option (List B) :=
  if ratchet.length = 32 ∧ counter.length = 4 ∧ chainKey.length = 32 ∧ pqKey.length = 32 ∧
      sender.length = 32 ∧ receiver.length = 32 ∧ expected.length = 36 ∧ wire.length ≤ 512 then
    some (openCore d o aes s a present ratchet counter chainKey pqKey sender receiver wire expected)
  else none

section
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha in
theorem identityMask_map (parsed ratchet counter : List B) :
    f (identityMask a parsed ratchet counter) = identityMask a' (parsed.map f) (ratchet.map f) (counter.map f) := by
  simp only [identityMask, ha.and, ByteAuth.equalMask_map ha, List.map_take, List.map_drop]
include ha in
theorem finish_map (accepted : B) (nextKey nextCounter oldKey oldCounter opened : List B) :
    (finish a accepted nextKey nextCounter oldKey oldCounter opened).map f =
      finish a' (f accepted) (nextKey.map f) (nextCounter.map f) (oldKey.map f) (oldCounter.map f) (opened.map f) := by
  simp only [finish, List.map_cons, List.map_append, ChainSend.selectState_map ha, ByteAuth.release_map ha, List.map_drop]
include hd ho he hs ha in
theorem openCore_map (present : B) (ratchet counter chainKey pqKey sender receiver wire expected : List B) :
    (openCore d o aes s a present ratchet counter chainKey pqKey sender receiver wire expected).map f =
      openCore d' o' aes' s' a' (f present) (ratchet.map f) (counter.map f) (chainKey.map f) (pqKey.map f)
        (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  have h := ChainSend.deriveFast_map hs (chainKey := chainKey) (pqKey := ChainSend.salt a present pqKey)
  simp only [Symmetric.Step.map, Symmetric.Material.map, ChainSend.salt_map ha] at h
  have hk := congrArg Symmetric.Step.nextChainKey h
  have hc := congrArg (fun x => x.material.cipherKey) h
  have hm := congrArg (fun x => x.material.macKey) h
  have hi := congrArg (fun x => x.material.iv) h
  simp only at hk hc hm hi
  simp only [openCore, finish_map ha, ha.and, OpenResult.get_map ha, identityMask_map ha,
    ChainSend.flagMask_map ha, ChainSend.counterMask_map ha, ProtoReceive.openCore_map hd ho he hs ha,
    ProtoParse.parseCore_map hd ho ha, ChainSend.nextCounter_map hs ha, hk, hc, hm, hi]
include hd ho he hs ha in
theorem openChecked_map (present : B) (ratchet counter chainKey pqKey sender receiver wire expected : List B) :
    (openChecked d o aes s a present ratchet counter chainKey pqKey sender receiver wire expected).map (List.map f) =
      openChecked d' o' aes' s' a' (f present) (ratchet.map f) (counter.map f) (chainKey.map f) (pqKey.map f)
        (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  simp only [openChecked, List.length_map]
  split <;> simp [openCore_map hd ho he hs ha]
end

theorem finish_reject (nextKey nextCounter oldKey oldCounter opened : List (BitVec 8)) :
    finish ByteAuth.concrete 0 nextKey nextCounter oldKey oldCounter opened =
      0 :: (oldKey ++ oldCounter ++ List.replicate (opened.drop 1).length 0) := by
  simp only [finish, ChainSend.selectState_reject, ByteAuth.release_reject]

theorem compiled_openCore_correct (present : BVExpr 8)
    (ratchet counter chainKey pqKey sender receiver wire expected : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      present ratchet counter chainKey pqKey sender receiver wire expected).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      present ratchet counter chainKey pqKey sender receiver wire expected))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        present ratchet counter chainKey pqKey sender receiver wire expected))).vec.get index hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        (BVExpr.eval assign present) (ratchet.map (BVExpr.eval assign)) (counter.map (BVExpr.eval assign))
        (chainKey.map (BVExpr.eval assign)) (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.ChainReceive
