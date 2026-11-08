import TlsMpc.Signal.PrivateSessionReceiveV1
import TlsMpc.Signal.PrivateNewDhReceiveSplitProofs

namespace TlsMpc.Signal.PrivateSessionReceiveV1

theorem finish_reject (known : BitVec 8) (hknown : known=0 ∨ known=255)
    (old next : RatchetStep.State (BitVec 8))
    (receivers : List (ReceiverStore.Entry (BitVec 8) 0))
    (oldPq remote chain counter pq plain : List (BitVec 8))
    (selected : ReceiverStore.Entry (BitVec 8) 0) :
 finish ByteAuth.concrete 0 known old next receivers oldPq remote chain counter pq plain selected =
   0 :: (old.bytes ++ ReceiverStore.bytes receivers ++ oldPq ++
     List.replicate (2+(plain.take 80).length) 0) := by
 unfold finish
 dsimp only
 rw [ChainSend.selectState_reject,ReceiverStore.insert_reject 0 _ receivers (by decide)]
 simp only [replace,ReceiverStore.replaceFirst_reject,ChainSend.selectState_reject,ByteAuth.release_reject]
 have hs : List.zipWith (ReceiverStore.choose ByteAuth.concrete known) receivers receivers=receivers := by
  rcases hknown with h|h <;> subst known <;> induction receivers with
  | nil => rfl
  | cons e rest ih => simp only [List.zipWith,ReceiverStore.choose_reject,ReceiverStore.choose_accept,ih]
 rw [hs]
 simp only [List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_zero]

-- This exact expression is the sender/root selection in finish. In particular
-- the136-byte root/private/public/sending-chain state cannot change on known path.
theorem known_sender_preserved (old next : RatchetStep.State (BitVec 8))
    (h : old.bytes.length=next.bytes.length) :
 ChainSend.selectState ByteAuth.concrete 255
   (ChainSend.selectState ByteAuth.concrete 255 old.bytes next.bytes) old.bytes=old.bytes := by
 rw [ChainSend.selectState_accept _ _ h,ChainSend.selectState_accept _ _ rfl]



open Std.Tactic.BVDecide PrivateNewDhReceive PrivateNewDhReceiveSplit
section Refinement
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem lookup_map (remote : List B) (old : List (ReceiverStore.Entry B 0)) :
 (lookup a remote old).map f=lookup a' (remote.map f) (old.map (ReceiverStore.Entry.map f)) := by
 simp only [lookup,ReceiverStore.lookup_map ha,listBytes_map ha]
theorem replace_map (allow : B) (remote : List B) (next : ReceiverStore.Entry B 0)
    (old : List (ReceiverStore.Entry B 0)) :
 (replace a allow remote next old).map (ReceiverStore.Entry.map f)=
   replace a' (f allow) (remote.map f) (next.map f) (old.map (ReceiverStore.Entry.map f)) := by
 simp only [replace,ReceiverStore.replaceFirst_map ha,listBytes_map ha]
theorem knownEntry_map (chain counter : List B) (selected : ReceiverStore.Entry B 0) :
 (⟨a.const 255,selected.ratchet,listBytes a chain,listBytes a counter,fun j=>Fin.elim0 j⟩ : ReceiverStore.Entry B 0).map f=
 (⟨a'.const 255,(selected.map f).ratchet,listBytes a' (chain.map f),listBytes a' (counter.map f),fun j=>Fin.elim0 j⟩ : ReceiverStore.Entry B' 0) := by
 have empty : (fun i : Fin 0 => (Fin.elim0 i : SkippedKeys.Slot B).map f)=
     (fun i : Fin 0 => (Fin.elim0 i : SkippedKeys.Slot B')) := by
  funext i;exact Fin.elim0 i
 simp only [ReceiverStore.Entry.map,listBytes_map ha,ha.const,empty]
theorem finish_map (accepted known : B) (old next : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq remote chain counter pq plain : List B)
    (selected : ReceiverStore.Entry B 0) :
 (finish a accepted known old next receivers oldPq remote chain counter pq plain selected).map f=
 finish a' (f accepted) (f known) (old.map f) (next.map f) (receivers.map (ReceiverStore.Entry.map f))
   (oldPq.map f) (remote.map f) (chain.map f) (counter.map f) (pq.map f) (plain.map f) (selected.map f) := by
 simp only [finish,List.map_cons,List.map_append,ChainSend.selectState_map ha,RatchetStep.bytes_map,
   ReceiverStore.bytes_map,ReceiverStore.insert_map ha,nextEntry_map ha,List.map_take,
   ByteAuth.release_map ha,ha.const,List.map_nil,ReceiverStore.chooseList_map ha,replace_map ha,knownEntry_map ha]

include hd ho he hs in
theorem receiveSummary_map (old : RatchetStep.State B) (receivers : List (ReceiverStore.Entry B 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) (summary : Summary B V) :
    (receiveSummary d o aes s a old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire summary).map f=
    receiveSummary d' o' aes' s' a' (old.map f) (receivers.map (ReceiverStore.Entry.map f))
      (oldPq.map f) (sender.map f) (receiver.map f) (newPrivate.map f) (newPublic.map f)
      (receiveAgreement.map f) (sendAgreement.map f) (encodedWire.map f) (summary.map f fv) := by
  have hpq : (ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
      ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).map f=
    ActiveSpqrReceive.prepare d' s' a' ((oldPq.map f).take 8) (((oldPq.map f).drop 8).take 32)
      (((oldPq.map f).drop 40).take 4) (pqWireSummary o' a' ((encodedWire.map f).drop 3) (summary.map f fv)) := by
    rw [ActiveSpqrReceive.prepare_map hd hs ha]
    simp only [List.map_take,List.map_drop,pqWireSummary_map ho ha]
  have dr:=derive_map hs old.root receiveAgreement sendAgreement
  have root:=congrArg Prod.fst dr
  have recv:=congrArg (fun x => x.2.1) dr
  have send:=congrArg (fun x => x.2.2) dr
  dsimp only at root recv send
  have selected:=lookup_map ha summary.remote receivers
  have knownValid:=congrArg ReceiverStore.Entry.valid selected
  simp only [ReceiverStore.Entry.map] at knownValid
  have knownChain : (List.ofFn (lookup a summary.remote receivers).chain).map f=
      List.ofFn (lookup a' (summary.remote.map f) (receivers.map (ReceiverStore.Entry.map f))).chain := by
    rw [List.map_ofFn];exact congrArg (fun e=>List.ofFn e.chain) selected
  have knownCounter : (List.ofFn (lookup a summary.remote receivers).counter).map f=
      List.ofFn (lookup a' (summary.remote.map f) (receivers.map (ReceiverStore.Entry.map f))).counter := by
    rw [List.map_ofFn];exact congrArg (fun e=>List.ofFn e.counter) selected
  let inputChain:=ChainSend.selectState a (ByteAuth.eqMask a (lookup a summary.remote receivers).valid (a.const 255))
    (List.ofFn (lookup a summary.remote receivers).chain) (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
  have hchain : inputChain.map f=ChainSend.selectState a'
      (ByteAuth.eqMask a' (lookup a' (summary.remote.map f) (receivers.map (ReceiverStore.Entry.map f))).valid (a'.const 255))
      (List.ofFn (lookup a' (summary.remote.map f) (receivers.map (ReceiverStore.Entry.map f))).chain)
      (RatchetStep.derive s' (old.root.map f) (receiveAgreement.map f) (sendAgreement.map f)).2.1 := by
    simp only [inputChain,ChainSend.selectState_map ha,ByteAuth.eqMask_map ha,knownValid,knownChain,recv,ha.const]
  have mat:=ChainSend.deriveFast_map hs inputChain
    ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
      ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).drop 45)
  simp only [List.map_drop,hpq,hchain] at mat
  have ck:=congrArg Symmetric.Step.nextChainKey mat
  have cipher:=congrArg (fun x=>x.material.cipherKey) mat
  have mac:=congrArg (fun x=>x.material.macKey) mat
  have iv:=congrArg (fun x=>x.material.iv) mat
  simp only [Symmetric.Step.map,Symmetric.Material.map] at ck cipher mac iv
  have opened:=CbcOpen.openCore_map he ha
    (Symmetric.deriveFast s inputChain
      ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
        ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).drop 45)).material.cipherKey
    (Symmetric.deriveFast s inputChain
      ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
        ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).drop 45)).material.iv
    (SliceAt.readCore o a 96 ((encodedWire.drop 3).drop 1)
      summary.cipherOffset summary.cipherLength)
  simp only [cipher,iv,SliceAt.readCore_map ho ha,List.map_drop,Summary.map] at opened
  dsimp only [inputChain] at ck cipher mac iv opened
  simp only [receiveSummary,Summary.map,finish_map ha,conjunction_map ha,List.map_cons,List.map_nil,
    List.map_append,List.map_take,List.map_drop,List.map_replicate,ha.const,ha.not,ha.and,
    OpenResult.get_map ha,ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,
    Word64.eq_map ho ha,Word64.bytes_map ho,ho.band,ho.const,PrivateMessageMac.verify_map ho hs ha,
    RatchetStep.State.map,RatchetStep.previousCounter_map hs ha,
    RatchetStep.bytes_map,DhRatchet.agreementMask_map ha,OpenResult.encodeLength_map ha,
    List.length_map,List.length_drop,apply_ite,Unpad.chooseByte_map ha,ChainSend.counterMask_map ha,ChainSend.nextCounter_map hs ha,knownChain,knownCounter,selected,hpq,root,recv,send,ck,cipher,mac,iv,opened,knownValid,
    ]

include hd ho he hs in
theorem parsed_receive_map (old : RatchetStep.State B) (receivers : List (ReceiverStore.Entry B 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) :
 (receiveSummary d o aes s a old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire
    (parseSummary d o a encodedWire)).map f=
 receiveSummary d' o' aes' s' a' (old.map f) (receivers.map (ReceiverStore.Entry.map f))
   (oldPq.map f) (sender.map f) (receiver.map f) (newPrivate.map f) (newPublic.map f)
   (receiveAgreement.map f) (sendAgreement.map f) (encodedWire.map f)
   (parseSummary d' o' a' (encodedWire.map f)) := by
 rw [receiveSummary_map hd ho he hs ha,parseSummary_map hd ho ha]

end Refinement


theorem compiled_receiveSummary_correct (old : RatchetStep.State (BVExpr 8)) (receivers : List (ReceiverStore.Entry (BVExpr 8) 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire : List (BVExpr 8)) (summary : Summary (BVExpr 8) (BVExpr 64))
    (assign : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement
   (receiveSummary VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
     old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire summary)
   (receiveSummary VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
     (old.map (BVExpr.eval assign)) (receivers.map (ReceiverStore.Entry.map (BVExpr.eval assign)))
     (oldPq.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
     (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign))
     (receiveAgreement.map (BVExpr.eval assign)) (sendAgreement.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (summary.map (BVExpr.eval assign) (BVExpr.eval assign))) assign := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,receiveSummary_map (VarintDecode.Spqr.evaluationHom assign)
   (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_parsed_receive_correct (old : RatchetStep.State (BVExpr 8)) (receivers : List (ReceiverStore.Entry (BVExpr 8) 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire : List (BVExpr 8))
    (assign : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement
   (receiveSummary VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
     old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire (parseSummary VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire))
   (receiveSummary VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
     (old.map (BVExpr.eval assign)) (receivers.map (ReceiverStore.Entry.map (BVExpr.eval assign)))
     (oldPq.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
     (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign))
     (receiveAgreement.map (BVExpr.eval assign)) (sendAgreement.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (parseSummary VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (wire.map (BVExpr.eval assign)))) assign := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,parsed_receive_map (VarintDecode.Spqr.evaluationHom assign)
   (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateSessionReceiveV1
