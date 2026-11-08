import TlsMpc.Signal.PrivateNewDhReceive
import TlsMpc.Signal.PrivateProtoParseV1Proofs

namespace TlsMpc.Signal.PrivateNewDhReceive
open Std.Tactic.BVDecide
section Refinement
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem conjunction_map (masks : List B) :
    f (conjunction a masks)=conjunction a' (masks.map f) := by
  induction masks with
  | nil => exact ha.const 255
  | cons x xs ih => simp only [conjunction,List.map_cons,ha.and,ih]

theorem listBytes_map (raw : List B) :
    f ∘ (listBytes a raw : SkippedKeys.Bytes B n)=listBytes a' (raw.map f) := by
  funext i
  exact OpenResult.get_map ha raw i.val

theorem nextEntry_map (remote chain : List B) :
    (nextEntry a remote chain).map f=nextEntry a' (remote.map f) (chain.map f) := by
  have empty : (fun i : Fin 0 => (Fin.elim0 i : SkippedKeys.Slot B).map f)=
      (fun i : Fin 0 => (Fin.elim0 i : SkippedKeys.Slot B')) := by
    funext i;exact Fin.elim0 i
  simp only [nextEntry,ReceiverStore.Entry.map,listBytes_map ha,ha.const,List.map_cons,List.map_nil,empty]

theorem selectResult_map (accepted : B) (old : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq : List B) (next : RatchetStep.State B)
    (remote nextReceiverChain pqCandidate plaintext : List B) :
    (selectResult a accepted old receivers oldPq next remote nextReceiverChain pqCandidate plaintext).map f=
    selectResult a' (f accepted) (old.map f) (receivers.map (ReceiverStore.Entry.map f)) (oldPq.map f)
      (next.map f) (remote.map f) (nextReceiverChain.map f) (pqCandidate.map f) (plaintext.map f) := by
  simp only [selectResult,List.map_cons,List.map_append,ChainSend.selectState_map ha,RatchetStep.bytes_map,
    ReceiverStore.bytes_map,ReceiverStore.insert_map ha,nextEntry_map ha,List.map_take,
    ByteAuth.release_map ha,ha.const,List.map_nil]

include ho

theorem pqWire_map (wire : List B) (parsed : PrivateProtoParseV1.Parsed B V) :
    (pqWire o a wire parsed).map f=pqWire o' a' (wire.map f) (parsed.map f fv) := by
  have field:=ProtoParse.getField_map ho ha parsed.state 4
  have present:=congrArg ProtoParse.Field.present field
  have length:=congrArg ProtoParse.Field.length field
  have offset:=congrArg ProtoParse.Field.offset field
  simp only [ProtoParse.Field.map] at present length offset
  simp only [pqWire,List.map_cons,ha.and,PrivateProtoParseV1.Parsed.map,ho.ule,ho.const,
    List.map_append,List.map_drop,Word64.bytes_map ho,SliceAt.readCore_map ho ha,present,length,offset]
include hs
omit ho ha in
theorem derive_map (root receiving sending : List B) :
    ((RatchetStep.derive s root receiving sending).1.map f,
      (RatchetStep.derive s root receiving sending).2.1.map f,
      (RatchetStep.derive s root receiving sending).2.2.map f)=
    RatchetStep.derive s' (root.map f) (receiving.map f) (sending.map f) := by
  simp only [RatchetStep.derive,DhRatchet.materialFast_map hs,List.map_take,List.map_drop]

include hd he

theorem receive_map (old : RatchetStep.State B) (receivers : List (ReceiverStore.Entry B 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) :
    (receive d o aes s a old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire).map f=
    receive d' o' aes' s' a' (old.map f) (receivers.map (ReceiverStore.Entry.map f))
      (oldPq.map f) (sender.map f) (receiver.map f) (newPrivate.map f) (newPublic.map f)
      (receiveAgreement.map f) (sendAgreement.map f) (encodedWire.map f) := by
  let p := PrivateProtoParseV1.parse d o a (encodedWire.drop 3) (OpenResult.get a encodedWire 1)
    (OpenResult.get a encodedWire 2) (OpenResult.get a encodedWire 0)
  let p' := PrivateProtoParseV1.parse d' o' a' ((encodedWire.map f).drop 3) (OpenResult.get a' (encodedWire.map f) 1)
    (OpenResult.get a' (encodedWire.map f) 2) (OpenResult.get a' (encodedWire.map f) 0)
  have hp : p.map f fv=p' := by
    simpa only [p,p',List.map_drop,OpenResult.get_map ha] using
      PrivateProtoParseV1.parse_map hd ho ha (encodedWire.drop 3) (OpenResult.get a encodedWire 1)
        (OpenResult.get a encodedWire 2) (OpenResult.get a encodedWire 0)
  have hstate:=congrArg PrivateProtoParseV1.Parsed.state hp
  have hvalid:=congrArg PrivateProtoParseV1.Parsed.valid hp
  have hmeta:=congrArg PrivateProtoParseV1.Parsed.metadata hp
  simp only [PrivateProtoParseV1.Parsed.map] at hstate hvalid hmeta
  have fields (i) := ProtoParse.getField_map ho ha p.state i
  simp only [hstate] at fields
  have present (i) := congrArg ProtoParse.Field.present (fields i)
  have length (i) := congrArg ProtoParse.Field.length (fields i)
  have offset (i) := congrArg ProtoParse.Field.offset (fields i)
  have scalar (i) := congrArg ProtoParse.Field.scalar (fields i)
  simp only [ProtoParse.Field.map] at present length offset scalar
  have hpq : (ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
      ((oldPq.drop 40).take 4) (pqWire o a (encodedWire.drop 3) p)).map f=
    ActiveSpqrReceive.prepare d' s' a' ((oldPq.map f).take 8) (((oldPq.map f).drop 8).take 32)
      (((oldPq.map f).drop 40).take 4) (pqWire o' a' ((encodedWire.map f).drop 3) p') := by
    rw [ActiveSpqrReceive.prepare_map hd hs ha]
    simp only [List.map_take,List.map_drop,pqWire_map ho ha,hp]
  have dr:=derive_map hs old.root receiveAgreement sendAgreement
  have root:=congrArg Prod.fst dr
  have recv:=congrArg (fun x => x.2.1) dr
  have send:=congrArg (fun x => x.2.2) dr
  dsimp only at root recv send
  have mat:=ChainSend.deriveFast_map hs (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
    ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
      ((oldPq.drop 40).take 4) (pqWire o a (encodedWire.drop 3) p)).drop 45)
  simp only [List.map_drop,hpq,recv] at mat
  have ck:=congrArg Symmetric.Step.nextChainKey mat
  have cipher:=congrArg (fun x=>x.material.cipherKey) mat
  have mac:=congrArg (fun x=>x.material.macKey) mat
  have iv:=congrArg (fun x=>x.material.iv) mat
  simp only [Symmetric.Step.map,Symmetric.Material.map] at ck cipher mac iv
  have opened:=CbcOpen.openCore_map he ha
    (Symmetric.deriveFast s (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
      ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
        ((oldPq.drop 40).take 4) (pqWire o a (encodedWire.drop 3) p)).drop 45)).material.cipherKey
    (Symmetric.deriveFast s (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
      ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
        ((oldPq.drop 40).take 4) (pqWire o a (encodedWire.drop 3) p)).drop 45)).material.iv
    (SliceAt.readCore o a 96 ((encodedWire.drop 3).drop 1)
      (ProtoParse.getField o a p.state 3).offset (ProtoParse.getField o a p.state 3).length)
  simp only [cipher,iv,SliceAt.readCore_map ho ha,List.map_drop,offset,length] at opened
  have known:=ReceiverStore.lookup_map ha (listBytes a (p.metadata.take 32)) receivers
  simp only [listBytes_map ha,List.map_take,hmeta] at known
  have knownValid:=congrArg ReceiverStore.Entry.valid known
  simp only [ReceiverStore.Entry.map] at knownValid
  dsimp only [p,p'] at hstate hvalid hmeta hpq ck cipher mac iv opened knownValid present length scalar
  simp only [receive,selectResult_map ha,conjunction_map ha,List.map_cons,List.map_nil,
    List.map_append,List.map_take,List.map_drop,List.map_replicate,ha.const,ha.not,ha.and,
    OpenResult.get_map ha,ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,
    Word64.eq_map ho ha,ho.band,ho.const,PrivateMessageMac.verify_map ho hs ha,
    RatchetStep.State.map,RatchetStep.previousCounter_map hs ha,
    RatchetStep.bytes_map,DhRatchet.agreementMask_map ha,OpenResult.encodeLength_map ha,
    List.length_map,List.length_drop,apply_ite,hvalid,hmeta,hpq,root,recv,send,ck,cipher,mac,iv,opened,knownValid,
    present,length,scalar]

end Refinement
theorem compiled_receive_correct (old : RatchetStep.State (BVExpr 8))
    (receivers : List (ReceiverStore.Entry (BVExpr 8) 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire : List (BVExpr 8))
    (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (receive VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire)
      (receive VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        (old.map (BVExpr.eval assign)) (receivers.map (ReceiverStore.Entry.map (BVExpr.eval assign)))
        (oldPq.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
        (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign))
        (receiveAgreement.map (BVExpr.eval assign)) (sendAgreement.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,receive_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign)
    (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateNewDhReceive
