import TlsMpc.Signal.PrivateNewDhReceiveSplit
namespace TlsMpc.Signal.PrivateNewDhReceiveSplit
open Std.Tactic.BVDecide

theorem word_pack_bytes (word : BitVec 64) : Word64.concrete.pack (Word64.bytes Word64.concrete word)=word := by
  change (((word.extractLsb' 56 8 ++ word.extractLsb' 48 8) ++
    (word.extractLsb' 40 8 ++ word.extractLsb' 32 8)) ++
    ((word.extractLsb' 24 8 ++ word.extractLsb' 16 8) ++
    (word.extractLsb' 8 8 ++ word.extractLsb' 0 8)))=word
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=56) (start₁:=48) (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=40) (start₁:=32) (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=48) (start₁:=32) (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=24) (start₁:=16) (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=8) (start₁:=0) (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=16) (start₁:=0) (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂:=32) (start₁:=0) (by decide)]
  exact BitVec.extractLsb'_eq_self
theorem decode_encode (x : Summary (BitVec 8) (BitVec 64)) (hremote : x.remote.length=32) :
    decode Word64.concrete ByteAuth.concrete (encode Word64.concrete x)=x := by
  cases x with
  | mk valid remote counter cipherOffset cipherLength pqOffset pqLength pqPresent addressPresent =>
    simp only [encode,decode,Word64.bytes_length,List.length_cons,List.length_nil,List.length_append] at hremote ⊢
    simp [List.drop_eq_nil_of_le,List.drop_append,List.take_append,hremote,Word64.bytes_length,word_pack_bytes,OpenResult.get]

section Refinement
open PrivateNewDhReceive
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho ha

theorem fromParsed_map (p : PrivateProtoParseV1.Parsed B V) :
    (fromParsed o a p).map f fv=fromParsed o' a' (p.map f fv) := by
  have fields (i):=ProtoParse.getField_map ho ha p.state i
  have present (i):=congrArg ProtoParse.Field.present (fields i)
  have offset (i):=congrArg ProtoParse.Field.offset (fields i)
  have length (i):=congrArg ProtoParse.Field.length (fields i)
  have scalar (i):=congrArg ProtoParse.Field.scalar (fields i)
  simp only [ProtoParse.Field.map] at present offset length scalar
  simp only [fromParsed,Summary.map,PrivateProtoParseV1.Parsed.map,List.map_take,present,offset,length,scalar]

omit ha in
theorem encode_map (x : Summary B V) :
    (encode o x).map f=encode o' (x.map f fv) := by
  simp only [encode,Summary.map,List.map_cons,List.map_nil,List.map_append,Word64.bytes_map ho]

theorem decode_map (raw : List B) :
    (decode o a raw).map f fv=decode o' a' (raw.map f) := by
  simp only [decode,Summary.map,OpenResult.get_map ha,ho.pack,List.map_take,List.map_drop]

theorem pqWireSummary_map (wire : List B) (x : Summary B V) :
    (pqWireSummary o a wire x).map f=pqWireSummary o' a' (wire.map f) (x.map f fv) := by
  simp only [pqWireSummary,Summary.map,List.map_cons,List.map_append,List.map_drop,ha.and,
    ho.ule,ho.const,Word64.bytes_map ho,SliceAt.readCore_map ho ha]
include hd

theorem parseSummary_map (encodedWire : List B) :
    (parseSummary d o a encodedWire).map f fv=parseSummary d' o' a' (encodedWire.map f) := by
  simp only [parseSummary,fromParsed_map ho ha,PrivateProtoParseV1.parse_map hd ho ha,
    OpenResult.get_map ha,List.map_drop]

theorem parseSummaryBytes_map (encodedWire : List B) :
    (parseSummaryBytes d o a encodedWire).map f=parseSummaryBytes d' o' a' (encodedWire.map f) := by
  simp only [parseSummaryBytes,encode_map ho,parseSummary_map hd ho ha]

include hd he hs
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
  have mat:=ChainSend.deriveFast_map hs (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
    ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
      ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).drop 45)
  simp only [List.map_drop,hpq,recv] at mat
  have ck:=congrArg Symmetric.Step.nextChainKey mat
  have cipher:=congrArg (fun x=>x.material.cipherKey) mat
  have mac:=congrArg (fun x=>x.material.macKey) mat
  have iv:=congrArg (fun x=>x.material.iv) mat
  simp only [Symmetric.Step.map,Symmetric.Material.map] at ck cipher mac iv
  have opened:=CbcOpen.openCore_map he ha
    (Symmetric.deriveFast s (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
      ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
        ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).drop 45)).material.cipherKey
    (Symmetric.deriveFast s (RatchetStep.derive s old.root receiveAgreement sendAgreement).2.1
      ((ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
        ((oldPq.drop 40).take 4) (pqWireSummary o a (encodedWire.drop 3) summary)).drop 45)).material.iv
    (SliceAt.readCore o a 96 ((encodedWire.drop 3).drop 1)
      summary.cipherOffset summary.cipherLength)
  simp only [cipher,iv,SliceAt.readCore_map ho ha,List.map_drop,Summary.map] at opened
  have known:=ReceiverStore.lookup_map ha (listBytes a summary.remote) receivers
  simp only [listBytes_map ha] at known
  have knownValid:=congrArg ReceiverStore.Entry.valid known
  simp only [ReceiverStore.Entry.map] at knownValid
  simp only [receiveSummary,Summary.map,selectResult_map ha,conjunction_map ha,List.map_cons,List.map_nil,
    List.map_append,List.map_take,List.map_drop,List.map_replicate,ha.const,ha.not,ha.and,
    OpenResult.get_map ha,ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,
    Word64.eq_map ho ha,ho.band,ho.const,PrivateMessageMac.verify_map ho hs ha,
    RatchetStep.State.map,RatchetStep.previousCounter_map hs ha,
    RatchetStep.bytes_map,DhRatchet.agreementMask_map ha,OpenResult.encodeLength_map ha,
    List.length_map,List.length_drop,apply_ite,hpq,root,recv,send,ck,cipher,mac,iv,opened,knownValid,
    ]

end Refinement

theorem parseSummary_remote_length (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V)
    (a : ByteAuth.Ops B) (encodedWire : List B) : (parseSummary d o a encodedWire).remote.length=32 := by
  simp only [parseSummary,fromParsed,List.length_take,PrivateProtoParseV1.parse,ByteAuth.release,
    List.length_map,PrivateProtoParseV1.metadata_length]
  rfl

theorem encode_length (o : Word64.Ops B V) (x : Summary B V) (hremote : x.remote.length=32) :
    (encode o x).length=75 := by
  simp only [encode,List.length_cons,List.length_append,List.length_nil,Word64.bytes_length,hremote]

theorem decoded_split_agreement (old : RatchetStep.State (BitVec 8))
    (receivers : List (ReceiverStore.Entry (BitVec 8) 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire : List (BitVec 8)) :
    receiveSummary VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
      old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire
      (decode Word64.concrete ByteAuth.concrete
        (parseSummaryBytes VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire))=
    PrivateNewDhReceive.receive VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
      old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire := by
  unfold parseSummaryBytes
  rw [decode_encode _ (parseSummary_remote_length _ _ _ _)]
  exact split_agreement _ _ _ _ _ old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire

theorem compiled_receiveSummary_correct (old : RatchetStep.State (BVExpr 8))
    (receivers : List (ReceiverStore.Entry (BVExpr 8) 0))
    (oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire : List (BVExpr 8))
    (summary : Summary (BVExpr 8) (BVExpr 64)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (receiveSummary VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement wire summary)
      (receiveSummary VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        (old.map (BVExpr.eval assign)) (receivers.map (ReceiverStore.Entry.map (BVExpr.eval assign)))
        (oldPq.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
        (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign))
        (receiveAgreement.map (BVExpr.eval assign)) (sendAgreement.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))
        (summary.map (BVExpr.eval assign) (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,receiveSummary_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign)
    (ByteAuth.evaluationHom assign)]

theorem compiled_parseSummary_correct (wire : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (parseSummaryBytes VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire)
      (parseSummaryBytes VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (wire.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,parseSummaryBytes_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateNewDhReceiveSplit
