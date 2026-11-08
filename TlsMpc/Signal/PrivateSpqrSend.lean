import TlsMpc.Signal.PrivateSignalMessage
import TlsMpc.Signal.SpqrSend

/-! Active SPQR epoch send with no public epoch/index/counter varint widths.
Epoch selection, KEM/chunk transitions and recoverable persistence remain
external; this module consumes an already selected active chain/payload. -/
namespace TlsMpc.Signal.PrivateSpqrSend

structure Prepared (B : Type) where
  candidateState : List B
  wire : PrivateBuffer.Buffer B

def Prepared.map (f : B → B') (p : Prepared B) : Prepared B' :=
  ⟨p.candidateState.map f,p.wire.map f⟩

def oldState (i : SpqrSend.Input B) : List B := i.chainKey ++ i.counter ++ i.pqChainKey ++ i.pqCounter

def pqMessage (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (hasChunk : Bool) (epoch nextCounter : List B) (kind : B) (chunkIndex chunkData : List B) : PrivateBuffer.Buffer B :=
  let cap := if hasChunk then 52 else 17
  let chunk := if hasChunk then PrivateSend.join a cap [
    PrivateVarint.uint32 s a (SpqrMessage.chunkWord s a chunkIndex),PrivateSend.literal a cap chunkData]
    else PrivateSend.literal a cap []
  let content := PrivateSend.join a cap [PrivateSend.literal a cap [a.const 1],
    PrivateVarint.uint64 v a (Varint64.pack v a epoch),PrivateVarint.uint32 s a (Varint.pack s a nextCounter),
    PrivateSend.literal a cap [kind],chunk]
  PrivateProtobuf.gate a (SpqrMessage.kindMask a hasChunk kind) content

def prepare (o : Aes.Ops B) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (hasChunk withAddresses : Bool) (i : SpqrSend.Input B) : Prepared B :=
  let pqOutput := SpqrChain.materialFast s a i.pqChainKey i.pqCounter
  let nextPqCounter := ChainSend.nextCounter s a i.pqCounter
  let pq := pqMessage v s a hasChunk i.epoch nextPqCounter i.kind i.chunkIndex i.chunkData
  let derived := Symmetric.deriveFast s i.chainKey (pqOutput.drop 32)
  let wire := PrivateSignalMessage.message o s a withAddresses true i.version i.counter i.previous i.ratchet
    derived.material.cipherKey derived.material.iv derived.material.macKey i.sender i.receiver i.plaintext i.addresses pq
  let accepted := a.and (ChainSend.counterMask a i.counter)
    (a.and (ChainSend.counterMask a i.pqCounter) (SpqrSend.epochMask a i.epoch))
  ⟨derived.nextChainKey ++ ChainSend.nextCounter s a i.counter ++ pqOutput.take 32 ++ nextPqCounter,
    PrivateProtobuf.gate a accepted wire⟩

def output (a : ByteAuth.Ops B) (old : List B) (p : Prepared B) : List B :=
  p.wire.valid :: (ChainSend.selectState a p.wire.valid p.candidateState old ++
    (PrivateBuffer.output a p.wire).drop 1)

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}
  (ho : Aes.Hom o o' f) (hv : Varint64.Hom v v' f fv)
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem oldState_map (i : SpqrSend.Input B) : (oldState i).map f = oldState (i.map f) := by
  simp only [oldState,List.map_append,SpqrSend.Input.map]
include hv hs

theorem pqMessage_map (hasChunk : Bool) (epoch nextCounter : List B) (kind : B) (chunkIndex chunkData : List B) :
    (pqMessage v s a hasChunk epoch nextCounter kind chunkIndex chunkData).map f =
      pqMessage v' s' a' hasChunk (epoch.map f) (nextCounter.map f) (f kind) (chunkIndex.map f) (chunkData.map f) := by
  simp only [pqMessage,PrivateProtobuf.gate_map ha,SpqrMessage.kindMask_map ha,PrivateSend.join_map ha,
    PrivateSend.literal_map ha,PrivateVarint.uint64_map hv ha,PrivateVarint.uint32_map hs ha,
    Varint64.pack_map hv ha,Varint.pack_map hs ha,List.map_cons,List.map_nil,ha.const]
  split <;> simp only [PrivateSend.join_map ha,PrivateSend.literal_map ha,PrivateVarint.uint32_map hs ha,
    SpqrMessage.chunkWord_map hs ha,List.map_cons,List.map_nil]
include ho

theorem prepare_map (hasChunk withAddresses : Bool) (i : SpqrSend.Input B) :
    (prepare o v s a hasChunk withAddresses i).map f = prepare o' v' s' a' hasChunk withAddresses (i.map f) := by
  have hd := ChainSend.deriveFast_map hs (chainKey := i.chainKey)
    (pqKey := (SpqrChain.materialFast s a i.pqChainKey i.pqCounter).drop 32)
  simp only [Symmetric.Step.map,Symmetric.Material.map,List.map_drop,SpqrChain.materialFast_map hs ha] at hd
  have hk := congrArg Symmetric.Step.nextChainKey hd
  have hc := congrArg (fun d => d.material.cipherKey) hd
  have hm := congrArg (fun d => d.material.macKey) hd
  have hi := congrArg (fun d => d.material.iv) hd
  simp only at hk hc hm hi
  simp only [prepare,Prepared.map,SpqrSend.Input.map,List.map_append,List.map_take,
    PrivateProtobuf.gate_map ha,PrivateSignalMessage.message_map ho hs ha,pqMessage_map hv hs ha,
    hk,hc,hm,hi,SpqrChain.materialFast_map hs ha,ChainSend.nextCounter_map hs ha,
    ha.and,ChainSend.counterMask_map ha,SpqrSend.epochMask_map ha]

omit ho hv hs in
theorem output_map (old : List B) (p : Prepared B) :
    (output a old p).map f = output a' (old.map f) (p.map f) := by
  simp only [output,List.map_cons,List.map_append,List.map_drop,PrivateBuffer.output_map ha,
    ChainSend.selectState_map ha,Prepared.map,PrivateBuffer.Buffer.map]

end Refinement
end TlsMpc.Signal.PrivateSpqrSend
