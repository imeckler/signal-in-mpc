import TlsMpc.Signal.SpqrParse
import TlsMpc.Signal.SpqrChain
import TlsMpc.Signal.PrivateProtobuf

/-! Candidate active-epoch in-order SPQR receive material. Input state is the
selected established receiving epoch/chain/counter, all shared. No supplied
message key or KEM secret. A bounded private-length wire is actually parsed;
truncation may not borrow bytes from its zero-capacity padding. Only V1 kind0,
matching epoch and exact next index are supported. KEM/chunks/acks/epoch switches,
skipped/old keys and full state admission are separate. This returns a candidate:
the outer Signal MAC/decrypt transaction MUST succeed before committing it. -/
namespace TlsMpc.Signal.ActiveSpqrReceive
open Std.Tactic.BVDecide

/-- Conservative bounded profile keeps actual SPQR's counter arithmetic inside
its documented hax resource precondition. Exhaustion rejects, never wraps. -/
def counterProfileMask (a : ByteAuth.Ops B) (counter : List B) : B :=
  a.and (a.not (a.maskBit (OpenResult.get a counter 0) 7))
    (a.not (ByteAuth.equalMask a counter [a.const 127,a.const 255,a.const 255,a.const 255]))

def mask (d : VarintDecode.Spqr.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (epoch counter : List B) (wire : PrivateBuffer.Buffer B) : B :=
  let stages := SpqrParse.stages d a wire.data
  let endPos := SpqrParse.cursor a stages.kind
  a.and wire.valid (a.and (SpqrParse.acceptedMask a wire.data stages)
    (a.and (ByteAuth.eqMask a (SpqrParse.kindByte a stages) (a.const 0))
      (a.and (ByteAuth.equalMask a (SpqrParse.value a stages.epoch) epoch)
        (a.and (ByteAuth.equalMask a ((SpqrParse.value a stages.index).drop 4) (ChainSend.nextCounter s a counter))
          (a.and (counterProfileMask a counter)
            (a.and (ByteAuth.equalMask a (endPos.take 6) (List.replicate 6 (a.const 0)))
              (a.not (PrivateBuffer.less a wire.lengthBits (PrivateBuffer.decodeLength a (endPos.drop 6))))))))))

/-- status, selected epoch8/chain32/counter4, private message key32. The input
wire encoding is validity8/lengthBE16/capacity32; its actual length stays shared.
Rejected candidate preserves old receiving state and releases zero key. -/
def prepare (d : VarintDecode.Spqr.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (epoch key counter encodedWire : List B) : List B :=
  let wire := PrivateBuffer.fromWire a 32 encodedWire
  let accepted := mask d s a epoch counter wire
  let material := SpqrChain.materialFast s a key counter
  accepted :: (ChainSend.selectState a accepted
    (epoch ++ material.take 32 ++ ChainSend.nextCounter s a counter) (epoch++key++counter) ++
    ByteAuth.release a accepted (material.drop 32))

section Refinement
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fv : V → V'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hd hs ha

theorem epoch_stage_map (raw : List B) :
    (SpqrParse.stages d a raw).epoch.map f=(SpqrParse.stages d' a' (raw.map f)).epoch :=
  congrArg SpqrParse.Stages.epoch (SpqrParse.stages_map hd ha raw)
theorem index_stage_map (raw : List B) :
    (SpqrParse.stages d a raw).index.map f=(SpqrParse.stages d' a' (raw.map f)).index :=
  congrArg SpqrParse.Stages.index (SpqrParse.stages_map hd ha raw)
theorem kind_stage_map (raw : List B) :
    (SpqrParse.stages d a raw).kind.map f=(SpqrParse.stages d' a' (raw.map f)).kind :=
  congrArg SpqrParse.Stages.kind (SpqrParse.stages_map hd ha raw)

theorem mask_map (epoch counter : List B) (wire : PrivateBuffer.Buffer B) :
    f (mask d s a epoch counter wire)=mask d' s' a' (epoch.map f) (counter.map f) (wire.map f) := by
  simp only [mask,ha.and,ha.not,ha.const,SpqrParse.stages_map hd ha,SpqrParse.cursor_map ha,
    SpqrParse.acceptedMask_map ha,SpqrParse.kindByte_map ha,SpqrParse.value_map ha,
    ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,ChainSend.nextCounter_map hs ha,
    counterProfileMask,ha.maskBit,OpenResult.get_map ha,PrivateBuffer.less_map ha,PrivateBuffer.decodeLength_map ha,
    List.map_take,List.map_drop,List.map_replicate,List.map_cons,List.map_nil,PrivateBuffer.Buffer.map,
    epoch_stage_map hd hs ha,index_stage_map hd hs ha,kind_stage_map hd hs ha]

theorem prepare_map (epoch key counter encodedWire : List B) :
    (prepare d s a epoch key counter encodedWire).map f=
    prepare d' s' a' (epoch.map f) (key.map f) (counter.map f) (encodedWire.map f) := by
  simp only [prepare,List.map_cons,List.map_append,ChainSend.selectState_map ha,
    ByteAuth.release_map ha,SpqrChain.materialFast_map hs ha,List.map_take,List.map_drop,
    ChainSend.nextCounter_map hs ha,mask_map hd hs ha,PrivateBuffer.fromWire_map ha]
end Refinement

theorem compiled_prepare_correct (epoch key counter wire : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (prepare VarintDecode.Spqr.symbolic Sha256.symbolic ByteAuth.symbolic epoch key counter wire)
      (prepare VarintDecode.Spqr.concrete Sha256.concrete ByteAuth.concrete
        (epoch.map (BVExpr.eval assign)) (key.map (BVExpr.eval assign))
        (counter.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,prepare_map (VarintDecode.Spqr.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.ActiveSpqrReceive
