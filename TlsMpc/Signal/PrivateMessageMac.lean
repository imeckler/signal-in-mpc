import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.SliceAt

/-! Signal MAC verification over an actual private-length original wire prefix.
The final8 bytes are located obliviously, not at the capacity end. Only public
capacity controls SHA work. No key, field offset, prefix length or tag is opened.
Full RustCrypto wrapper/source refinement remains separate. -/
namespace TlsMpc.Signal.PrivateMessageMac
open Std.Tactic.BVDecide

def contentBuffer (a : ByteAuth.Ops B) (wire : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let removed := PrivateBuffer.addLoop a wire.lengthBits (PrivateBuffer.publicLength a 65528) (List.range 16) (a.const 0)
  let valid := a.and wire.valid (a.and removed.2
    (a.not (PrivateBuffer.less a wire.lengthBits (PrivateBuffer.publicLength a 9))))
  PrivateProtobuf.gate a valid (PrivateBuffer.make a wire.data.length removed.1 wire.data)

def offset (o : Word64.Ops B V) (a : ByteAuth.Ops B) (content : PrivateBuffer.Buffer B) : V :=
  o.pack (List.replicate 6 (a.const 0) ++ PrivateBuffer.encodeLength a content.lengthBits)

def verify (o : Word64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat)
    (macKey sender receiver encodedWire : List B) : B :=
  let wire := PrivateBuffer.fromWire a capacity encodedWire
  let content := contentBuffer a wire
  let domain := PrivateSend.join a (capacity+66)
    [PrivateSend.literal a (capacity+66) (MessageMac.identity s sender ++ MessageMac.identity s receiver),content]
  let computed := PrivateHash.hmac s a macKey (capacity+66) domain
  let tag := SliceAt.readCore o a 8 wire.data (offset o a content) (o.const 8)
  a.and computed.valid (ByteAuth.equalMask a (computed.data.take 8) tag)

section Refinement
variable {o : Word64.Ops B V} {o' : Word64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (ho : Word64.Hom o o' f fv) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem contentBuffer_map (wire : PrivateBuffer.Buffer B) :
    (contentBuffer a wire).map f=contentBuffer a' (wire.map f) := by
  have h:=PrivateBuffer.addLoop_map ha wire.lengthBits (PrivateBuffer.publicLength a 65528) (List.range 16) (a.const 0)
  have bits:=congrArg Prod.fst h
  have carry:=congrArg Prod.snd h
  simp only [PrivateBuffer.publicLength_map ha,ha.const] at bits carry
  unfold contentBuffer
  rw [PrivateProtobuf.gate_map ha,PrivateBuffer.make_map ha]
  simp only [ha.and,ha.not,
    PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha,PrivateBuffer.Buffer.map,List.length_map,bits,carry]

include ho in
theorem offset_map (content : PrivateBuffer.Buffer B) :
    fv (offset o a content)=offset o' a' (content.map f) := by
  simp only [offset,ho.pack,List.map_append,List.map_replicate,ha.const,
    PrivateBuffer.encodeLength_map ha,PrivateBuffer.Buffer.map]

include ho hs

theorem verify_map (capacity : Nat) (macKey sender receiver encodedWire : List B) :
    f (verify o s a capacity macKey sender receiver encodedWire)=
    verify o' s' a' capacity (macKey.map f) (sender.map f) (receiver.map f) (encodedWire.map f) := by
  have w:=PrivateBuffer.fromWire_map ha capacity encodedWire
  have c:=contentBuffer_map ha (PrivateBuffer.fromWire a capacity encodedWire)
  have cd:=congrArg PrivateBuffer.Buffer.data c
  have cb:=congrArg PrivateBuffer.Buffer.lengthBits c
  have wd:=congrArg PrivateBuffer.Buffer.data w
  simp only [PrivateBuffer.Buffer.map] at cd cb wd
  have idmap (x : List B) : (MessageMac.identity s x).map f=MessageMac.identity s' (x.map f) := by
    simp only [MessageMac.identity,List.map_cons,hs.byteConst]
  have dom:=PrivateSend.join_map ha (capacity+66)
    [PrivateSend.literal a (capacity+66) (MessageMac.identity s sender ++ MessageMac.identity s receiver),
     contentBuffer a (PrivateBuffer.fromWire a capacity encodedWire)]
  simp only [List.map_cons,List.map_nil,PrivateSend.literal_map ha,List.map_append,idmap,contentBuffer_map ha,w] at dom
  have mac:=PrivateHash.hmac_map hs ha macKey (capacity+66)
    (PrivateSend.join a (capacity+66)
      [PrivateSend.literal a (capacity+66) (MessageMac.identity s sender ++ MessageMac.identity s receiver),
       contentBuffer a (PrivateBuffer.fromWire a capacity encodedWire)])
  rw [dom] at mac
  have valid:=congrArg PrivateBuffer.Buffer.valid mac
  have data:=congrArg PrivateBuffer.Buffer.data mac
  simp only [PrivateBuffer.Buffer.map] at valid data
  simp only [verify,ha.and,ByteAuth.equalMask_map ha,List.map_take,SliceAt.readCore_map ho ha,
    offset_map ho ha,ho.const,w,c,wd,valid,data]
end Refinement

theorem compiled_verify_correct (capacity : Nat)
    (macKey sender receiver wire : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      [verify Word64.symbolic Sha256.symbolic ByteAuth.symbolic capacity macKey sender receiver wire]
      [verify Word64.concrete Sha256.concrete ByteAuth.concrete capacity
        (macKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))] assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct]
  simp only [List.map_cons,List.map_nil]
  have h := verify_map (Word64.evaluationHom assign) (Sha256.evaluationHom assign)
    (ByteAuth.evaluationHom assign) capacity macKey sender receiver wire
  rw [h]
end TlsMpc.Signal.PrivateMessageMac
