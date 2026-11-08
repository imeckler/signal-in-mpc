import TlsMpc.Signal.ProtoParse
namespace TlsMpc.Signal.ProtoParse.HistoricalV1
open TlsMpc.Signal.ProtoParse TlsMpc.Signal.Word64
def decodePrefix (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (wire : List B) (start : Nat) : Decoded B W :=
  let tail := wire.drop start
  let decoded := VarintDecode.Spqr.decodeCore d a tail
  let count := OpenResult.get a decoded 1
  let fits := bor a (a.not (ByteAuth.eqMask a count (a.const 10)))
    (ByteAuth.zeroMask a (a.and (OpenResult.get a tail 9) (a.const 254)))
  let good := a.and (OpenResult.get a decoded 0) fits
  ⟨good, o.add (o.const start) (o.pack (List.replicate 7 (a.const 0) ++ [count])), o.pack (decoded.drop 2)⟩

def table (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) :
    List (Decoded B W) := (List.range wire.length).map (decodePrefix d o a wire)

def plan (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat)
    (key payload : Decoded B W) (state : State B W) : Plan B W :=
  let tag := o.shift key.value 3
  let kind := o.band key.value (o.const 7)
  let isKind := fun k => Word64.eq o a kind (o.const k)
  let top := Word64.eq o a state.depth (o.const 0)
  let known := a.and top (o.ule tag (o.const 6))
  let scalar := bor a (Word64.eq o a tag (o.const 2)) (Word64.eq o a tag (o.const 3))
  let expectedKind := Unpad.chooseByte a scalar (isKind 0) (isKind 2)
  let validKnown := bor a (a.not known) expectedKind
  let belowLimit := o.ule state.depth (o.const 99)
  let endGroup := a.and (a.not top)
    (Word64.eq o a tag (lookupWord o a (o.sub state.depth (o.const 1)) 0 state.stack))
  let validPayload := bor a
    (a.and belowLimit (bor a
      (a.and (isKind 0) payload.ok)
      (bor a (a.and (isKind 1) (o.ule (o.add key.stop (o.const 8)) (o.const capacity)))
        (bor a (a.and (isKind 2) (a.and payload.ok (o.ule payload.value (o.sub (o.const capacity) payload.stop))))
          (bor a (isKind 3) (a.and (isKind 5) (o.ule (o.add key.stop (o.const 4)) (o.const capacity))))))))
    (a.and (isKind 4) endGroup)
  let good := a.and key.ok (a.and (o.ule key.value (o.const 4294967295))
    (a.and (a.not (Word64.eq o a tag (o.const 0))) (a.and validKnown validPayload)))
  let stop := o.select (isKind 0) payload.stop
    (o.select (isKind 1) (o.add key.stop (o.const 8))
      (o.select (isKind 2) (o.add payload.stop payload.value)
        (o.select (isKind 5) (o.add key.stop (o.const 4)) key.stop)))
  ⟨good, stop, tag, kind, payload⟩

def applyPlan (o : Word64.Ops B W) (a : ByteAuth.Ops B) (position : Nat)
    (p : Plan B W) (state : State B W) : State B W :=
  let here := Word64.eq o a state.next (o.const position)
  let enabled := a.and state.ok (a.and here p.ok)
  let start := Word64.eq o a p.kind (o.const 3)
  let stop := Word64.eq o a p.kind (o.const 4)
  let top := Word64.eq o a state.depth (o.const 0)
  ⟨a.and state.ok (a.not (a.and here (a.not p.ok))),
    o.select enabled p.stop state.next,
    o.select enabled (o.select start (o.add state.depth (o.const 1))
      (o.select stop (o.sub state.depth (o.const 1)) state.depth)) state.depth,
    writeStack o a (a.and enabled start) state.depth p.tag state.stack,
    writeFields o a (a.and enabled top) p.tag p.payload state.fields⟩

def step (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat) (decoders : List (Decoded B W))
    (state : State B W) (position : Nat) : State B W :=
  let key := decoders[position]?.getD ⟨a.const 0, o.const position, o.const 0⟩
  let payload := lookupDecoded o a key.stop (position + 1) ((decoders.drop (position + 1)).take 10)
  applyPlan o a position (plan o a capacity key payload state) state

def parseBody (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (body : List B) : State B W :=
  (List.range body.length).foldl (step o a body.length (table d o a body)) (initial o a body.length)


end TlsMpc.Signal.ProtoParse.HistoricalV1
