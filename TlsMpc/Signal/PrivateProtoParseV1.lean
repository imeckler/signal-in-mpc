import TlsMpc.Signal.ProtoParseProofs

/-! Versioned private-length SignalMessage parser. All list lengths and scans
are public capacities; the actual wire/body end is a shared word. Bytes beyond
the secret body end are replaced by continuation-only 0x80, so padding cannot
terminate a truncated varint. Every fixed/bytes bound and failure cursor uses
the same private end. This module does not verify the MAC. -/
namespace TlsMpc.Signal.PrivateProtoParseV1
open ProtoParse Word64

/-- Preserve the capacity while making every byte beyond the private end an
inert continuation byte. Masking with zero would incorrectly complete varints. -/
def boundedBytes (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W)
    (bytes : List B) : List B :=
  bytes.zipIdx.map (fun (byte,index) =>
    Unpad.chooseByte a (o.ule (o.const (index+1)) ending) byte (a.const 128))

def table (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (ending : W) (bytes : List B) : List (Decoded B W) :=
  ProtoParse.table d o a (boundedBytes o a ending bytes)

def plan (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W)
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
      (bor a (a.and (isKind 1) (o.ule (o.add key.stop (o.const 8)) (ending)))
        (bor a (a.and (isKind 2) (a.and payload.ok (o.ule payload.value (o.sub (ending) payload.stop))))
          (bor a (isKind 3) (a.and (isKind 5) (o.ule (o.add key.stop (o.const 4)) (ending))))))))
    (a.and (isKind 4) endGroup)
  let good := a.and key.ok (a.and (o.ule key.value (o.const 4294967295))
    (a.and (a.not (Word64.eq o a tag (o.const 0))) (a.and validKnown validPayload)))
  let stop := o.select (isKind 0) payload.stop
    (o.select (isKind 1) (o.add key.stop (o.const 8))
      (o.select (isKind 2) (o.add payload.stop payload.value)
        (o.select (isKind 5) (o.add key.stop (o.const 4)) key.stop)))
  ⟨good, stop, tag, kind, payload⟩


def planWithCursor (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W) (position : Nat)
    (lastClear : B) (key payload : Decoded B W) (state : State B W) : Plan B W :=
  let p := plan o a ending key payload state
  let keyGood := a.and key.ok (a.and (o.ule key.value (o.const 4294967295))
    (a.and (a.not (Word64.eq o a p.tag (o.const 0))) (o.ule p.kind (o.const 5))))
  let known := a.and (Word64.eq o a state.depth (o.const 0)) (o.ule p.tag (o.const 6))
  let scalar := bor a (Word64.eq o a p.tag (o.const 2)) (Word64.eq o a p.tag (o.const 3))
  let expected := Unpad.chooseByte a scalar (Word64.eq o a p.kind (o.const 0)) (Word64.eq o a p.kind (o.const 2))
  let validKnown := bor a (a.not known) expected
  let attemptsPayload := a.and keyGood (a.and validKnown (a.and (o.ule state.depth (o.const 99))
    (bor a (Word64.eq o a p.kind (o.const 0)) (Word64.eq o a p.kind (o.const 2)))))
  let keyFast := bor a (o.ule (o.const (position + 11)) ending) lastClear
  let payloadFast := bor a (o.ule (o.add key.stop (o.const 11)) (ending)) lastClear
  let slowKeyStop := o.select (o.ule (o.const (position + 10)) ending) (o.const (position + 10)) ending
  let slowPayloadStop := o.select (o.ule (o.add key.stop (o.const 10)) (ending))
    (o.add key.stop (o.const 10)) (ending)
  let keyFailure := o.select key.ok key.stop (o.select keyFast (o.const position) slowKeyStop)
  let payloadFailure := o.select payload.ok payload.stop (o.select payloadFast key.stop slowPayloadStop)
  let failureStop := o.select attemptsPayload payloadFailure keyFailure
  { p with stop := o.select p.ok p.stop failureStop, tag := o.select keyGood p.tag (o.const 0) }


/-- Cells beyond the private initial stack length are unaddressable in the
accepted take-prefix parser. Prevent writes into that public-capacity tail,
which remains zero and is related explicitly by zero extension in the proof. -/
def applyPlan (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W) (position : Nat)
    (p : Plan B W) (state : State B W) : State B W :=
  let here := Word64.eq o a state.next (o.const position)
  let active := a.and state.ok here
  let enabled := a.and active p.ok
  let start := Word64.eq o a p.kind (o.const 3)
  let stop := Word64.eq o a p.kind (o.const 4)
  let top := Word64.eq o a state.depth (o.const 0)
  ⟨a.and state.ok (a.not (a.and here (a.not p.ok))),
    o.select active p.stop state.next,
    o.select enabled (o.select start (o.add state.depth (o.const 1))
      (o.select stop (o.sub state.depth (o.const 1)) state.depth)) state.depth,
    writeStack o a (a.and (a.and enabled start) (a.not (o.ule ending state.depth))) state.depth p.tag state.stack,
    writeFields o a (a.and enabled top) p.tag p.payload
      (initializeFields o a (a.and active top) p.tag state.fields)⟩


/-- Select equal-shape parser states. Production steps retain the fixed stack
and six-field shapes established by initial/applyPlan. -/
def selectState (o : Word64.Ops B W) (a : ByteAuth.Ops B) (mask : B)
    (yes no : State B W) : State B W :=
  ⟨Unpad.chooseByte a mask yes.ok no.ok, o.select mask yes.next no.next,
    o.select mask yes.depth no.depth,
    List.zipWith (o.select mask) yes.stack no.stack,
    List.zipWith (selectField o a mask) yes.fields no.fields⟩

def step (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W)
    (rows : List (Decoded B W)) (state : State B W) (position : Nat) : State B W :=
  let key := rows[position]?.getD ⟨a.const 0,o.const position,o.const 0⟩
  let payload := lookupDecoded o a key.stop (position+1) ((rows.drop (position+1)).take 10)
  let last := lookupDecoded o a (o.sub ending (o.const 1)) 0 rows
  let candidate := applyPlan o a ending position (planWithCursor o a ending position last.ok key payload state) state
  selectState o a (o.ule (o.const (position+1)) ending) candidate state

def parseBody (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (ending : W) (bytes : List B) : State B W :=
  (List.range bytes.length).foldl (step o a ending (table d o a ending bytes))
    (initial o a bytes.length)

def completeMask (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W)
    (state : State B W) : B :=
  a.and state.ok (a.and (Word64.eq o a state.next ending) (Word64.eq o a state.depth (o.const 0)))

structure Parsed (B W : Type) where
  state : State B W
  wireLength : W
  bodyLength : W
  valid : B
  metadata : List B

/-- Entire capacity wire is version||protobuf body||MAC8. Offsets in state and
metadata are relative to the body (wire offset = body offset +1). The upstream
mask is checked canonically and never omitted. MAC authentication is external. -/
def parse (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (wire : List B) (lengthHigh lengthLow upstreamValid : B) : Parsed B W :=
  let wireLength := o.pack (List.replicate 6 (a.const 0) ++ [lengthHigh,lengthLow])
  let framing := a.and (o.ule (o.const 9) wireLength) (o.ule wireLength (o.const wire.length))
  let bodyLength := o.select framing (o.sub wireLength (o.const 9)) (o.const 0)
  let bytes := ProtoParse.body wire
  let state := parseBody d o a bodyLength bytes
  let ratchet := getField o a state 0
  let accepted := a.and framing (a.and (ByteAuth.eqMask a upstreamValid (a.const 255))
    (a.and (Receive.versionMask a wire)
      (a.and (completeMask o a bodyLength state)
        (a.and ratchet.present (a.and (getField o a state 1).present
          (a.and (getField o a state 3).present
            (a.and (o.ule (o.const 33) ratchet.length)
              (ByteAuth.eqMask a (OpenResult.get a (ratchetRead o a bytes state) 9) (a.const 5)))))))))
  ⟨state,wireLength,bodyLength,accepted,ByteAuth.release a accepted (ProtoParse.metadata o a wire state)⟩

def parseCore (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (wire : List B) (lengthHigh lengthLow upstreamValid : B) : List B :=
  let parsed := parse d o a wire lengthHigh lengthLow upstreamValid
  parsed.valid :: parsed.metadata

end TlsMpc.Signal.PrivateProtoParseV1
