import TlsMpc.Signal.Word64
import TlsMpc.Signal.SpqrDecodeAt
import TlsMpc.Signal.ReadAt
import TlsMpc.Signal.ReceiveSpec

/-! General bounded SignalMessage protobuf parsing. Only the wire capacity is
public. A shared next-field cursor gates a public scan; duplicate fields replace
prior values, unknown fields/groups are skipped with matching end tags and the
pinned default recursion limit100. Valid uint64 scalar varints truncate to u32;
uint64 overflow fails. Bytes fields keep secret offsets/lengths into the same
wire, including empty fields. All malformed input fails closed.

The compiler theorem covers this Lean implementation. Actual whole-Prost and
SignalMessage Rust refinement remains distinct from concrete oracle fixtures. -/
namespace TlsMpc.Signal.ProtoParse
open Std.Tactic.BVDecide
open Word64

structure Decoded (B W : Type) where
  ok : B
  stop : W
  value : W

def Decoded.map (f : B → B') (fw : W → W') (x : Decoded B W) : Decoded B' W' :=
  ⟨f x.ok, fw x.stop, fw x.value⟩

def decodePrefix (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (wire : List B) (start : Nat) : Decoded B W :=
  let tail := wire.drop start
  let decoded := VarintDecode.Spqr.decodeCore d a tail
  let count := OpenResult.get a decoded 1
  let fits := bor a (a.not (ByteAuth.eqMask a count (a.const 10)))
    (ByteAuth.zeroMask a (a.and (OpenResult.get a tail 9) (a.const 254)))
  let good := a.and (OpenResult.get a decoded 0) fits
  ⟨good, o.add (o.const start) (o.pack (List.replicate 7 (a.const 0) ++ [count])), o.pack (decoded.drop 2)⟩

def selectDecoded (o : Word64.Ops B W) (a : ByteAuth.Ops B) (mask : B)
    (yes no : Decoded B W) : Decoded B W :=
  ⟨Unpad.chooseByte a mask yes.ok no.ok, o.select mask yes.stop no.stop, o.select mask yes.value no.value⟩

def lookupDecoded (o : Word64.Ops B W) (a : ByteAuth.Ops B) (index : W) :
    Nat → List (Decoded B W) → Decoded B W
  | _, [] => ⟨a.const 0, index, o.const 0⟩
  | i, row :: rest => selectDecoded o a (Word64.eq o a index (o.const i)) row (lookupDecoded o a index (i + 1) rest)

def table (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) :
    List (Decoded B W) := (List.range wire.length).map (decodePrefix d o a wire)

structure Field (B W : Type) where
  present : B
  offset : W
  length : W
  scalar : W

def Field.map (f : B → B') (fw : W → W') (x : Field B W) : Field B' W' :=
  ⟨f x.present, fw x.offset, fw x.length, fw x.scalar⟩

def emptyField (o : Word64.Ops B W) (a : ByteAuth.Ops B) : Field B W :=
  ⟨a.const 0, o.const 0, o.const 0, o.const 0⟩

def selectField (o : Word64.Ops B W) (a : ByteAuth.Ops B) (mask : B)
    (yes no : Field B W) : Field B W :=
  ⟨Unpad.chooseByte a mask yes.present no.present, o.select mask yes.offset no.offset,
    o.select mask yes.length no.length, o.select mask yes.scalar no.scalar⟩

structure State (B W : Type) where
  ok : B
  next : W
  depth : W
  stack : List W
  fields : List (Field B W)

def State.map (f : B → B') (fw : W → W') (x : State B W) : State B' W' :=
  ⟨f x.ok, fw x.next, fw x.depth, x.stack.map fw, x.fields.map (Field.map f fw)⟩

def initial (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat) : State B W :=
  ⟨a.const 255, o.const 0, o.const 0, List.replicate (min 100 capacity) (o.const 0),
    List.replicate 6 (emptyField o a)⟩

def lookupWord (o : Word64.Ops B W) (a : ByteAuth.Ops B) (index : W) : Nat → List W → W
  | _, [] => o.const 0
  | i, x :: xs => o.select (Word64.eq o a index (o.const i)) x (lookupWord o a index (i + 1) xs)

def writeStack (o : Word64.Ops B W) (a : ByteAuth.Ops B) (enabled : B) (index tag : W) (stack : List W) : List W :=
  stack.zipIdx.map (fun (old, i) => o.select (a.and enabled (Word64.eq o a index (o.const i))) tag old)

def writeFields (o : Word64.Ops B W) (a : ByteAuth.Ops B) (enabled : B) (tag : W)
    (decoded : Decoded B W) (fields : List (Field B W)) : List (Field B W) :=
  fields.zipIdx.map (fun (old, i) => selectField o a
    (a.and enabled (Word64.eq o a tag (o.const (i + 1))))
    ⟨a.const 255, decoded.stop, decoded.value, decoded.value⟩ old)

/-- Prost obtains a mutable Option field before attempting its decoder. Missing
fields therefore become present with their type's zero/empty default on errors. -/
def initializeFields (o : Word64.Ops B W) (a : ByteAuth.Ops B) (enabled : B)
    (tag : W) (fields : List (Field B W)) : List (Field B W) :=
  fields.zipIdx.map (fun (old, i) => selectField o a
    (a.and enabled (Word64.eq o a tag (o.const (i + 1))))
    (selectField o a old.present old ⟨a.const 255,o.const 0,o.const 0,o.const 0⟩) old)

structure Plan (B W : Type) where
  ok : B
  stop : W
  tag : W
  kind : W
  payload : Decoded B W

def Plan.map (f : B → B') (fw : W → W') (p : Plan B W) : Plan B' W' :=
  ⟨f p.ok, fw p.stop, fw p.tag, fw p.kind, p.payload.map f fw⟩

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

/-- Preserve the accepted prefix/table representation and separately calculate
actual failure consumption. The final table row reports whether the last byte
has its continuation bit clear, exactly the shared contiguous fast-path guard. -/
def planWithCursor (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity position : Nat)
    (lastClear : B) (key payload : Decoded B W) (state : State B W) : Plan B W :=
  let p := plan o a capacity key payload state
  let keyGood := a.and key.ok (a.and (o.ule key.value (o.const 4294967295))
    (a.and (a.not (Word64.eq o a p.tag (o.const 0))) (o.ule p.kind (o.const 5))))
  let known := a.and (Word64.eq o a state.depth (o.const 0)) (o.ule p.tag (o.const 6))
  let scalar := bor a (Word64.eq o a p.tag (o.const 2)) (Word64.eq o a p.tag (o.const 3))
  let expected := Unpad.chooseByte a scalar (Word64.eq o a p.kind (o.const 0)) (Word64.eq o a p.kind (o.const 2))
  let validKnown := bor a (a.not known) expected
  let attemptsPayload := a.and keyGood (a.and validKnown (a.and (o.ule state.depth (o.const 99))
    (bor a (Word64.eq o a p.kind (o.const 0)) (Word64.eq o a p.kind (o.const 2)))))
  let keyFast := if capacity > position + 10 then a.const 255 else lastClear
  let payloadFast := bor a (o.ule (o.add key.stop (o.const 11)) (o.const capacity)) lastClear
  let slowKeyStop := o.const (position + min 10 (capacity-position))
  let slowPayloadStop := o.select (o.ule (o.add key.stop (o.const 10)) (o.const capacity))
    (o.add key.stop (o.const 10)) (o.const capacity)
  let keyFailure := o.select key.ok key.stop (o.select keyFast (o.const position) slowKeyStop)
  let payloadFailure := o.select payload.ok payload.stop (o.select payloadFast key.stop slowPayloadStop)
  let failureStop := o.select attemptsPayload payloadFailure keyFailure
  { p with stop := o.select p.ok p.stop failureStop, tag := o.select keyGood p.tag (o.const 0) }

def applyPlan (o : Word64.Ops B W) (a : ByteAuth.Ops B) (position : Nat)
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
    writeStack o a (a.and enabled start) state.depth p.tag state.stack,
    writeFields o a (a.and enabled top) p.tag p.payload
      (initializeFields o a (a.and active top) p.tag state.fields)⟩

def step (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat) (decoders : List (Decoded B W))
    (state : State B W) (position : Nat) : State B W :=
  let key := decoders[position]?.getD ⟨a.const 0, o.const position, o.const 0⟩
  let payload := lookupDecoded o a key.stop (position + 1) ((decoders.drop (position + 1)).take 10)
  let lastClear := (decoders[capacity - 1]?.getD ⟨a.const 0,o.const (capacity - 1),o.const 0⟩).ok
  applyPlan o a position (planWithCursor o a capacity position lastClear key payload state) state

def parseBody (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (body : List B) : State B W :=
  (List.range body.length).foldl (step o a body.length (table d o a body)) (initial o a body.length)

def completeMask (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat) (state : State B W) : B :=
  a.and state.ok (a.and (Word64.eq o a state.next (o.const capacity)) (Word64.eq o a state.depth (o.const 0)))

def getField (o : Word64.Ops B W) (a : ByteAuth.Ops B) (state : State B W) (index : Nat) : Field B W :=
  state.fields[index]?.getD (emptyField o a)

def body (wire : List B) : List B := (MessageMac.content wire).drop 1

def ratchetRead (o : Word64.Ops B W) (a : ByteAuth.Ops B) (body : List B) (state : State B W) : List B :=
  ReadAt.readCore a 33 body (Word64.bytes o (getField o a state 0).offset)

def acceptedMask (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) (state : State B W) : B :=
  let ratchet := getField o a state 0
  a.and (if wire.length ≥ 9 then a.const 255 else a.const 0)
    (a.and (Receive.versionMask a wire)
      (a.and (completeMask o a (body wire).length state)
        (a.and ratchet.present (a.and (getField o a state 1).present
          (a.and (getField o a state 3).present
            (a.and (o.ule (o.const 33) ratchet.length)
              (ByteAuth.eqMask a (OpenResult.get a (ratchetRead o a (body wire) state) 9) (a.const 5))))))))

def metadata (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) (state : State B W) : List B :=
  (ratchetRead o a (body wire) state).drop 10 ++
    (Word64.bytes o (getField o a state 1).scalar).drop 4 ++
    (Word64.bytes o (getField o a state 2).scalar).drop 4 ++
    Word64.bytes o (getField o a state 3).offset ++ Word64.bytes o (getField o a state 3).length ++
    Word64.bytes o (getField o a state 4).offset ++ Word64.bytes o (getField o a state 4).length ++
    [a.and (getField o a state 5).present (a.const 1)] ++
    Word64.bytes o (getField o a state 5).offset ++ Word64.bytes o (getField o a state 5).length

def parseCore (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : List B :=
  let state := parseBody d o a (body wire)
  let accepted := acceptedMask o a wire state
  accepted :: ByteAuth.release a accepted (metadata o a wire state)

def parseChecked (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : Option (List B) :=
  if wire.length ≤ 512 then some (parseCore d o a wire) else none

end TlsMpc.Signal.ProtoParse
