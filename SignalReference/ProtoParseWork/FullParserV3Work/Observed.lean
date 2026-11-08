import TlsMpc.Signal.ProtoParseProofs
open TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed

/-- Private refinement metadata. Codes: 0 success, 1 InvalidVarint, 2 InvalidKey,
3 InvalidWireType, 4 InvalidTag, 5 UnexpectedWireType, 6 BufferUnderflow,
7 RecursionLimitReached, 8 UnexpectedEndGroupTag. Unexpected wire parameters
encode actual + 8*expected; InvalidKey retains the complete uint64 argument. -/
structure ErrorMeta (W : Type) where
  code : W
  parameter : W

def ErrorMeta.map (f : W → W') (x : ErrorMeta W) : ErrorMeta W' := ⟨f x.code,f x.parameter⟩

structure State (B W : Type) where
  parser : ProtoParse.State B W
  error : ErrorMeta W

def State.map (f : B → B') (fw : W → W') (x : State B W) : State B' W' :=
  ⟨x.parser.map f fw,x.error.map fw⟩

/-- Classification follows pinned decode_key then generated merge_field error
precedence. It is consumed only when the active numeric plan rejects. -/
def classify (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (key payload : ProtoParse.Decoded B W) (state : ProtoParse.State B W) : ErrorMeta W :=
  let tag := o.shift key.value 3
  let kind := o.band key.value (o.const 7)
  let isKind := fun k => Word64.eq o a kind (o.const k)
  let top := Word64.eq o a state.depth (o.const 0)
  let known := a.and top (o.ule tag (o.const 6))
  let scalar := Word64.bor a (Word64.eq o a tag (o.const 2)) (Word64.eq o a tag (o.const 3))
  let expected := Unpad.chooseByte a scalar (isKind 0) (isKind 2)
  let wrong := a.and known (a.not expected)
  let payloadCode := o.select payload.ok (o.const 6) (o.const 1)
  let leafCode := o.select (Word64.bor a (isKind 0) (isKind 2)) payloadCode (o.const 6)
  let skipCode := o.select (isKind 4) (o.const 8)
    (o.select (o.ule state.depth (o.const 99)) leafCode (o.const 7))
  let fieldCode := o.select wrong (o.const 5) skipCode
  let zeroTag := Word64.eq o a tag (o.const 0)
  let validKind := o.ule kind (o.const 5)
  let validRange := o.ule key.value (o.const 4294967295)
  let code := o.select key.ok
    (o.select validRange (o.select validKind (o.select zeroTag (o.const 4) fieldCode) (o.const 3)) (o.const 2))
    (o.const 1)
  let wirePair := o.add kind (o.select scalar (o.const 0) (o.const 16))
  let parameter := o.select key.ok
    (o.select validRange (o.select validKind
      (o.select zeroTag (o.const 0) (o.select wrong wirePair (o.const 0))) kind) key.value)
    (o.const 0)
  ⟨code,parameter⟩

def step (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat)
    (rows : List (ProtoParse.Decoded B W)) (state : State B W) (position : Nat) : State B W :=
  let key := rows[position]?.getD ⟨a.const 0,o.const position,o.const 0⟩
  let payload := ProtoParse.lookupDecoded o a key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[capacity-1]?.getD ⟨a.const 0,o.const (capacity-1),o.const 0⟩).ok
  let p := ProtoParse.planWithCursor o a capacity position lastClear key payload state.parser
  let failed := a.and state.parser.ok (a.and (Word64.eq o a state.parser.next (o.const position)) (a.not p.ok))
  let error := classify o a key payload state.parser
  ⟨ProtoParse.step o a capacity rows state.parser position,
    ⟨o.select failed error.code state.error.code,o.select failed error.parameter state.error.parameter⟩⟩

def finish (o : Word64.Ops B W) (a : ByteAuth.Ops B) (state : State B W) : State B W :=
  let unclosed := a.and state.parser.ok (a.not (Word64.eq o a state.parser.depth (o.const 0)))
  ⟨state.parser,⟨o.select unclosed (o.const 1) state.error.code,o.select unclosed (o.const 0) state.error.parameter⟩⟩

def parse (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (body : List B) : State B W :=
  finish o a ((List.range body.length).foldl (step o a body.length (ProtoParse.table d o a body))
    ⟨ProtoParse.initial o a body.length,⟨o.const 0,o.const 0⟩⟩)

/-- Erasing proof-only diagnostics gives the existing numeric parser exactly.
Production parseCore continues to use that original parser and incurs no cost. -/
theorem erase_parse (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (body : List B) : (parse d o a body).parser = ProtoParse.parseBody d o a body := by
  have h (positions : List Nat) (state : State B W) :
      (positions.foldl (step o a body.length (ProtoParse.table d o a body)) state).parser =
        positions.foldl (ProtoParse.step o a body.length (ProtoParse.table d o a body)) state.parser := by
    induction positions generalizing state with
    | nil => rfl
    | cons p rest ih => exact ih _
  exact h _ _

/-- External compiler output remains the established masked 90-byte result,
including all-zero rejection; error metadata is private proof instrumentation. -/
theorem erase_external (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (wire : List B) :
    (let state := (parse d o a (ProtoParse.body wire)).parser
     let accepted := ProtoParse.acceptedMask o a wire state
     accepted :: ByteAuth.release a accepted (ProtoParse.metadata o a wire state)) =
      ProtoParse.parseCore d o a wire := by rw [erase_parse]; rfl

#print axioms erase_parse
#print axioms erase_external
end FullParserV3.Observed
