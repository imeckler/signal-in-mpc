import TlsMpc.Signal.PrivateRecordEncodingV1

/-! Private bounded active-session receive update of a fixed-capacity record tree.
Requires a complete canonical schema with exactly one slot for each named field,
five receiver slots, one PQ epoch link, and no skipped keys. Schema/admission
validation and a source theorem remain open; this module must not admit state. -/
namespace TlsMpc.Signal.PrivateRecordUpdateV1
open PrivateRecordEncodingV1

def chooseList (a : ByteAuth.Ops B) (mask : B) (yes no : List B) : List B :=
 List.zipWith (PrivateBuffer.choose a mask) yes no

def alter (tag : Nat) (f : Node B → Node B) (nodes : List (Node B)) : List (Node B) :=
 nodes.map fun node => match node with
 | .bytes t _ _ _ | .scalar t _ _ _ | .message t _ _ => if tag=t then f node else node

def nested (tag : Nat) (f : List (Node B) → List (Node B)) (nodes : List (Node B)) : List (Node B) :=
 alter tag (fun node => match node with | .message t p children => .message t p (f children) | other => other) nodes

def putBytes (a : ByteAuth.Ops B) (mask : B) (tag : Nat) (raw : List B) (nodes : List (Node B)) : List (Node B) :=
 alter tag (fun node => match node with
 | .bytes t p empty value => .bytes t p empty (selectBuffer a mask
      (PrivateBuffer.fromPublic a value.data.length raw) value)
 | other => other) nodes

def putScalar (a : ByteAuth.Ops B) (mask : B) (tag : Nat) (raw : List B) (nodes : List (Node B)) : List (Node B) :=
 alter tag (fun node => match node with
 | .scalar t p defaults old => .scalar t p defaults (chooseList a mask raw old)
 | other => other) nodes

def presence (a : ByteAuth.Ops B) (mask : B) (value : B) (tag : Nat) (nodes : List (Node B)) : List (Node B) :=
 alter tag (fun node => match node with
 | .bytes t p e b => .bytes t (PrivateBuffer.choose a mask value p) e b
 | .scalar t p e b => .scalar t (PrivateBuffer.choose a mask value p) e b
 | .message t p b => .message t (PrivateBuffer.choose a mask value p) b) nodes

def scalarValue (a : ByteAuth.Ops B) (tag : Nat) (nodes : List (Node B)) : List B :=
 (nodes.foldl (fun old node => match node with | .scalar t _ _ raw => if t=tag then raw else old | _ => old)
   (List.replicate 4 (a.const 0)))

def slice (xs : List B) (start size : Nat) : List B := (xs.drop start).take size

def receiver (a : ByteAuth.Ops B) (mask : B) (slot : List B) (node : Node B) : Node B :=
 match node with
 | .message tag p children =>
  let children := presence a mask (a.const 255) 1 (putBytes a mask 1 (a.const 5::slice slot 1 32) children)
  let children := presence a mask (a.const 255) 3 (nested 3 (presence a mask (a.const 255) 2 ∘ putScalar a mask 1 (slice slot 65 4) ∘ putBytes a mask 2 (slice slot 33 32)) children)
  .message tag (PrivateBuffer.choose a mask (OpenResult.get a slot 0) p) children
 | other => other

def receivers (a : ByteAuth.Ops B) (mask : B) (state : List B) (nodes : List (Node B)) : List (Node B) :=
 (nodes.foldl (fun (acc : Nat × List (Node B)) node => match node with
   | .message 7 _ _ => (acc.1+1,acc.2++[receiver a mask (slice state (136+69*acc.1) 69) node])
   | _ => (acc.1,acc.2++[node])) (0,[])).2

def current (a : ByteAuth.Ops B) (mask : B) (state : List B) (nodes : List (Node B)) : List (Node B) :=
 let oldOrigin := scalarValue a 16 nodes
 let legacy := ByteAuth.equalMask a oldOrigin (List.replicate 4 (a.const 0))
 let localNew := ByteAuth.equalMask a oldOrigin [a.const 0,a.const 0,a.const 0,a.const 1]
 let clear := a.and mask (a.xor legacy localNew)
 let nodes := presence a clear (a.const 0) 14 (presence a clear (a.const 0) 9 nodes)
 let nodes := putScalar a (a.and mask localNew) 16 [a.const 0,a.const 0,a.const 0,a.const 2] nodes
 let nodes := putBytes a mask 4 (slice state 0 32) nodes
 let nodes := putScalar a mask 5 (slice state 132 4) nodes
 let nodes := nested 6 (fun chain =>
   let chain := putBytes a mask 1 (a.const 5::slice state 64 32) chain
   let chain := putBytes a mask 2 (slice state 32 32) chain
   nested 3 (putScalar a mask 1 (slice state 128 4) ∘ putBytes a mask 2 (slice state 96 32)) chain) nodes
 let nodes := receivers a mask state nodes
 -- PQ epoch, phase, direction, send chain, auth/KEM and all other fields are
 -- retained. This profile updates only the sole active recv next/ctr.
 nested 15 (nested 2 (nested 3 (nested 2
   (putScalar a mask 1 (slice state 521 4) ∘ putBytes a mask 2 (slice state 489 32))))) nodes

def applyReceive (a : ByteAuth.Ops B) (record : List (Node B)) (result : List B) : List (Node B) :=
 if result.length=608 then
  let accepted := ByteAuth.eqMask a (OpenResult.get a result 0) (a.const 255)
  let record := nested 1 (current a accepted (slice result 1 525)) record
  let record := presence a accepted (a.const 255) 3 record
  nested 3 (putScalar a accepted 1 [a.const 0,a.const 0,a.const 0,a.const 1]) record
 else record
end TlsMpc.Signal.PrivateRecordUpdateV1
