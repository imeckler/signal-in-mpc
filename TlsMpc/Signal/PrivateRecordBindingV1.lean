import TlsMpc.Signal.PrivateRecordSendV1

/-! Internal bounded canonical-record/service binding. Checks are computed on
secret fields, never supplied validity/DH flags. This profile is v4/no-chunk,
NoHeaderReceived, one active PQ link, no skipped keys and nonoverflowing Tahini
counter. Full canonical schema/source refinement and bootstrap remain separate;
this candidate does not admit a provider. -/
namespace TlsMpc.Signal.PrivateRecordBindingV1
open PrivateRecordEncodingV1 PrivateRecordUpdateV1

def all (a : ByteAuth.Ops B) (masks : List B) : B := masks.foldl a.and (a.const 255)
def bytesMask (a : ByteAuth.Ops B) (tag width : Nat) (nodes : List (Node B)) : B :=
 nodes.foldl (fun old node => match node with
  | .bytes t p _ value => if t=tag then all a [ByteAuth.eqMask a p (a.const 255),
      ByteAuth.eqMask a value.valid (a.const 255),ByteAuth.equalMask a value.lengthBits (PrivateBuffer.publicLength a width)] else old
  | _ => old) (a.const 0)
def absentBytesMask (a : ByteAuth.Ops B) (tag : Nat) (nodes : List (Node B)) : B :=
 nodes.foldl (fun old node => match node with
  | .bytes t p _ value => if t=tag then all a [ByteAuth.eqMask a p (a.const 0),
      ByteAuth.eqMask a value.valid (a.const 255),ByteAuth.equalMask a value.lengthBits (PrivateBuffer.publicLength a 0)] else old
  | _ => old) (a.const 0)
def scalarMask (a : ByteAuth.Ops B) (tag : Nat) (nodes : List (Node B)) : B :=
 nodes.foldl (fun old node => match node with
  | .scalar t p _ raw => if t=tag then (if raw.length=4 then ByteAuth.eqMask a p (a.const 255) else a.const 0) else old
  | _ => old) (a.const 0)
def presentMask (a : ByteAuth.Ops B) (tag : Nat) (nodes : List (Node B)) : B :=
 ByteAuth.eqMask a (fieldPresence a tag nodes) (a.const 255)
def publicKeyMask (a : ByteAuth.Ops B) (tag : Nat) (nodes : List (Node B)) : B :=
 a.and (bytesMask a tag 33 nodes) (ByteAuth.eqMask a
  (OpenResult.get a (PrivateRecordSnapshotV1.bytesValue tag nodes) 0) (a.const 5))

def canonicalNodes (a : ByteAuth.Ops B) : Nat → List (Node B) → B
 | 0,_ => a.const 0
 | fuel+1,nodes => all a (nodes.map fun node => match node with
   | .bytes _ p _ value => a.and (PrivateRecordEncodingV1.canonicalMask a p)
       (ByteAuth.eqMask a value.valid (a.const 255))
   | .scalar _ p emitDefault _ => if emitDefault then PrivateRecordEncodingV1.canonicalMask a p else ByteAuth.eqMask a p (a.const 255)
   | .message _ p children => a.and (PrivateRecordEncodingV1.canonicalMask a p) (canonicalNodes a fuel children))

def coherence (s : Sha256.Ops B W) (o : Word64.Ops B V) (a : ByteAuth.Ops B)
    (record : List (Node B)) (service : List B) : B :=
 let current := PrivateRecordSnapshotV1.children 1 record
 let sender := PrivateRecordSnapshotV1.children 6 current
 let key := PrivateRecordSnapshotV1.children 3 sender
 let pq := PrivateRecordSnapshotV1.children 15 current
 let chain := PrivateRecordSnapshotV1.children 2 pq
 let link := PrivateRecordSnapshotV1.children 3 chain
 let send := PrivateRecordSnapshotV1.children 1 link
 let epoch := PrivateRecordSnapshotV1.scalarValue 2 chain
 let epoch := List.replicate (8-epoch.length) (a.const 0) ++ epoch
 let actualEpoch := Word64.bytes o (o.add (o.pack epoch) (o.const 1))
 let equal := ByteAuth.equalMask a
 let body := service.drop 292
 let management := PrivateRecordSnapshotV1.children 3 record
 let action := PrivateRecordUpdateV1.scalarValue a 1 management
 let counter := PrivateRecordUpdateV1.scalarValue a 2 management
 let inactive := equal action [a.const 0,a.const 0,a.const 0,a.const 2]
 let overflow := equal counter (List.replicate 4 (a.const 255))
 let _ := s
 all a [canonicalNodes a 16 record,presentMask a 1 record,presentMask a 6 current,presentMask a 3 sender,
  publicKeyMask a 2 current,publicKeyMask a 3 current,bytesMask a 4 32 current,
  bytesMask a 2 32 sender,publicKeyMask a 1 sender,bytesMask a 2 32 key,
  scalarMask a 1 key,scalarMask a 5 current,scalarMask a 1 current,
  presentMask a 15 current,presentMask a 2 pq,presentMask a 3 chain,presentMask a 1 link,
  bytesMask a 2 32 send,absentBytesMask a 3 send,scalarMask a 1 send,scalarMask a 2 chain,
  absentBytesMask a 1 pq,
  -- First protobuf key0x32 identifies NoHeaderReceived in canonical V1State.
  -- This is profile selection, not validation of arbitrary serialized KEM data.
  presentMask a 3 pq,ByteAuth.eqMask a (OpenResult.get a (PrivateRecordSnapshotV1.bytesValue 3 pq) 0) (a.const 50),
  equal (PrivateRecordSnapshotV1.scalarValue 1 current) [a.const 0,a.const 0,a.const 0,a.const 4],
  ByteAuth.eqMask a (OpenResult.get a body 0) (a.const 4),ByteAuth.eqMask a (OpenResult.get a body 117) (a.const 0),
  equal (PrivateRecordSnapshotV1.scalarValue 1 key) (slice body 1 4),
  equal (PrivateRecordSnapshotV1.scalarValue 5 current) (slice body 5 4),
  equal ((PrivateRecordSnapshotV1.bytesValue 1 sender).drop 1) (slice body 9 32),
  equal (PrivateRecordSnapshotV1.bytesValue 2 key) (slice body 41 32),
  equal (PrivateRecordSnapshotV1.bytesValue 2 send) (slice body 73 32),
  equal (PrivateRecordSnapshotV1.scalarValue 1 send) (slice body 105 4),equal actualEpoch (slice body 109 8),
  equal ((PrivateRecordSnapshotV1.bytesValue 2 current).drop 1) (slice body 118 32),
  equal ((PrivateRecordSnapshotV1.bytesValue 3 current).drop 1) (slice body 150 32),
  a.not (a.and inactive overflow)]

def bind (s : Sha256.Ops B W) (o : Word64.Ops B V) (a : ByteAuth.Ops B)
    (record : List (Node B)) (service producer : List B) : List B × List (Node B) :=
 let old := slice service 333 32 ++ slice service 293 4 ++ slice service 365 32 ++
   slice service 397 4 ++ slice service 594 8
 let accepted := if service.length=611 ∧ producer.length=81 then
   a.and (ByteAuth.eqMask a (OpenResult.get a producer 0) (a.const 255)) (coherence s o a record service)
   else a.const 0
 let boundPrefix := accepted :: PrivateRecordUpdateV1.chooseList a accepted (producer.drop 1) old
 (boundPrefix,PrivateRecordSendV1.applySend s a record boundPrefix)
end TlsMpc.Signal.PrivateRecordBindingV1
