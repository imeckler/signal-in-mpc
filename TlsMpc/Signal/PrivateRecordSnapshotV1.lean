import TlsMpc.Signal.PrivateRecordUpdateV1
import TlsMpc.Signal.Word64

/-! Fixed-schema share snapshot codec. It stores every private presence/length/
value in the canonical tree, so restart need not parse live protobuf on the host.
Schema tree/capacities are PUBLIC and must be authenticated by the archive domain.
No helper below grants provider admission. -/
namespace TlsMpc.Signal.PrivateRecordSnapshotV1
open PrivateRecordEncodingV1

def flatten (a : ByteAuth.Ops B) : Nat → List (Node B) → List B
 | 0,_ => []
 | fuel+1,nodes => nodes.flatMap fun node => match node with
   | .bytes _ present _ value => present :: PrivateBuffer.output a value
   | .scalar _ present _ be => present :: be
   | .message _ present children => present :: flatten a fuel children

def restore (a : ByteAuth.Ops B) : Nat → List (Node B) → List B → List (Node B) × List B
 | 0,_,raw => ([],raw)
 | fuel+1,nodes,raw =>
  nodes.foldl (fun (acc : List (Node B) × List B) node =>
   let p := OpenResult.get a acc.2 0
   let tail := acc.2.drop 1
   let restored := match node with
    | .bytes tag _ empty value =>
      let n := value.data.length
      (Node.bytes tag p empty (PrivateBuffer.fromWire a n (tail.take (3+n))),tail.drop (3+n))
    | .scalar tag _ defaults be => (Node.scalar tag p defaults (tail.take be.length),tail.drop be.length)
    | .message tag _ children =>
      let child := restore a fuel children tail
      (Node.message tag p child.1,child.2)
   (acc.1++[restored.1],restored.2)) ([],raw)

def children (tag : Nat) (nodes : List (Node B)) : List (Node B) :=
 nodes.foldl (fun old node => match node with | .message t _ ns => if tag=t then ns else old | _ => old) []
def bytesValue (tag : Nat) (nodes : List (Node B)) : List B :=
 nodes.foldl (fun old node => match node with | .bytes t _ _ b => if tag=t then b.data else old | _ => old) []
def scalarValue (tag : Nat) (nodes : List (Node B)) : List B :=
 nodes.foldl (fun old node => match node with | .scalar t _ _ raw => if tag=t then raw else old | _ => old) []

def project (o : Word64.Ops B V) (a : ByteAuth.Ops B) (record : List (Node B)) : List B :=
 let current := children 1 record
 let sender := children 6 current
 let sendKey := children 3 sender
 let root := bytesValue 4 current
 let ownPrivate := bytesValue 2 sender
 let ownPublic := (bytesValue 1 sender).drop 1
 let senderBytes := root ++ ownPrivate ++ ownPublic ++ bytesValue 2 sendKey ++ scalarValue 1 sendKey ++ scalarValue 5 current
 let recv := current.flatMap fun node => match node with
  | .message 7 present ns =>
    let key := children 3 ns
    present :: ByteAuth.release a present ((bytesValue 1 ns).drop 1 ++ bytesValue 2 key ++ scalarValue 1 key)
  | _ => []
 let pq := children 15 current
 let chain := children 2 pq
 let epoch := scalarValue 2 chain
 let epoch := List.replicate (8-epoch.length) (a.const 0) ++ epoch
 let link := children 3 chain
 let recvKey := children 2 link
 senderBytes ++ recv ++ Word64.bytes o (o.add (o.pack epoch) (o.const 1)) ++ bytesValue 2 recvKey ++ scalarValue 1 recvKey
end TlsMpc.Signal.PrivateRecordSnapshotV1
