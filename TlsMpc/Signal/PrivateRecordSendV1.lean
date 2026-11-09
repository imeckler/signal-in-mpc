import TlsMpc.Signal.PrivateRecordSnapshotV1
namespace TlsMpc.Signal.PrivateRecordSendV1
open PrivateRecordEncodingV1 PrivateRecordUpdateV1

/-! Selected established no-chunk sender update. Input prefix is the real
VariableConversation output: status::CK32::counter4::PQnext32::PQcounter4::nextID8.
Full SPQR phase/epoch transitions and semantic schema validation remain required.
The snapshot remains canonical state; no stale protobuf baseline is retained. -/
def applySend (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (record : List (Node B)) (result : List B) : List (Node B) :=
 if 81≤result.length then
  let accepted := ByteAuth.eqMask a (OpenResult.get a result 0) (a.const 255)
  let record := nested 1 (fun current =>
    let current := nested 6 (nested 3
      (putScalar a accepted 1 (slice result 33 4) ∘ putBytes a accepted 2 (slice result 1 32))) current
    nested 15 (nested 2 (nested 3 (nested 1
      (putScalar a accepted 1 (slice result 69 4) ∘ putBytes a accepted 2 (slice result 37 32))))) current) record
  let management := PrivateRecordSnapshotV1.children 3 record
  let oldAct := PrivateRecordUpdateV1.scalarValue a 1 management
  let inactive := ByteAuth.equalMask a oldAct [a.const 0,a.const 0,a.const 0,a.const 2]
  let oldCounter := PrivateRecordUpdateV1.scalarValue a 2 management
  let nextCounter := s.add (Varint.pack s a oldCounter) (s.wordConst 1)
  let nextBytes := [s.unpack nextCounter 0,s.unpack nextCounter 1,s.unpack nextCounter 2,s.unpack nextCounter 3]
  let record := presence a accepted (a.const 255) 3 record
  nested 3 (putScalar a accepted 1 (List.replicate 4 (a.const 0)) ∘
    putScalar a (a.and accepted inactive) 2 nextBytes) record
 else record
end TlsMpc.Signal.PrivateRecordSendV1
