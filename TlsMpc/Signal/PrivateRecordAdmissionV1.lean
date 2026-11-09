import TlsMpc.Signal.PrivateRecordBindingV1
import TlsMpc.Signal.PrivateRecordSchemaV1
/-! Bounded restored canonical-record coherence guard. Its validity is computed
from shared bytes, never supplied. It does not validate full accounts, previous
certificate chains, arbitrary SPQR state or fresh-session bootstrap. -/
namespace TlsMpc.Signal.PrivateRecordAdmissionV1

def validate (s : Sha256.Ops B W) (o : Word64.Ops B V) (a : ByteAuth.Ops B)
    (raw : List B) : List B :=
 let snapshot := raw.take 5550
 let selected := (raw.drop 5550).take 525
 let service := raw.drop 6075
 let record := (PrivateRecordSnapshotV1.restore a 16 (PrivateRecordSchemaV1.schema a) snapshot).1
 [if raw.length=6686 then PrivateRecordBindingV1.all a [
   PrivateRecordBindingV1.coherence s o a record service,
   ByteAuth.equalMask a (PrivateRecordSnapshotV1.project o a record) selected,
   ByteAuth.equalMask a (PrivateRecordSnapshotV1.flatten a 16 record) snapshot]
  else a.const 0]
end TlsMpc.Signal.PrivateRecordAdmissionV1
