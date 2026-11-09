import ChatResponseReferenceWork.ParserCircuitCandidateV1.Stack32Codec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1.AdmissionExport
/-- Minimal computational import boundary for resource-limited export. The
separate kernel bridge proves exact equality with the already-proved endpoint. -/
def sourceIndex (index : Nat) : Option Nat :=
  if index < 73 then some index
  else if index < 873 then
    if (index-73)%8 < 4 then none
    else some (73+4*((index-73)/8)+((index-73)%8-4))
  else some (index-400)

def expand (a : ByteAuth.Ops B) (compact : List B) : List B :=
  (List.range 992).map (fun i => match sourceIndex i with
    | none => a.const 0
    | some source => TlsWebSocketUpgrade.get a compact source)

def run (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  (compactOutput a (TlsChatResponseMux.runAdmit o a (expand a raw))).take 582
end ChatResponseReference.ParserCircuitCandidateV1.AdmissionExport
