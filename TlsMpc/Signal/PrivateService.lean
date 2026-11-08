import TlsMpc.Signal.PrivateSpqrSend
import TlsMpc.Signal.PrivateSealedSender
import TlsMpc.Signal.PrivateRelay

/-! Selected established-session candidate: one private chain transition,
Signal wire, SSv1 and actual relay WebSocket request. The final envelope/
request status selects all next states; failure retains both old chains.
Shared inner length and all canonical protocol widths survive to the typed
TLS payload. DH inputs here are a curve/backend refinement boundary; the
native adapter must compute them privately, as in NativeService. -/
namespace TlsMpc.Signal.PrivateService

def prepare (o : Aes.Ops B) (v : Varint64.Ops B V) (d : RelayEncoding.DecimalOps B V)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List B)
    (i : SpqrSend.Input B) : PrivateSpqrSend.Prepared B :=
  let inner := PrivateSpqrSend.prepare o v s a hasChunk withAddresses i
  let envelope := PrivateSealedSender.boundSeal o s a i.receiver ephemeralPublic computedSender
    ephemeralDh staticDh certificate i.sender inner.wire
  let request := PrivateRelay.encode s d v a metadata envelope
  ⟨inner.candidateState,request⟩

def output (a : ByteAuth.Ops B) (i : SpqrSend.Input B) (p : PrivateSpqrSend.Prepared B) : List B :=
  PrivateSpqrSend.output a (PrivateSpqrSend.oldState i) p

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {d : RelayEncoding.DecimalOps B V} {d' : RelayEncoding.DecimalOps B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}
  (ho : Aes.Hom o o' f) (hv : Varint64.Hom v v' f fv)
  (hd : RelayEncoding.DecimalHom d d' f fv) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho hv hd hs ha

theorem prepare_map (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List B) (i : SpqrSend.Input B) :
    (prepare o v d s a hasChunk withAddresses ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i).map f =
    prepare o' v' d' s' a' hasChunk withAddresses (ephemeralPublic.map f) (computedSender.map f)
      (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (metadata.map f) (i.map f) := by
  have core := PrivateSpqrSend.prepare_map ho hv hs ha hasChunk withAddresses i
  have state := congrArg PrivateSpqrSend.Prepared.candidateState core
  have wire := congrArg PrivateSpqrSend.Prepared.wire core
  simp only [PrivateSpqrSend.Prepared.map] at state wire
  simp only [prepare,PrivateSpqrSend.Prepared.map,PrivateRelay.encode_map hs hd hv ha,
    PrivateSealedSender.boundSeal_map ho hs ha,state,wire,SpqrSend.Input.map]

omit ho hv hd hs in
theorem output_map (i : SpqrSend.Input B) (p : PrivateSpqrSend.Prepared B) :
    (output a i p).map f = output a' (i.map f) (p.map f) := by
  simp only [output,PrivateSpqrSend.output_map ha,PrivateSpqrSend.oldState_map ha]

end Refinement
open Std.Tactic.BVDecide

theorem compiled_output_correct (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List (BVExpr 8))
    (i : SpqrSend.Input (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (output ByteAuth.symbolic i (prepare Aes.symbolic Varint64.symbolic RelayEncoding.decimalSymbolic Sha256.symbolic
        ByteAuth.symbolic hasChunk withAddresses ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i))
      (output ByteAuth.concrete (i.map (BVExpr.eval assign))
        (prepare Aes.concrete Varint64.concrete RelayEncoding.decimalConcrete Sha256.concrete ByteAuth.concrete
          hasChunk withAddresses (ephemeralPublic.map (BVExpr.eval assign)) (computedSender.map (BVExpr.eval assign))
          (ephemeralDh.map (BVExpr.eval assign)) (staticDh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign))
          (metadata.map (BVExpr.eval assign)) (i.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,output_map (ByteAuth.evaluationHom assign),
    prepare_map (Aes.evaluationHom assign) (Varint64.evaluationHom assign) (RelayEncoding.decimalEvaluationHom assign)
      (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateService
