import TlsMpc.TlsWorker

/-! Bounded binary pipe transport for the public worker RPC. The native service
must reserve stdout for these responses and send diagnostics to stderr. This
transport carries public metadata only. A mutex serializes whole exchanges;
application receives poll rather than monopolizing this pipe while idle.
-/
namespace TlsMpc.TlsWorkerPipe
open TlsWire TlsClient TlsWorker

def code : Operation → Nat
  | .begin => 1 | .derive => 2 | .openHandshake => 3 | .authenticate => 4
  | .verifyFinished => 5 | .finish => 6 | .retire => 7 | .abort => 8
  | .connect => 9 | .sendRecord => 10 | .receiveRecord => 11
  | .openApplication => 12 | .sealApplication => 13 | .sealControl => 14
  | .rotateSend => 15 | .rotateReceive => 16
  | .pollRecord => 17
  | .processWebSocket => 18
  | .providerCatalogue => 19 | .providerUpgrade => 20 | .providerProduce => 21
  | .muxCatalogue => 22 | .muxUpgrade => 23 | .muxProduce => 24 | .muxProcess => 25 | .muxProduceBatch => 26 | .muxResumeOutbox => 27 | .muxCheckpointOutcomes => 28
  | .revealApplication => 29 | .publicBuffer => 30 | .providerProduceOpen => 31 | .providerUpgradeOpen => 32
  | .publicRandom => 33 | .providerSealOpen => 34 | .providerRequest => 35
  | .contactKey => 36 | .contactOpen => 37 | .contactSeal => 38 | .exchange => 39 | .contactEvict => 40
  | .contactSend => 41 | .contactRequest => 42

def maxPayload : Nat := 2 * 1024 * 1024

def frame (operation : Operation) (sequence : Nat) (payload : Bytes) : Bytes :=
  [UInt8.ofNat (code operation)] ++ uint 8 sequence ++ uint 4 payload.length ++ payload

def readLoop (stream : IO.FS.Stream) : Nat → Nat → Bytes → M Bytes
  | 0, _, _ => throw "worker pipe read exhausted"
  | fuel + 1, remaining, accumulated => do
      if remaining == 0 then return accumulated.reverse
      let part ← liftM (stream.read (USize.ofNat remaining))
      insist (!part.isEmpty && part.size ≤ remaining) "truncated worker pipe response"
      readLoop stream fuel (remaining - part.size) (part.data.toList.reverse ++ accumulated)

def readExact (stream : IO.FS.Stream) (size : Nat) : M Bytes := do
  insist (size ≤ maxPayload) "worker pipe response exceeds bound"
  readLoop stream (size+1) size []

private structure PipeState where
  next : Nat := 0
  failed : Bool := false
  cleanupAvailable : Bool := false

def make (input output : IO.FS.Stream)
    (authenticate : String → List Bytes → Nat → Bytes → Bytes → M Bool) : IO Rpc := do
  let state ← Std.Mutex.new ({} : PipeState)
  return {
    authenticate
    call := fun operation payload => ExceptT.mk <| state.atomically fun stateRef => do
      let before ← stateRef.get
      if before.failed && !(operation == .abort && before.cleanupAvailable) then
        return .error "worker pipe is terminal after failure"
      let action : M Bytes := do
        insist (payload.length ≤ maxPayload) "worker pipe request exceeds bound"
        let sequence := before.next
        insist (sequence < 2^64) "worker request sequence exhausted"
        liftM (stateRef.set { before with next := sequence+1, cleanupAvailable := false } : IO Unit)
        liftM (output.write ⟨(frame operation sequence payload).toArray⟩)
        liftM output.flush
        let header ← readExact input 5
        let size := number (header.drop 1)
        let response ← readExact input size
        let status := header[0]?.getD 255
        insist (status == 0 || (status == 1 && response.isEmpty)) "invalid worker pipe status"
        if status == 1 then
          -- A complete, bounded rejection preserves framing. Private work stays
          -- terminal; only a cleanup receipt may use this pipe afterward.
          liftM (stateRef.modify (fun current => { current with cleanupAvailable := true }) : IO Unit)
          throw "native worker rejected the operation"
        if before.failed then
          liftM (stateRef.modify (fun current => { current with cleanupAvailable := true }) : IO Unit)
        return response
      let result ← try action.run catch _ => pure (.error "worker pipe I/O failed")
      match result with
      | .error _ => stateRef.modify fun current => { current with failed := true }
      | .ok _ => pure ()
      return result }
end TlsMpc.TlsWorkerPipe
