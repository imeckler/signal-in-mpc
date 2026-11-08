import ProtoParseWork.FullParserV3Work.WrongWireRejectionStep
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

private theorem wrong_kind (kind : LoopSupportSkip.encoding.wire_type.WireType) (hw : kind ≠ .LengthDelimited) :
    BitVec.ofNat 64 (LibSignalReference.Candidate.ProstSkipKey.wireNumber kind) ≠ 2 := by
  cases kind <;> first | exact False.elim (hw rfl) | decide

/-- All actual bytes wrong-wire keys, including closing groups, reject with
the Rust wire constructor and expected LengthDelimited parameter and preserve the exact
cursor and initialized full field record through the remaining public scan. -/
theorem actual_bytes_wrong_rejection (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hs : state.parser.ok = 255)
    (hn : state.parser.next = BitVec.ofNat 64 position) (hd : state.parser.depth = 0)
    (ht : BytesTag tag) (hw : kind ≠ .LengthDelimited)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle)) :
    ∀ positions : List Nat, ActiveRejection bytes middle
      (LibSignalReference.Candidate.ProstBytes.decodeError
        (.UnexpectedWireType (toBytesWire (signalWire kind)) .LengthDelimited)) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)))
      (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 tag.val) state.parser.fields) := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,htag,hkind,_⟩ := actual_key_row bytes middle position tag kind hp hk
  have htags : key.value >>> 3 = 1 ∨ key.value >>> 3 = 4 ∨ key.value >>> 3 = 5 ∨ key.value >>> 3 = 6 := by
    rw [htag]; rcases ht with rfl | rfl | rfl | rfl <;> decide
  have hwrong : key.value &&& 7 ≠ 2 := by
    rw [hkind]
    exact wrong_kind kind hw
  exact wrong_wire_rejection_step bytes middle position tag kind _ state hp hcap hs hn hd hk
    (valid_known_bytes_wrong key state.parser hd htags hwrong)
    (bytes_wrong_parameter key tag kind ht htag hkind)

#print axioms actual_bytes_wrong_rejection
end FullParserV3.Observed
