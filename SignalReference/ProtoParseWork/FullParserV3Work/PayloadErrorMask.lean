import ProtoParseWork.FullParserV3Work.PayloadPlan
import ProtoParseWork.FullParserV3Work.KeyRow
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 3000000

theorem plan_payload_error (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hp : payload.ok = 0)
    (hkind : key.value &&& 7 = 0 ∨ key.value &&& 7 = 2) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rcases hkind with hk | hk
  all_goals simp only [ProtoParse.plan,show Word64.concrete.band key.value (Word64.concrete.const 7) = key.value &&& 7 from rfl,hk,
    show Word64.eq Word64.concrete ByteAuth.concrete (0 : BitVec 64) (Word64.concrete.const 0) = 255 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (0 : BitVec 64) (Word64.concrete.const 1) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (0 : BitVec 64) (Word64.concrete.const 2) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (0 : BitVec 64) (Word64.concrete.const 3) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (0 : BitVec 64) (Word64.concrete.const 4) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (0 : BitVec 64) (Word64.concrete.const 5) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 0) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 1) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 2) = 255 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 3) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 4) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 5) = 0 from by decide,hp,hz,hz',Word64.bor,show ByteAuth.concrete.xor 0 0 = 0 from rfl]

theorem actual_payload_error_mask (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : LoopSupportSkip.error.DecodeError)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after)) :
    let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
    (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1)
      (((rowsOf bytes).drop (position+1)).take 10)).ok = 0 := by
  obtain ⟨kc,h1,h10,hb,hmiddle,_,hstop,_,_,_,_,_⟩ := actual_key_row bytes middle position tag kind hp hk
  dsimp only
  rw [hstop]
  by_cases hmore : position+kc < bytes.length
  · apply payload_actual_error bytes after position kc error h1 h10 hmore (by omega)
    simpa only [hmiddle] using hd
  · have he : position+kc = bytes.length := by omega
    rw [he]
    have hl : (rowsOf bytes).length = bytes.length := by rw [table_length]; exact List.length_map _
    have hend := payload_window_end (rowsOf bytes) position (by rw [hl]; exact hp) (by rw [hl]; omega)
    simp only [hl] at hend
    rw [hend]

#print axioms plan_payload_error
#print axioms actual_payload_error_mask
end FullParserV3
