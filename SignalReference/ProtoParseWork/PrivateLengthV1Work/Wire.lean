import ProtoParseWork.PrivateLengthV1Work.Metadata
namespace PrivateLengthV1.Wire
open TlsMpc TlsMpc.Signal
open ProtoParse

def stackTail (wire : List B) (length : Nat) : Nat :=
  min 100 (ProtoParse.body wire).length-min 100 (length-9)

/-- Proof-only name for the production acceptance expression. Its connection
below is definitional; it adds no diagnostic gates to production. -/
def acceptance (o : Word64.Ops B W) (a : ByteAuth.Ops B) (framing : B)
    (wire : List B) (bodyLength : W) (bytes : List B) (state : ProtoParse.State B W)
    (upstreamValid : B) : B :=
  let ratchet := getField o a state 0
  a.and framing (a.and (ByteAuth.eqMask a upstreamValid (a.const 255))
    (a.and (Receive.versionMask a wire)
      (a.and (PrivateProtoParseV1.completeMask o a bodyLength state)
        (a.and ratchet.present (a.and (getField o a state 1).present
          (a.and (getField o a state 3).present
            (a.and (o.ule (o.const 33) ratchet.length)
              (ByteAuth.eqMask a (OpenResult.get a (PrivateProtoParseV1.ratchetRead o a bodyLength bytes state) 9) (a.const 5)))))))))


theorem body_parse_take (wire : List (BitVec 8)) (length : Nat)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    PrivateProtoParseV1.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 (length-9)) (ProtoParse.body wire) =
    Stack.pad (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (ProtoParse.body (wire.take length))) (stackTail wire length) := by
  rw [Scan.parseBody_take (ProtoParse.body wire) (length-9)
    (by rw [Framing.body_length]; omega) (by rw [Framing.body_length]; omega)]
  rw [←Framing.body_take wire length within]
  rfl

theorem state_take (wire : List (BitVec 8)) (length : Nat) (upstream : BitVec 8)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    (PrivateProtoParseV1.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire
      (BitVec.ofNat 8 (length/256)) (BitVec.ofNat 8 length) upstream).state =
    Stack.pad (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (ProtoParse.body (wire.take length))) (stackTail wire length) := by
  simp only [PrivateProtoParseV1.parse,Framing.be16 length (by omega),
    Framing.body_length_word wire.length length within capacity]
  exact body_parse_take wire length within capacity

theorem acceptance_take (wire : List (BitVec 8)) (length count : Nat) (upstream : BitVec 8)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    acceptance Word64.concrete ByteAuth.concrete (if 9 ≤ length then 255 else 0) wire
      (BitVec.ofNat 64 (length-9)) (ProtoParse.body wire) (Stack.pad state count) upstream =
    ByteAuth.concrete.and (ByteAuth.eqMask ByteAuth.concrete upstream (ByteAuth.concrete.const 255))
      (ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete (wire.take length) state) := by
  unfold acceptance ProtoParse.acceptedMask
  rw [Metadata.complete_pad,Metadata.ratchet_take wire length count within capacity state]
  simp only [Metadata.field_pad,Framing.body_length,List.length_take,Nat.min_eq_left within]
  by_cases enough : 9 ≤ length
  · simp only [if_pos enough]
    rw [Framing.version_take wire length (by omega)]
    simp [ByteAuth.concrete]
  · simp [enough,ByteAuth.concrete]

theorem valid_take (wire : List (BitVec 8)) (length : Nat) (upstream : BitVec 8)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    (PrivateProtoParseV1.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire
      (BitVec.ofNat 8 (length/256)) (BitVec.ofNat 8 length) upstream).valid =
    ByteAuth.concrete.and (ByteAuth.eqMask ByteAuth.concrete upstream (ByteAuth.concrete.const 255))
      (ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete (wire.take length)
        (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (ProtoParse.body (wire.take length)))) := by
  simp only [PrivateProtoParseV1.parse,Framing.be16 length (by omega),
    Framing.body_length_word wire.length length within capacity,body_parse_take wire length within capacity]
  change acceptance Word64.concrete ByteAuth.concrete _ wire _ _ _ upstream = _
  rw [Framing.framing_mask wire.length length within capacity]
  exact acceptance_take wire length (stackTail wire length) upstream within capacity _


theorem length_take (wire : List (BitVec 8)) (length : Nat) (upstream : BitVec 8)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    (PrivateProtoParseV1.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire
      (BitVec.ofNat 8 (length/256)) (BitVec.ofNat 8 length) upstream).bodyLength =
      BitVec.ofNat 64 (length-9) := by
  simp only [PrivateProtoParseV1.parse,Framing.be16 length (by omega),
    Framing.body_length_word wire.length length within capacity]

theorem metadata_output_take (wire : List (BitVec 8)) (length : Nat) (upstream : BitVec 8)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    (PrivateProtoParseV1.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire
      (BitVec.ofNat 8 (length/256)) (BitVec.ofNat 8 length) upstream).metadata =
    let state := ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (ProtoParse.body (wire.take length))
    let valid := ByteAuth.concrete.and (ByteAuth.eqMask ByteAuth.concrete upstream (ByteAuth.concrete.const 255))
      (ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete (wire.take length) state)
    ByteAuth.release ByteAuth.concrete valid (ProtoParse.metadata Word64.concrete ByteAuth.concrete (wire.take length) state) := by
  simp only [PrivateProtoParseV1.parse,Framing.be16 length (by omega),
    Framing.body_length_word wire.length length within capacity,body_parse_take wire length within capacity]
  change ByteAuth.release ByteAuth.concrete
    (acceptance Word64.concrete ByteAuth.concrete _ wire _ _ _ upstream)
    (PrivateProtoParseV1.metadata Word64.concrete ByteAuth.concrete _ wire _) = _
  rw [Framing.framing_mask wire.length length within capacity,
    acceptance_take wire length (stackTail wire length) upstream within capacity,
    Metadata.metadata_take wire length (stackTail wire length) within capacity]

theorem core_projection (wire : List (BitVec 8)) (length : Nat) (upstream : BitVec 8)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    PrivateProtoParseV1.parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire
      (BitVec.ofNat 8 (length/256)) (BitVec.ofNat 8 length) upstream =
    let state := ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (ProtoParse.body (wire.take length))
    let valid := ByteAuth.concrete.and (ByteAuth.eqMask ByteAuth.concrete upstream (ByteAuth.concrete.const 255))
      (ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete (wire.take length) state)
    valid :: ByteAuth.release ByteAuth.concrete valid (ProtoParse.metadata Word64.concrete ByteAuth.concrete (wire.take length) state) := by
  simp only [PrivateProtoParseV1.parseCore,valid_take wire length upstream within capacity,
    metadata_output_take wire length upstream within capacity]

/-- Full version/body/MAC framing and released-output agreement for every
secret total length. Padding cannot change parsing or metadata. -/
theorem parseCore_take (wire : List (BitVec 8)) (length : Nat)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512) :
    PrivateProtoParseV1.parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire
      (BitVec.ofNat 8 (length/256)) (BitVec.ofNat 8 length) 255 =
    ProtoParse.parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (wire.take length) := by
  rw [core_projection wire length 255 within capacity]
  have mask (value : BitVec 8) : ByteAuth.concrete.and
      (ByteAuth.eqMask ByteAuth.concrete 255 (ByteAuth.concrete.const 255)) value = value := by
    have equal : ByteAuth.eqMask ByteAuth.concrete 255 (ByteAuth.concrete.const 255) = 255 := rfl
    rw [equal]
    exact BitVec.allOnes_and
  simp only [mask,ProtoParse.parseCore]

#print axioms state_take
#print axioms valid_take
#print axioms metadata_output_take
#print axioms parseCore_take
end PrivateLengthV1.Wire
