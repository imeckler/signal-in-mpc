import SealedSenderPackagingWork.Generated.WireContent.Funs

namespace LibSignalReference.Candidate.SealedSenderTypeReplay
open Aeneas Aeneas.Std

theorem source_enum_discriminants_preserved :
    [read_discriminant SealedSenderPackaging.prost.encoding.wire_type.WireType.Varint,
     read_discriminant SealedSenderPackaging.prost.encoding.wire_type.WireType.SixtyFourBit,
     read_discriminant SealedSenderPackaging.prost.encoding.wire_type.WireType.LengthDelimited,
     read_discriminant SealedSenderPackaging.prost.encoding.wire_type.WireType.StartGroup,
     read_discriminant SealedSenderPackaging.prost.encoding.wire_type.WireType.EndGroup,
     read_discriminant SealedSenderPackaging.prost.encoding.wire_type.WireType.ThirtyTwoBit] = [0#u8,1#u8,2#u8,3#u8,4#u8,5#u8] ∧
    [read_discriminant _root_.ProstBytesField.encoding.wire_type.WireType.Varint,
     read_discriminant _root_.ProstBytesField.encoding.wire_type.WireType.SixtyFourBit,
     read_discriminant _root_.ProstBytesField.encoding.wire_type.WireType.LengthDelimited,
     read_discriminant _root_.ProstBytesField.encoding.wire_type.WireType.StartGroup,
     read_discriminant _root_.ProstBytesField.encoding.wire_type.WireType.EndGroup,
     read_discriminant _root_.ProstBytesField.encoding.wire_type.WireType.ThirtyTwoBit] = [0#u8,1#u8,2#u8,3#u8,4#u8,5#u8] ∧
    [read_discriminant ProstBytesCandidate.encoding.wire_type.WireType.Varint,
     read_discriminant ProstBytesCandidate.encoding.wire_type.WireType.SixtyFourBit,
     read_discriminant ProstBytesCandidate.encoding.wire_type.WireType.LengthDelimited,
     read_discriminant ProstBytesCandidate.encoding.wire_type.WireType.StartGroup,
     read_discriminant ProstBytesCandidate.encoding.wire_type.WireType.EndGroup,
     read_discriminant ProstBytesCandidate.encoding.wire_type.WireType.ThirtyTwoBit] = [0#u8,1#u8,2#u8,3#u8,4#u8,5#u8] := by
  exact ⟨rfl,rfl,rfl⟩

end LibSignalReference.Candidate.SealedSenderTypeReplay
