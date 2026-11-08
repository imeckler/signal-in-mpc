import ChatResponseReferenceWork.GeneratedMetadataPositive.Funs
open Aeneas Aeneas.Std
namespace ChatResponseReference
open ActualChatResponseMetadata_positive

/-- The success regression executes the generated transformed source, rather
than merely comparing a fixture's length to itself. It holds for all valid
contiguous byte slices, including empty and maximal represented lengths. -/
theorem lowered_slice_metadata (bytes : Slice U8) :
    slice_metadata_positive bytes = .ok bytes.len := by
  rfl

theorem lowered_seed_metadata (bytes : Slice U8) :
    reference_length_seed bytes = .ok bytes.len := by
  rfl

theorem metadata_native_length (bytes : Slice U8) : bytes.len.val = bytes.length := Slice.len_val bytes

#print axioms lowered_slice_metadata
#print axioms lowered_seed_metadata
#print axioms metadata_native_length
end ChatResponseReference
