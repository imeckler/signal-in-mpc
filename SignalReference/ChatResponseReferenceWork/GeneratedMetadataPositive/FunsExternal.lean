import ChatResponseReferenceWork.GeneratedMetadataPositive.Types
namespace ActualChatResponseMetadata_positive
open Aeneas Aeneas.Std
/-- Valid shared byte-slice fat-pointer metadata in the functional slice model.
No UTF8 assumption or byte validation is introduced by this length model. -/
def slice_metadata_len (input : Slice U8) : Result Usize := .ok input.len
end ActualChatResponseMetadata_positive
