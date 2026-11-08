import ProtoParseWork.FullParserV3Work.KeyErrors
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

def skipStatusView (result : core.result.Result Unit error.DecodeError) :=
  statusView (match result with | .Ok () => .Ok () | .Err e => .Err (SignalMessageIntegration.skipError e))
def Represented (result : core.result.Result Unit error.DecodeError) : Prop :=
  ∃ encoded, skipStatusView result = some encoded

private theorem represented_ok : Represented (.Ok ()) := ⟨⟨0,0⟩,rfl⟩
private theorem represented_invalid : Represented (.Err invalidError) := ⟨⟨1,0⟩,rfl⟩
private theorem represented_fixed (bytes : Slice U8) (width : Nat) :
    Represented (fixedResult bytes width).1 := by
  unfold fixedResult
  split
  · exact ⟨⟨6,0⟩,rfl⟩
  · exact represented_ok

/-- Every error from the actual contiguous varint decoder belongs to the
constructor/payload projection; this is derived from its full reference. -/
theorem varint_error_represented (bytes after : Slice U8) (e : error.DecodeError)
    (hd : encoding.varint.decode_varint sliceBuf bytes = .ok (.Err e,after)) :
    Represented (.Err e) := by
  obtain ⟨result,remaining,hr,hp,_⟩ := decode_full_reference bytes
  rw [hd] at hr
  cases hr
  have he := hp.1
  rw [he]
  exact represented_invalid

theorem key_error_represented (bytes after : Slice U8) (e : error.DecodeError)
    (hd : encoding.decode_key sliceBuf bytes = .ok (.Err e,after)) :
    Represented (.Err e) := by
  exact ⟨_,actual_key_error bytes after e ⟨0,0,0⟩ (ProtoParse.initial Word64.concrete ByteAuth.concrete 0) hd⟩

/-- Finite skip derivations cannot introduce any unrepresented constructor.
Together with constructive skip totality this removes a diagnostic-domain
assumption, including malformed keys inside nested groups. -/
theorem skip_errors_represented {mode tag count bytes result}
    (derivation : SkipSemantics mode tag count bytes result) : Represented result.1 := by
  induction derivation with
  | limit => exact ⟨⟨7,0⟩,rfl⟩
  | endField => exact ⟨⟨8,0⟩,rfl⟩
  | fixed32 => exact represented_fixed _ _
  | fixed64 => exact represented_fixed _ _
  | varint => exact represented_ok
  | varintError _ hd => exact varint_error_represented _ _ _ hd
  | length => exact represented_fixed _ _
  | lengthError _ hd => exact varint_error_represented _ _ _ hd
  | start _ _ ih => exact ih
  | keyError hd => exact key_error_represented _ _ _ hd
  | close =>
    unfold groupClose
    split
    · exact represented_ok
    · exact ⟨⟨8,0⟩,rfl⟩
  | childError _ _ _ _ ih => exact ih
  | childNext _ _ _ _ _ _ ih => exact ih

#print axioms varint_error_represented
#print axioms key_error_represented
#print axioms skip_errors_represented
end FullParserV3.Observed
