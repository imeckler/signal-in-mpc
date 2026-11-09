import ChatResponseReferenceWork.StreamingV1.KnownKeyReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Executable source projection for the fields actually cached by Core.
Full body/String/header content remains in source results and event references. -/
def optionMask {T : Type} : Option T → BitVec 8
  | none => 0
  | some _ => 255

def sourceCache (outer : ResponseData) (source : InnerResponseV1.Message) : ResponseData :=
  {outer with
    idPresent := optionMask source.id
    id := (source.id.getD core.default.DefaultU64.default).bv
    status := statusWord (source.status.getD core.default.DefaultU32.default)
    bodyPresent := optionMask source.body
    bodyLength := match source.body with
      | none => 0
      | some body => BitVec.ofNat 64 body.contents.length
    messagePresent := optionMask source.message}

def CacheAgrees (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop :=
  responseData state = sourceCache outer source

theorem source_cache_id (outer : ResponseData) (source : InnerResponseV1.Message) (native : U64) :
    sourceCache outer {source with id := some native} = scalarUpdateData false (sourceCache outer source) native := rfl

theorem source_cache_status (outer : ResponseData) (source : InnerResponseV1.Message) (native : U64) :
    sourceCache outer {source with status := some (UScalar.cast .U32 native)} = scalarUpdateData true (sourceCache outer source) native := rfl

theorem source_cache_message (outer : ResponseData) (source : InnerResponseV1.Message) (value : ActualInnerResponseV1.String) :
    sourceCache outer {source with message := some value} = {sourceCache outer source with messagePresent := 255} := rfl

theorem source_cache_body (outer : ResponseData) (source : InnerResponseV1.Message) (after : Slice U8) (native : U64)
    (fits : native.val ≤ after.length) :
    sourceCache outer {source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩} =
      {sourceCache outer source with bodyPresent := 255,bodyLength := native.bv} := by
  have length := copied_body_length after native fits
  have nativeBound : native.val < 2^64 := native.bv.isLt
  have nativeBits : BitVec.ofNat 64 native.val = native.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound,UScalar.bv_toNat]
  simp only [sourceCache,optionMask,Option.getD_some,length,nativeBits]

theorem source_cache_headers (outer : ResponseData) (source : InnerResponseV1.Message)
    (headers : alloc.vec.Vec ActualInnerResponseV1.String) :
    sourceCache outer {source with headers := headers} = sourceCache outer source := rfl

def sourceDefault : InnerResponseV1.Message :=
  {id := none,status := none,message := none,headers := alloc.vec.Vec.new ActualInnerResponseV1.String,body := none}

theorem actual_default_cache (outer : ResponseData) :
    ActualInnerResponseV1.default_response = .ok sourceDefault ∧
    sourceCache outer sourceDefault = {outer with idPresent := 0,id := 0,status := 0,bodyPresent := 0,bodyLength := 0,messagePresent := 0} :=
  ⟨rfl,rfl⟩

#print axioms actual_default_cache
#print axioms source_cache_id
#print axioms source_cache_status
#print axioms source_cache_message
#print axioms source_cache_body
#print axioms source_cache_headers
end ChatResponseReference.StreamingV1
