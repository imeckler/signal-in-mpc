import ChatResponseReferenceWork.ParserCircuitCandidateV1.CodecIndices
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

theorem pack_word_bytes (word : BitVec 64) :
    Word64.concrete.pack (Word64.bytes Word64.concrete word) = word := by
  change (((word.extractLsb' 56 8 ++ word.extractLsb' 48 8) ++
    (word.extractLsb' 40 8 ++ word.extractLsb' 32 8)) ++
    ((word.extractLsb' 24 8 ++ word.extractLsb' 16 8) ++
    (word.extractLsb' 8 8 ++ word.extractLsb' 0 8))) = word
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb'

theorem trimmed_word_bytes (word : BitVec 64) :
    Word64.bytes Word64.concrete (trimWord word) =
    List.replicate 4 (0 : BitVec 8) ++ (Word64.bytes Word64.concrete word).drop 4 := by
  change [_,_,_,_,_,_,_,_] = [0,0,0,0,_,_,_,_]
  simp only [Word64.concrete,trimWord,BitVec.extractLsb'_and]
  change [word.extractLsb' 56 8 &&& 0,word.extractLsb' 48 8 &&& 0,
    word.extractLsb' 40 8 &&& 0,word.extractLsb' 32 8 &&& 0,
    word.extractLsb' 24 8 &&& 255,word.extractLsb' 16 8 &&& 255,
    word.extractLsb' 8 8 &&& 255,word.extractLsb' 0 8 &&& 255] =
    [0,0,0,0,word.extractLsb' 24 8,word.extractLsb' 16 8,word.extractLsb' 8 8,word.extractLsb' 0 8]
  have keep (byte : BitVec 8) : byte &&& 255 = byte := BitVec.and_allOnes
  have erase (byte : BitVec 8) : byte &&& 0 = 0 := BitVec.and_zero
  simp only [erase,keep]

#print axioms pack_word_bytes
#print axioms trimmed_word_bytes
end ChatResponseReference.ParserCircuitCandidateV1
