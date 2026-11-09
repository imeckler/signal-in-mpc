import ChatResponseReferenceWork.ParserCircuitCandidateV1.SerializedTrim
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

def compactInput (a : ByteAuth.Ops B) (full : List B) : List B :=
  (List.range 586).map (fun i => TlsWebSocketUpgrade.get a full (retainedIndex i))

def expandedInputTest (index : Nat) : Bool :=
  match expandedSourceIndex index with
  | none => true
  | some compact => decide (compact < 586 ∧ retainedIndex compact = index)

theorem expanded_input_test : ∀ index : Fin 986, expandedInputTest index.val = true := by
  decide +kernel

theorem get_compact_input (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 586) :
    TlsWebSocketUpgrade.get a (compactInput a raw) index =
    TlsWebSocketUpgrade.get a raw (retainedIndex index) := by
  simp [compactInput,TlsWebSocketUpgrade.get,bound]

theorem expand_compact_input_get (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 986) :
    TlsWebSocketUpgrade.get a (expandInput a (compactInput a raw)) index = projectedByte a raw index := by
  rw [get_expanded a _ index bound]
  have inverse := expanded_input_test ⟨index,bound⟩
  unfold projectedByte expandedInputTest at *
  cases source : expandedSourceIndex index with
  | none => rfl
  | some compact =>
    simp only [source] at inverse ⊢
    have correct : compact < 586 ∧ retainedIndex compact = index := of_decide_eq_true inverse
    rw [get_compact_input a raw compact correct.1,correct.2]

def encodeCompactInput (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) : List (BitVec 8) :=
  compactInput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ [active,beginning,ending,byte])

theorem expand_encoded_input (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (active beginning ending byte : BitVec 8) :
    expandInput ByteAuth.concrete (encodeCompactInput state active beginning ending byte) =
    TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ [active,beginning,ending,byte] := by
  have leftLength := expand_length ByteAuth.concrete (encodeCompactInput state active beginning ending byte)
  have rightLength : (TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ [active,beginning,ending,byte]).length = 986 := by
    simp only [List.length_append,mux_bytes_length _ (mux_trim_codec_shape state shape),List.length_cons,List.length_nil]
  apply List.ext_getElem (leftLength.trans rightLength.symm)
  intro index left right
  have bound : index < 986 := by simpa only [leftLength] using left
  have eq := (expand_compact_input_get ByteAuth.concrete
    (TlsChatResponseMux.stateBytes Word64.concrete state ++ [active,beginning,ending,byte]) index bound).trans
    (serialized_mux_trim_get state shape [active,beginning,ending,byte] index).symm
  simp only [encodeCompactInput] at left ⊢
  simpa only [TlsWebSocketUpgrade.get,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,Option.getD_some] using eq

#print axioms expanded_input_test
#print axioms expand_encoded_input
end ChatResponseReference.ParserCircuitCandidateV1
