import ChatResponseReferenceWork.ParserCircuitCandidateV1.TrimMux
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Public index map of expandInput; none denotes an inserted zero byte. -/
def expandedSourceIndex (index : Nat) : Option Nat :=
  if index < 73 then some index
  else if index < 873 then
    if (index-73)%8 < 4 then none
    else some (73+4*((index-73)/8)+((index-73)%8-4))
  else some (index-400)

theorem retained_inverse : ∀ index : Fin 585,
    expandedSourceIndex (retainedIndex index.val) = some index.val ∧ retainedIndex index.val < 986 := by
  decide +kernel

def expandedInverseTest (index : Nat) : Bool :=
  match expandedSourceIndex index with
  | none => true
  | some compact => decide (compact < 585 ∧ retainedIndex compact = index)

theorem expanded_inverse_test : ∀ index : Fin 985, expandedInverseTest index.val = true := by
  decide +kernel

theorem expanded_inverse (index : Fin 985) :
    match expandedSourceIndex index.val with
    | none => True
    | some compact => compact < 585 ∧ retainedIndex compact = index.val := by
  have test := expanded_inverse_test index
  unfold expandedInverseTest at test
  cases source : expandedSourceIndex index.val with
  | none => trivial
  | some compact =>
    simp only [source] at test ⊢
    exact of_decide_eq_true test

theorem get_expanded (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 986) :
    TlsWebSocketUpgrade.get a (expandInput a raw) index =
    match expandedSourceIndex index with
    | none => a.const 0
    | some source => TlsWebSocketUpgrade.get a raw source := by
  by_cases first : index < 73 <;> by_cases second : index < 873 <;>
    by_cases high : (index-73)%8 < 4 <;>
    simp [expandInput,TlsWebSocketUpgrade.get,bound,expandedSourceIndex,first,second,high]

theorem get_compact (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 585) :
    TlsWebSocketUpgrade.get a (compactOutput a raw) index =
    TlsWebSocketUpgrade.get a raw (retainedIndex index) := by
  simp [compactOutput,compactOutputSize,TlsWebSocketUpgrade.get,bound]

theorem compact_expand (a : ByteAuth.Ops B) (raw : List B) :
    compactOutput a (expandInput a raw) =
    (List.range 585).map (TlsWebSocketUpgrade.get a raw) := by
  apply List.map_congr_left
  intro index member
  have bound : index < 585 := List.mem_range.mp member
  have inverse := retained_inverse ⟨index,bound⟩
  rw [get_expanded a raw _ inverse.2,inverse.1]

/-- Serialized projection. It erases only the first four bytes of each stack
word; all other output bytes, including every event byte, remain unchanged. -/
def projectedByte (a : ByteAuth.Ops B) (raw : List B) (index : Nat) : B :=
  match expandedSourceIndex index with
  | none => a.const 0
  | some _ => TlsWebSocketUpgrade.get a raw index

theorem expand_compact_get (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 985) :
    TlsWebSocketUpgrade.get a (expandInput a (compactOutput a raw)) index = projectedByte a raw index := by
  rw [get_expanded a _ index (by omega)]
  have inverse := expanded_inverse ⟨index,bound⟩
  unfold projectedByte
  cases source : expandedSourceIndex index with
  | none => rfl
  | some compact =>
    simp only [source] at inverse ⊢
    rw [get_compact a raw compact inverse.1,inverse.2]

#print axioms retained_inverse
#print axioms expanded_inverse
#print axioms compact_expand
#print axioms expand_compact_get
end ChatResponseReference.ParserCircuitCandidateV1
