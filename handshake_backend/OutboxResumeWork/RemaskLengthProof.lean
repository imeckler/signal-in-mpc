import TlsMpc.TlsWebSocketRemask
namespace TlsMpc.TlsWebSocketRemask
private theorem and_flags (p q : Prop) [Decidable p] [Decidable q] :
 ByteAuth.concrete.and (if p then 255 else 0) (if q then 255 else 0) =
 if p∧q then 255 else 0 := by
 by_cases hp:p <;> by_cases hq:q <;> simp [hp,hq,ByteAuth.concrete]
private theorem or_flags (p q : Prop) [Decidable p] [Decidable q] :
 TlsPrivateSeal.orMask ByteAuth.concrete (if p then 255 else 0) (if q then 255 else 0) =
 if p∨q then 255 else 0 := by
 by_cases hp:p <;> by_cases hq:q <;> simp [hp,hq,TlsPrivateSeal.orMask,ByteAuth.concrete]
attribute [local instance] Classical.propDecidable
-- Exact acceptance of the bounded length scan; arbitrary secret length bytes.
theorem lengthMatch_value (hi lo wh wl : BitVec 8) (offset count : Nat)
 (bound : offset+count≤65536) :
 lengthMatch ByteAuth.concrete hi lo wh wl offset count =
 if ∃ n, offset≤n ∧ n<offset+count ∧ 134≤n ∧
     TlsPrivateSeal.lengthValue hi lo=n ∧ TlsPrivateSeal.lengthValue wh wl=n-8 then 255 else 0 := by
 induction count generalizing offset with
 | zero =>
   have none : ¬∃ n, offset≤n ∧ n<offset+0 ∧ 134≤n ∧
       TlsPrivateSeal.lengthValue hi lo=n ∧ TlsPrivateSeal.lengthValue wh wl=n-8 := by
     rintro ⟨n,h1,h2,_⟩;omega
   simp only [lengthMatch,if_neg none]
   rfl
 | succ count ih =>
   have here : (if 134≤offset then ByteAuth.concrete.and
       (TlsPrivateSeal.eqLength ByteAuth.concrete hi lo offset)
       (TlsPrivateSeal.eqLength ByteAuth.concrete wh wl (offset-8)) else ByteAuth.concrete.const 0) =
       if 134≤offset ∧ TlsPrivateSeal.lengthValue hi lo=offset ∧
           TlsPrivateSeal.lengthValue wh wl=offset-8 then 255 else 0 := by
     by_cases h:134≤offset
     · simp only [if_pos h,TlsPrivateSeal.eqLength_value hi lo offset (by omega),
         TlsPrivateSeal.eqLength_value wh wl (offset-8) (by omega),and_flags]
       simp [h]
     · simp [h,ByteAuth.concrete]
   rw [lengthMatch,here,ih (offset+1) (by omega),or_flags]
   have split : (134≤offset ∧ TlsPrivateSeal.lengthValue hi lo=offset ∧
        TlsPrivateSeal.lengthValue wh wl=offset-8) ∨
      (∃ n, offset+1≤n ∧ n<offset+1+count ∧ 134≤n ∧
        TlsPrivateSeal.lengthValue hi lo=n ∧ TlsPrivateSeal.lengthValue wh wl=n-8) ↔
      ∃ n, offset≤n ∧ n<offset+(count+1) ∧ 134≤n ∧
        TlsPrivateSeal.lengthValue hi lo=n ∧ TlsPrivateSeal.lengthValue wh wl=n-8 := by
     constructor
     · rintro (⟨h,l,w⟩|⟨n,a,b,h,l,w⟩)
       · exact ⟨offset,by omega,by omega,h,l,w⟩
       · exact ⟨n,by omega,by omega,h,l,w⟩
     · rintro ⟨n,a,b,h,l,w⟩
       by_cases same:n=offset
       · exact Or.inl ⟨by omega,by omega,by omega⟩
       · exact Or.inr ⟨n,by omega,by omega,h,l,w⟩
   simp only [split]
#print axioms lengthMatch_value
end TlsMpc.TlsWebSocketRemask
