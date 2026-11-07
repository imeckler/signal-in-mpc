import AesKeyScheduleWork.Generated.Funs

/-! Deterministic public fixture data, never secret runtime state. -/
namespace AesKeySchedulePublicCheck

open Aeneas Aeneas.Std

def key (seed : Nat) : Aeneas.Std.Array U8 32#usize :=
  ⟨List.ofFn (fun (i : Fin 32) => ⟨BitVec.ofNat 8
    (if seed = 0 then 0 else if seed = 1 then 255 else if seed = 2 then i.val
     else i.val * 13 + seed * 17 + i.val * seed * 3)⟩), by simp⟩

end AesKeySchedulePublicCheck
