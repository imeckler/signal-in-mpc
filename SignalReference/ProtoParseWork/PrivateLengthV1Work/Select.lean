import TlsMpc.Signal.PrivateProtoParseV1
namespace PrivateLengthV1.Select
open TlsMpc TlsMpc.Signal

theorem zip_left {α : Type} (f : α → α → α) (rule : ∀ x y, f x y = x)
    (yes no : List α) (shape : yes.length = no.length) : List.zipWith f yes no = yes := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all
  | cons x xs ih =>
    cases no with
    | nil => simp at shape
    | cons y ys => simp only [List.zipWith_cons_cons,rule]; congr 1; exact ih ys (by simpa using shape)

theorem zip_right {α : Type} (f : α → α → α) (rule : ∀ x y, f x y = y)
    (yes no : List α) (shape : yes.length = no.length) : List.zipWith f yes no = no := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all
  | cons x xs ih =>
    cases no with
    | nil => simp at shape
    | cons y ys => simp only [List.zipWith_cons_cons,rule]; congr 1; exact ih ys (by simpa using shape)

theorem field_accept (yes no : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 yes no = yes := by
  cases yes
  simp only [ProtoParse.selectField,Unpad.chooseByte_accept,Word64.select_accept]

theorem field_reject (yes no : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 yes no = no := by
  cases no
  simp only [ProtoParse.selectField,Unpad.chooseByte_reject,Word64.select_reject]

theorem state_accept (yes no : ProtoParse.State (BitVec 8) (BitVec 64))
    (stack : yes.stack.length = no.stack.length) (fields : yes.fields.length = no.fields.length) :
    PrivateProtoParseV1.selectState Word64.concrete ByteAuth.concrete 255 yes no = yes := by
  cases yes; cases no
  simp only [PrivateProtoParseV1.selectState,Unpad.chooseByte_accept,Word64.select_accept]
  rw [zip_left _ Word64.select_accept _ _ stack,zip_left _ field_accept _ _ fields]

theorem state_reject (yes no : ProtoParse.State (BitVec 8) (BitVec 64))
    (stack : yes.stack.length = no.stack.length) (fields : yes.fields.length = no.fields.length) :
    PrivateProtoParseV1.selectState Word64.concrete ByteAuth.concrete 0 yes no = no := by
  cases yes; cases no
  simp only [PrivateProtoParseV1.selectState,Unpad.chooseByte_reject,Word64.select_reject]
  rw [zip_right _ Word64.select_reject _ _ stack,zip_right _ field_reject _ _ fields]

#print axioms state_accept
#print axioms state_reject
end PrivateLengthV1.Select
