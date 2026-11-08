import ChatResponseReferenceWork.Utf8Spec
open TlsMpc
namespace ChatResponseReference.Utf8
set_option maxHeartbeats 2000000

def flag (value : Bool) : BitVec 8 := if value then 255 else 0

theorem flag_either (x y : Bool) :
    TlsWebSocketUpgrade.either ByteAuth.concrete (flag x) (flag y) = flag (x || y) := by
  cases x <;> cases y <;> rfl

theorem eq_flag (byte : BitVec 8) (n : Nat) :
    TlsWebSocketUpgrade.eq ByteAuth.concrete byte n = flag (decide (byte = BitVec.ofNat 8 n)) := by
  change ByteAuth.eqMask ByteAuth.concrete byte (BitVec.ofNat 8 n) = _
  rw [ByteAuth.eqMask_value]
  by_cases h : byte = BitVec.ofNat 8 n <;> simp only [h,if_true,if_false,flag,decide_true,decide_false,Bool.false_eq_true]

theorem fold_flags (values : List Bool) (initial : Bool) :
    (values.map flag).foldl (TlsWebSocketUpgrade.either ByteAuth.concrete) (flag initial) =
      flag (values.foldl (· || ·) initial) := by
  induction values generalizing initial with
  | nil => rfl
  | cons value rest ih => rw [List.map_cons,List.foldl_cons,flag_either,List.foldl_cons]; exact ih _

theorem fold_or (values : List Bool) (initial : Bool) :
    values.foldl (· || ·) initial = (initial || values.any id) := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest ih => simp only [List.foldl_cons,List.any_cons,ih,Bool.or_assoc,id_eq]

theorem member_flag (byte : BitVec 8) (values : List Nat) :
    TlsWebSocketUpgrade.member ByteAuth.concrete byte values =
      flag (values.any (fun n => decide (byte = BitVec.ofNat 8 n))) := by
  have hm : values.map (TlsWebSocketUpgrade.eq ByteAuth.concrete byte) =
      (values.map (fun n => decide (byte = BitVec.ofNat 8 n))).map flag := by
    simp only [List.map_map,Function.comp_def]
    exact List.map_congr_left (fun _ _ => eq_flag byte _)
  unfold TlsWebSocketUpgrade.member TlsWebSocketUpgrade.any
  rw [hm]
  change (List.map flag _).foldl _ (flag false) = _
  rw [fold_flags,fold_or]
  simp only [Bool.false_or,List.any_map,Function.comp_def,id_eq]

#print axioms eq_flag
#print axioms member_flag
end ChatResponseReference.Utf8
