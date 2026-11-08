import TlsMpc.Signal.PrivateMessageMac
import TlsMpc.Signal.PrivateBufferRecordSemantics

namespace TlsMpc.Signal.PrivateMessageMac
open PrivateBuffer
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem remove_eight_arithmetic (n : Fin 257) (h : 9≤n.val) :
    let removed := addLoop ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
      (publicLength ByteAuth.concrete 65528) (List.range 16) 0
    removed.1=publicLength ByteAuth.concrete (n.val-8) ∧
      (255 : BitVec 8) &&& (removed.2 &&& ~~~less ByteAuth.concrete
        (publicLength ByteAuth.concrete n.val) (publicLength ByteAuth.concrete 9))=255 := by
  let left := Semantics.byteBits (BitVec.ofNat 8 n.val) ++ Semantics.byteBits (BitVec.ofNat 8 (n.val/256))
  let right := Semantics.byteBits (248 : BitVec 8) ++ Semantics.byteBits (255 : BitVec 8)
  let pairs := (List.range 16).map (fun i => (left[i]?.getD false,right[i]?.getD false))
  let result := Semantics.add pairs false
  have rep : addLoop ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
      (publicLength ByteAuth.concrete 65528) (List.range 16) 0 =
      (result.1.map Semantics.mask,Semantics.mask result.2) := by
    unfold publicLength
    rw [Semantics.decodeLength_masks,Semantics.decodeLength_masks]
    exact Semantics.addLoop_masks left right (List.range 16) false
  have length : result.1.length=16 := by simp [result,pairs,add_length]
  have equation:=Semantics.add_decoded_integer (BitVec.ofNat 8 (n.val/256)) (BitVec.ofNat 8 n.val) 255 248
  change Semantics.value ((addLoop ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
      (publicLength ByteAuth.concrete 65528) (List.range 16) 0).1.map Semantics.unmask)+
      65536*(Semantics.unmask (addLoop ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
      (publicLength ByteAuth.concrete 65528) (List.range 16) 0).2).toNat =
      ((BitVec.ofNat 8 (n.val/256))++BitVec.ofNat 8 n.val).toNat+65528 at equation
  rw [rep,public_length_value n.val (by omega)] at equation
  simp only [List.map_map,Function.comp_def,Semantics.unmask_mask,List.map_id'] at equation
  have bound:=Semantics.value_lt_pow result.1
  rw [length] at bound
  have carry : result.2=true := by
    cases hc : result.2
    · simp only [hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at equation
      omega
    · rfl
  have value : Semantics.value result.1=n.val-8 := by rw [carry] at equation;simp only [Bool.toNat_true] at equation;omega
  let target:=Semantics.byteBits (BitVec.ofNat 8 (n.val-8))++Semantics.byteBits (BitVec.ofNat 8 ((n.val-8)/256))
  have bits : result.1=target := by
    apply bits_value_injective
    · simp [target,Semantics.byteBits,length]
    · rw [value,Semantics.bytePair_value,public_length_value (n.val-8) (by omega)]
  have encoded : result.1.map Semantics.mask=publicLength ByteAuth.concrete (n.val-8) := by
    unfold publicLength
    rw [Semantics.decodeLength_masks]
    change result.1.map Semantics.mask=target.map Semantics.mask
    exact congrArg (List.map Semantics.mask) bits
  have hless : less ByteAuth.concrete (publicLength ByteAuth.concrete n.val) (publicLength ByteAuth.concrete 9)=0 := by
    unfold publicLength
    rw [Semantics.less_decoded_integer]
    change (if ((BitVec.ofNat 8 (n.val/256))++BitVec.ofNat 8 n.val).toNat<
      ((BitVec.ofNat 8 (9/256))++BitVec.ofNat 8 9).toNat then (255 : BitVec 8) else 0)=0
    rw [public_length_value n.val (by omega),public_length_value 9 (by decide),if_neg (by omega)]
  dsimp only
  rw [rep]
  change result.1.map Semantics.mask=publicLength ByteAuth.concrete (n.val-8) ∧
    (255 : BitVec 8) &&& (Semantics.mask result.2 &&& ~~~less ByteAuth.concrete
      (publicLength ByteAuth.concrete n.val) (publicLength ByteAuth.concrete 9))=255
  exact ⟨encoded,by rw [carry,hless];decide⟩

theorem prefixData_take (capacity count : Nat) (raw : List (BitVec 8))
    (hcount : count≤raw.length) (fit : count≤capacity) :
    prefixData ByteAuth.concrete capacity count raw=
      (ofContents capacity (raw.take count)).data := by
  have len : (raw.take count).length=count := by simp [Nat.min_eq_left hcount]
  calc
    _=prefixData ByteAuth.concrete capacity count (raw.take count++raw.drop count) := by
      rw [List.take_append_drop]
    _=prefixData ByteAuth.concrete capacity (raw.take count).length (raw.take count++raw.drop count) := by rw [len]
    _=prefixData ByteAuth.concrete capacity (raw.take count).length (raw.take count) :=
      prefix_append_tail capacity (raw.take count) (raw.drop count)
    _=_ := by rw [prefix_contents capacity _ (by omega)];rfl

theorem contentBuffer_contents (wire : List (BitVec 8)) (fit : wire.length≤256) (minimum : 9≤wire.length) :
    contentBuffer ByteAuth.concrete (ofContents 256 wire)=ofContents 256 (wire.take (wire.length-8)) := by
  have ar:=remove_eight_arithmetic ⟨wire.length,by omega⟩ minimum
  have len : (ofContents 256 wire).data.length=256 := by
    simp only [ofContents,List.length_append,List.length_replicate];omega
  unfold contentBuffer
  change PrivateProtobuf.gate ByteAuth.concrete
    ((255 : BitVec 8) &&& ((addLoop ByteAuth.concrete (publicLength ByteAuth.concrete wire.length)
      (publicLength ByteAuth.concrete 65528) (List.range 16) 0).2 &&&
      ~~~less ByteAuth.concrete (publicLength ByteAuth.concrete wire.length) (publicLength ByteAuth.concrete 9)))
    (make ByteAuth.concrete (ofContents 256 wire).data.length
      (addLoop ByteAuth.concrete (publicLength ByteAuth.concrete wire.length)
        (publicLength ByteAuth.concrete 65528) (List.range 16) 0).1 (ofContents 256 wire).data)=_
  rw [ar.1,ar.2,len]
  have made:=make_decoded 256 (by decide) (BitVec.ofNat 8 ((wire.length-8)/256))
    (BitVec.ofNat 8 (wire.length-8)) (ofContents 256 wire).data len
  rw [public_length_value (wire.length-8) (by omega),if_pos (by omega)] at made
  change make ByteAuth.concrete 256 (publicLength ByteAuth.concrete (wire.length-8))
    (ofContents 256 wire).data=_ at made
  rw [made]
  have data : prefixData ByteAuth.concrete 256 (wire.length-8) (ofContents 256 wire).data=
      (ofContents 256 (wire.take (wire.length-8))).data := by
    have take : (ofContents 256 wire).data.take (wire.length-8)=wire.take (wire.length-8) := by
      change (wire++List.replicate (256-wire.length) 0).take (wire.length-8)=_
      exact List.take_append_of_le_length (by omega)
    have result:=prefixData_take 256 (wire.length-8) (ofContents 256 wire).data
      (by rw [len];omega) (by omega)
    rw [take] at result
    exact result
  rw [data]
  unfold PrivateProtobuf.gate
  have mask : (255 : BitVec 8) &&& ByteAuth.eqMask ByteAuth.concrete 255 255=255 := by decide
  change finish ByteAuth.concrete ((255 : BitVec 8) &&& ByteAuth.eqMask ByteAuth.concrete 255 255)
    (publicLength ByteAuth.concrete (wire.length-8)) (ofContents 256 (wire.take (wire.length-8))).data=_
  rw [mask,finish_accept]
  simp only [ofContents,List.length_take,Nat.min_eq_left (show wire.length-8≤wire.length by omega)]
end TlsMpc.Signal.PrivateMessageMac
