import TlsMpc.Signal.Unpad

/-! Shared CBC opening result: acceptance byte, eight-byte big-endian retained
length, then a fixed-size plaintext buffer. Every byte is zero on rejection.
The final-block decoder is the existing strictly checked PKCS7 circuit.
No secret controls a branch, loop bound or index. -/

namespace TlsMpc.Signal.OpenResult
open Std.Tactic.BVDecide

def get (o : ByteAuth.Ops B) (bytes : List B) (index : Nat) : B :=
  bytes[index]?.getD (o.const 0)

def encodeLength (o : ByteAuth.Ops B) (n : Nat) : List B :=
  (List.range 8).map (fun i => o.const (n / 256 ^ (7 - i) % 256))

def lengthCases (o : ByteAuth.Ops B) (leading : Nat) (tail : B) : List Nat → List B
  | [] => List.replicate 8 (o.const 0)
  | n :: ns => Unpad.choose o (ByteAuth.eqMask o tail (o.const n))
      (encodeLength o (leading + n)) (lengthCases o leading tail ns)

def lengthBytes (o : ByteAuth.Ops B) (leading : Nat) (tail : B) : List B :=
  lengthCases o leading tail (List.range 16)

def candidatePayload (o : ByteAuth.Ops B) (leading decoded : List B) : List B :=
  lengthBytes o leading.length (get o decoded 1) ++ leading ++ decoded.drop 2

def finish (o : ByteAuth.Ops B) (authenticated : B) (candidate : List B) : List B :=
  let leading := candidate.take (candidate.length - 16)
  let decoded := Unpad.decode o (candidate.drop (candidate.length - 16))
  let accepted := o.and authenticated (get o decoded 0)
  accepted :: ByteAuth.release o accepted (candidatePayload o leading decoded)

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem get_map (bytes : List B) (index : Nat) :
    f (get a bytes index) = get b (bytes.map f) index := by
  simp [get, ← h.const 0]

theorem encodeLength_map (n : Nat) :
    (encodeLength a n).map f = encodeLength b n := by
  simp [encodeLength, h.const]

theorem lengthCases_map (leading : Nat) (tail : B) (counts : List Nat) :
    (lengthCases a leading tail counts).map f = lengthCases b leading (f tail) counts := by
  induction counts with
  | nil => simp [lengthCases, h.const]
  | cons n ns ih =>
    simp only [lengthCases, Unpad.choose_map h, ByteAuth.eqMask_map h, h.const,
      encodeLength_map h, ih]

theorem lengthBytes_map (leading : Nat) (tail : B) :
    (lengthBytes a leading tail).map f = lengthBytes b leading (f tail) :=
  lengthCases_map h _ _ _

theorem candidatePayload_map (leading decoded : List B) :
    (candidatePayload a leading decoded).map f =
      candidatePayload b (leading.map f) (decoded.map f) := by
  simp only [candidatePayload, List.map_append, lengthBytes_map h, get_map h,
    List.length_map, List.map_drop]

theorem finish_map (authenticated : B) (candidate : List B) :
    (finish a authenticated candidate).map f = finish b (f authenticated) (candidate.map f) := by
  simp only [finish, List.map_cons, h.and, get_map h, Unpad.decode_map h,
    List.map_drop, List.length_map, ByteAuth.release_map h, candidatePayload_map h,
    List.map_take]

end Refinement

theorem encodeLength_length (o : ByteAuth.Ops B) (n : Nat) :
    (encodeLength o n).length = 8 := by simp [encodeLength]

theorem lengthCases_length (o : ByteAuth.Ops B) (leading : Nat) (tail : B) (counts : List Nat) :
    (lengthCases o leading tail counts).length = 8 := by
  induction counts with
  | nil => simp [lengthCases]
  | cons n ns ih => simp [lengthCases, Unpad.choose, encodeLength_length, ih]

theorem lengthBytes_length (o : ByteAuth.Ops B) (leading : Nat) (tail : B) :
    (lengthBytes o leading tail).length = 8 := lengthCases_length _ _ _ _

theorem finish_length (o : ByteAuth.Ops B) (authenticated : B) (candidate : List B)
    (hlen : 16 ≤ candidate.length) : (finish o authenticated candidate).length = 9 + candidate.length := by
  have ht : (candidate.drop (candidate.length - 16)).length = 16 := by simp; omega
  have hd : (Unpad.decode o (candidate.drop (candidate.length - 16))).length = 18 := by
    apply Unpad.decodeCases_length _ _ ht
    intro n hn
    rcases List.mem_map.mp hn with ⟨i, hi, hn⟩
    simp only [List.mem_range] at hi
    omega
  simp only [finish, ByteAuth.release, List.length_cons, List.length_map,
    candidatePayload, List.length_append, lengthBytes_length, List.length_take,
    List.length_drop, hd]
  omega

theorem finish_reject_auth (candidate : List (BitVec 8)) (hlen : 16 ≤ candidate.length) :
    finish ByteAuth.concrete 0 candidate = List.replicate (9 + candidate.length) 0 := by
  have hs := finish_length ByteAuth.concrete 0 candidate hlen
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [finish, hz, ByteAuth.release_reject] at hs ⊢
  simp only [List.length_cons, List.length_replicate] at hs
  rw [← hs, List.replicate_succ]

theorem finish_reject_padding (authenticated : BitVec 8) (candidate : List (BitVec 8))
    (hlen : 16 ≤ candidate.length)
    (bad : get ByteAuth.concrete
      (Unpad.decode ByteAuth.concrete (candidate.drop (candidate.length - 16))) 0 = 0) :
    finish ByteAuth.concrete authenticated candidate = List.replicate (9 + candidate.length) 0 := by
  have hzero : finish ByteAuth.concrete authenticated candidate = finish ByteAuth.concrete 0 candidate := by
    have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
    simp only [finish, bad, hz]
  rw [hzero, finish_reject_auth candidate hlen]

theorem lengthCases_value (leading retained : Nat) (counts : List Nat)
    (hr : retained < 16) (hm : retained ∈ counts) (hb : ∀ n ∈ counts, n < 16) :
    lengthCases ByteAuth.concrete leading (BitVec.ofNat 8 retained) counts =
      encodeLength ByteAuth.concrete (leading + retained) := by
  induction counts with
  | nil => simp at hm
  | cons n ns ih =>
    have heq : (BitVec.ofNat 8 retained = BitVec.ofNat 8 n) ↔ retained = n := by
      constructor
      · intro h
        have ht := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : retained < 2^8),
          Nat.mod_eq_of_lt (by have := hb n (by simp); omega : n < 2^8)] using ht
      · intro h; rw [h]
    change Unpad.choose ByteAuth.concrete
      (ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 retained) (BitVec.ofNat 8 n))
      (encodeLength ByteAuth.concrete (leading + n)) _ = _
    simp only [ByteAuth.eqMask_value, heq]
    by_cases hn : retained = n
    · rw [if_pos hn, Unpad.choose_accept _ _ (by
        rw [encodeLength_length, lengthCases_length]), ← hn]
    · rw [if_neg hn, Unpad.choose_reject _ _ (by
        rw [encodeLength_length, lengthCases_length])]
      apply ih
      · simpa only [List.mem_cons, hn, false_or] using hm
      · intro k hk; exact hb k (by simp [hk])

theorem lengthBytes_value (leading retained : Nat) (hr : retained < 16) :
    lengthBytes ByteAuth.concrete leading (BitVec.ofNat 8 retained) =
      encodeLength ByteAuth.concrete (leading + retained) := by
  exact lengthCases_value _ _ _ hr (by simpa) (by simpa)

theorem compiled_finish_correct (authenticated : BVExpr 8) (candidate : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (finish ByteAuth.symbolic authenticated candidate).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (finish ByteAuth.symbolic authenticated candidate))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (finish ByteAuth.symbolic authenticated candidate))).vec.get index hi)) =
      (ByteCircuit.joinValue (finish ByteAuth.concrete (authenticated.eval assign)
        (candidate.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, finish_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.OpenResult
