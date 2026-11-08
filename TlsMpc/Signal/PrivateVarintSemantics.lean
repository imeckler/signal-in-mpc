import TlsMpc.Signal.PrivateVarint
import TlsMpc.Signal.PrivateBufferWireSemantics

namespace TlsMpc.Signal.PrivateVarint
open PrivateBuffer

theorem active_value (groups : List (BitVec 8)) (i : Nat) :
    active ByteAuth.concrete groups i =
      if i=0 ∨ groups.drop i≠List.replicate (groups.length-i) 0 then 255 else 0 := by
  unfold active
  rw [ByteAuth.equalMask_value]
  by_cases hi : i=0
  · simp [hi,ByteAuth.concrete]
  · simp only [hi,false_or]
    change (~~~(if groups.drop i=List.replicate (groups.length-i) 0 then (255 : BitVec 8) else 0))=_
    split <;> simp_all

theorem active_canonical (groups : List (BitVec 8)) (width : Nat)
    (hw : 0<width) (hl : width≤groups.length)
    (hz : groups.drop width=List.replicate (groups.length-width) 0)
    (ht : width=1 ∨ groups[width-1]?.getD 0≠0) (i : Nat) :
    active ByteAuth.concrete groups i = if i<width then 255 else 0 := by
  rw [active_value]
  by_cases hi : i=0
  · simp [hi,hw]
  by_cases bound : i<width
  · have nonzero : groups.drop i≠List.replicate (groups.length-i) 0 := by
      intro he
      have ht' : groups[width-1]?.getD 0≠0 := by rcases ht with h|h;omega;exact h
      have atIndex := congrArg (fun xs : List (BitVec 8) => xs[width-1-i]?.getD 0) he
      rw [List.getElem?_drop] at atIndex
      have pos : i+(width-1-i)=width-1 := by omega
      have b : width-1-i<groups.length-i := by omega
      simp only [pos,List.getElem?_replicate,if_pos b,Option.getD_some] at atIndex
      exact ht' atIndex
    simp only [hi,false_or,if_pos bound]
    rw [if_pos nonzero]
  · have zero : groups.drop i=List.replicate (groups.length-i) 0 := by
      calc
        groups.drop i=(groups.drop width).drop (i-width) := by rw [List.drop_drop];congr 1;omega
        _=(List.replicate (groups.length-width) 0).drop (i-width) := by rw [hz]
        _=_ := by rw [List.drop_replicate];congr 1;omega
    simp [hi,bound,zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem increment_small (n : Fin 11) (b : Bool) :
    (addLoop ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
      ((if b then 255 else 0)::List.replicate 15 0) (List.range 16) 0).1 =
      publicLength ByteAuth.concrete (n.val+b.toNat) := by
  have all : ∀ n : Fin 11, ∀ b : Bool,
    (addLoop ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
      ((if b then 255 else 0)::List.replicate 15 0) (List.range 16) 0).1 =
      publicLength ByteAuth.concrete (n.val+b.toNat) := by decide +kernel
  exact all n b

theorem countLoop_value (groups : List (BitVec 8)) (width : Nat)
    (ha : ∀ i, active ByteAuth.concrete groups i=if i<width then 255 else 0)
    (is : List Nat) (n : Nat) (hb : n+is.length≤10) :
    countLoop ByteAuth.concrete groups is (publicLength ByteAuth.concrete n) =
      publicLength ByteAuth.concrete (n+(is.filter (fun i => i<width)).length) := by
  induction is generalizing n with
  | nil => simp [countLoop]
  | cons i is ih =>
    rw [countLoop,ha i]
    by_cases hi : i<width
    · rw [if_pos hi]
      have inc := increment_small ⟨n,by simp only [List.length_cons] at hb;omega⟩ true
      simp only [Bool.toNat_true,if_true] at inc
      rw [show (ByteAuth.concrete.const 0 : BitVec 8)=0 from rfl,inc]
      rw [ih (n+1) (by simp only [List.length_cons] at hb;omega)]
      simp [hi,Nat.add_assoc,Nat.add_comm]
    · rw [if_neg hi]
      have inc := increment_small ⟨n,by simp only [List.length_cons] at hb;omega⟩ false
      simp only [Bool.toNat_false,Nat.add_zero,Bool.false_eq_true,if_false] at inc
      rw [show (ByteAuth.concrete.const 0 : BitVec 8)=0 from rfl,inc]
      rw [ih n (by simp only [List.length_cons] at hb;omega)]
      simp [hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem filtered_range_length (capacity width : Fin 11) (h : width.val≤capacity.val) :
    ((List.range capacity.val).filter (fun i => i<width.val)).length=width.val := by
  have all : ∀ c w : Fin 11, w.val≤c.val →
      ((List.range c.val).filter (fun i => i<w.val)).length=w.val := by decide +kernel
  exact all capacity width h

theorem canonical_length_bits (groups : List (BitVec 8)) (width : Nat)
    (hw : 0<width) (hl : width≤groups.length) (hc : groups.length≤10)
    (hz : groups.drop width=List.replicate (groups.length-width) 0)
    (ht : width=1 ∨ groups[width-1]?.getD 0≠0) :
    countLoop ByteAuth.concrete groups (List.range groups.length) (publicLength ByteAuth.concrete 0) =
      publicLength ByteAuth.concrete width := by
  rw [countLoop_value groups width (active_canonical groups width hw hl hz ht) _ 0 (by simpa)]
  simp only [Nat.zero_add]
  rw [filtered_range_length ⟨groups.length,by omega⟩ ⟨width,by omega⟩ hl]

def canonicalData (groups : List (BitVec 8)) (width : Nat) : List (BitVec 8) :=
  (List.range groups.length).map (fun i => if i<width then
    OpenResult.get ByteAuth.concrete groups i ^^^ (if i+1<width then 128 else 0) else 0)

theorem canonical_raw_data (groups : List (BitVec 8)) (width : Nat)
    (hw : 0<width) (hl : width≤groups.length)
    (hz : groups.drop width=List.replicate (groups.length-width) 0)
    (ht : width=1 ∨ groups[width-1]?.getD 0≠0) :
    (List.range groups.length).map (fun i =>
      ByteAuth.concrete.and (active ByteAuth.concrete groups i)
        (ByteAuth.concrete.xor (OpenResult.get ByteAuth.concrete groups i)
          (if i+1<groups.length then ByteAuth.concrete.and (active ByteAuth.concrete groups (i+1))
            (ByteAuth.concrete.const 128) else ByteAuth.concrete.const 0))) = canonicalData groups width := by
  unfold canonicalData
  apply List.map_congr_left
  intro i hi
  rw [active_canonical groups width hw hl hz ht i]
  by_cases bound : i<width
  · rw [if_pos bound]
    have inner : (if i+1<groups.length then ByteAuth.concrete.and
        (active ByteAuth.concrete groups (i+1)) (ByteAuth.concrete.const 128)
        else ByteAuth.concrete.const 0) = (if i+1<width then (128 : BitVec 8) else 0) := by
      rw [active_canonical groups width hw hl hz ht (i+1)]
      by_cases h : i+1<width
      · simp [h,show i+1<groups.length from by omega,ByteAuth.concrete]
      · rw [if_neg h];split <;> rfl
    rw [inner]
    change (255 : BitVec 8) &&& _ = _
    rw [PrivateBuffer.and_full_literal]
    simp only [if_pos bound,ByteAuth.concrete]
  · rw [if_neg bound]
    change (0 : BitVec 8) &&& _ = _
    simp [bound]

theorem canonical_data_prefix (groups : List (BitVec 8)) (width : Nat) :
    PrivateBuffer.prefixData ByteAuth.concrete groups.length width (canonicalData groups width) =
      canonicalData groups width := by
  unfold PrivateBuffer.prefixData canonicalData
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  by_cases h : i<width <;> simp [OpenResult.get,bound,h,ByteAuth.concrete]

theorem fromGroups_canonical (groups : List (BitVec 8)) (width : Nat)
    (hw : 0<width) (hl : width≤groups.length) (hc : groups.length≤10)
    (hz : groups.drop width=List.replicate (groups.length-width) 0)
    (ht : width=1 ∨ groups[width-1]?.getD 0≠0) :
    fromGroups ByteAuth.concrete groups =
      ⟨255,publicLength ByteAuth.concrete width,canonicalData groups width⟩ := by
  unfold fromGroups
  rw [canonical_length_bits groups width hw hl hc hz ht,canonical_raw_data groups width hw hl hz ht]
  have result := PrivateBuffer.make_decoded groups.length (by omega)
    (BitVec.ofNat 8 (width/256)) (BitVec.ofNat 8 width) (canonicalData groups width)
    (by simp [canonicalData])
  rw [PrivateBuffer.public_length_value width (by omega),if_pos hl,canonical_data_prefix] at result
  exact result

theorem canonical_data_bytes (groups : List (BitVec 8)) (width : Nat) (hl : width≤groups.length) :
    canonicalData groups width = Varint.encodeGroups ByteAuth.concrete groups width ++
      List.replicate (groups.length-width) 0 := by
  unfold canonicalData
  have len : groups.length=width+(groups.length-width) := by omega
  rw [len,List.range_add,List.map_append,List.map_map]
  have left : (List.range width).map (fun i => if i<width then
      OpenResult.get ByteAuth.concrete groups i ^^^ (if i+1<width then 128 else 0) else 0) =
      Varint.encodeGroups ByteAuth.concrete groups width := by
    unfold Varint.encodeGroups
    apply List.map_congr_left
    intro i hi
    simp only [if_pos (List.mem_range.mp hi),ByteAuth.concrete]
    split <;> rfl
  have right : (List.range (groups.length-width)).map (fun i => if width+i<width then
      OpenResult.get ByteAuth.concrete groups (width+i) ^^^ (if width+i+1<width then 128 else 0) else 0) =
      List.replicate (groups.length-width) 0 := by
    have eq : (fun i : Nat => if width+i<width then
        OpenResult.get ByteAuth.concrete groups (width+i) ^^^ (if width+i+1<width then 128 else 0) else 0) =
        (fun _ : Nat => (0 : BitVec 8)) := by funext i;rw [if_neg (by omega)]
    rw [eq,List.map_const',List.length_range]
  rw [left]
  simpa only [Function.comp_def,Nat.add_sub_cancel_left] using
    congrArg (fun xs => Varint.encodeGroups ByteAuth.concrete groups width ++ xs) right

theorem fromGroups_wire (groups : List (BitVec 8)) (width : Nat)
    (hw : 0<width) (hl : width≤groups.length) (hc : groups.length≤10)
    (hz : groups.drop width=List.replicate (groups.length-width) 0)
    (ht : width=1 ∨ groups[width-1]?.getD 0≠0) :
    PrivateBuffer.output ByteAuth.concrete (fromGroups ByteAuth.concrete groups) =
      255 :: (BitVec.ofNat 8 (width/256) :: BitVec.ofNat 8 width ::
        (Varint.encodeGroups ByteAuth.concrete groups width ++ List.replicate (groups.length-width) 0)) := by
  rw [fromGroups_canonical groups width hw hl hc hz ht]
  unfold PrivateBuffer.output
  rw [canonical_data_bytes groups width hl]
  have enc : PrivateBuffer.encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete width) =
      [BitVec.ofNat 8 (width/256),BitVec.ofNat 8 width] :=
    PrivateBuffer.length_roundtrip _ _
  rw [enc]
  rfl

theorem uint32_wire (word : BitVec 32) (width : Nat) (hw : 0<width) (hl : width≤5)
    (canonical : Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete word) width) :
    PrivateBuffer.output ByteAuth.concrete (uint32 Sha256.concrete ByteAuth.concrete word) =
      255 :: (BitVec.ofNat 8 (width/256) :: BitVec.ofNat 8 width ::
        (Varint.encode Sha256.concrete ByteAuth.concrete word width ++ List.replicate (5-width) 0)) := by
  have len : (Varint.groups Sha256.concrete ByteAuth.concrete word).length=5 := by simp [Varint.groups]
  apply fromGroups_wire _ width hw (by omega) (by omega)
  · simpa only [len] using canonical.1
  · rcases canonical.2 with h|h
    · exact Or.inl h
    · right
      have geteq : OpenResult.get ByteAuth.concrete (Varint.groups Sha256.concrete ByteAuth.concrete word) (width-1) =
          (Varint.groups Sha256.concrete ByteAuth.concrete word)[width-1]?.getD 0 := by
        cases he : (Varint.groups Sha256.concrete ByteAuth.concrete word)[width-1]? <;>
          simp only [OpenResult.get,he,Option.getD_none,Option.getD_some] <;> rfl
      rw [geteq] at h
      exact h

theorem uint64_wire (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    PrivateBuffer.output ByteAuth.concrete (uint64 Varint64.concrete ByteAuth.concrete word) =
      255 :: (BitVec.ofNat 8 (width/256) :: BitVec.ofNat 8 width ::
        (Varint64.encode Varint64.concrete ByteAuth.concrete word width ++ List.replicate (10-width) 0)) := by
  have len : (Varint64.groups Varint64.concrete word).length=10 := by simp [Varint64.groups]
  apply fromGroups_wire _ width hw (by omega) (by omega)
  · simpa only [len] using canonical.1
  · rcases canonical.2 with h|h
    · exact Or.inl h
    · right
      have geteq : OpenResult.get ByteAuth.concrete (Varint64.groups Varint64.concrete word) (width-1) =
          (Varint64.groups Varint64.concrete word)[width-1]?.getD 0 := by
        cases he : (Varint64.groups Varint64.concrete word)[width-1]? <;>
          simp only [OpenResult.get,he,Option.getD_none,Option.getD_some] <;> rfl
      rw [geteq] at h
      exact h

end TlsMpc.Signal.PrivateVarint
