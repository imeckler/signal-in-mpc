import TlsMpc.TlsRecord
import TlsMpc.TlsInner

/-! Fixed-capacity TLS 1.3 application sealing with a shared actual length.
The validity byte is computed by the private producer and is never discarded.
Only capacity is public. The native release boundary must authenticate/open
status first and abort without releasing wire bytes when status is not255. -/
namespace TlsMpc.TlsPrivateSeal
open Std.Tactic.BVDecide

def lengthValue (high low : BitVec 8) : Nat := 256*high.toNat+low.toNat

def eqLength (a : ByteAuth.Ops B) (high low : B) (n : Nat) : B :=
  a.and (ByteAuth.eqMask a high (a.const (n/256))) (ByteAuth.eqMask a low (a.const n))

def orMask (a : ByteAuth.Ops B) (x y : B) : B := a.not (a.and (a.not x) (a.not y))

structure Built (B : Type) where
  valid : B
  bytes : List B

def Built.map (f : B → B') (r : Built B) : Built B' := ⟨f r.valid,r.bytes.map f⟩

-- The suffix scan inspects only public positions. A matched private length
-- inserts type23; positions before it retain data, positions after it are zero.
def build (a : ByteAuth.Ops B) (high low : B) : Nat → List B → Built B
  | offset, [] =>
      let marker := eqLength a high low offset
      ⟨marker,[a.and marker (a.const 23)]⟩
  | offset, byte::rest =>
      let tail := build a high low (offset+1) rest
      let marker := eqLength a high low offset
      ⟨orMask a marker tail.valid,
        TlsInner.select a tail.valid byte (a.and marker (a.const 23)) :: tail.bytes⟩

def sealCore (g : Gcm.Ops B W) (a : ByteAuth.Ops B) (key iv sequence : List B)
    (valid high low : B) (data : List B) : List B :=
  let built := build a high low 0 data
  let accepted := a.and (ByteAuth.eqMask a valid (a.const 255)) built.valid
  let aad := TlsRecord.header g (data.length+17)
  accepted :: (aad ++ (Gcm.sealCore g key (TlsRecord.nonce g iv sequence) aad built.bytes).bytes)

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem eqLength_map (high low : B) (n : Nat) :
    f (eqLength a high low n) = eqLength b (f high) (f low) n := by
  simp [eqLength,h.and,ByteAuth.eqMask_map h,h.const]

theorem orMask_map (x y : B) : f (orMask a x y) = orMask b (f x) (f y) := by
  simp [orMask,h.not,h.and]

theorem build_map (high low : B) (offset : Nat) (data : List B) :
    (build a high low offset data).map f = build b (f high) (f low) offset (data.map f) := by
  induction data generalizing offset with
  | nil => simp [build,Built.map,eqLength_map h,h.and,h.const]
  | cons byte rest ih =>
      have hv := congrArg Built.valid (ih (offset+1))
      have hb := congrArg Built.bytes (ih (offset+1))
      simp only [Built.map] at hv hb
      simp [build,Built.map,orMask_map h,eqLength_map h,TlsInner.select_map h,h.and,h.const,hv,hb]

end Refinement

theorem build_length (a : ByteAuth.Ops B) (high low : B) (offset : Nat) (data : List B) :
    (build a high low offset data).bytes.length = data.length+1 := by
  induction data generalizing offset with
  | nil => simp [build]
  | cons byte rest ih => simp [build,ih]

theorem seal_map {g : Gcm.Ops B W} {g' : Gcm.Ops B' W'} {f : B → B'} {fw : W → W'}
    (hg : Gcm.Hom g g' f fw) {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} (ha : ByteAuth.Hom a a' f)
    (key iv sequence : List B) (valid high low : B) (data : List B) :
    (sealCore g a key iv sequence valid high low data).map f =
      sealCore g' a' (key.map f) (iv.map f) (sequence.map f) (f valid) (f high) (f low) (data.map f) := by
  have hv := congrArg Built.valid (build_map ha high low 0 data)
  have hb := congrArg Built.bytes (build_map ha high low 0 data)
  simp only [Built.map] at hv hb
  simp [sealCore,ha.and,ByteAuth.eqMask_map ha,ha.const,hv,hb,
    TlsRecord.header_map hg,TlsRecord.nonce_map hg,Gcm.sealCore_bytes_map hg]

theorem eqLength_value (high low : BitVec 8) (n : Nat) (hn : n < 65536) :
    eqLength ByteAuth.concrete high low n = if lengthValue high low = n then 255 else 0 := by
  have hh : n/256 < 256 := by omega
  have hhi : high.toNat < 256 := high.isLt
  have hlo : low.toNat < 256 := low.isLt
  have highEq : (high = BitVec.ofNat 8 (n/256)) ↔ high.toNat = n/256 := by
    constructor
    · intro h; rw [h]; simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hh]
    · intro h; apply BitVec.eq_of_toNat_eq; simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hh] using h
  have lowEq : (low = BitVec.ofNat 8 n) ↔ low.toNat = n%256 := by
    constructor
    · intro h; rw [h]; simp [BitVec.toNat_ofNat]
    · intro h; apply BitVec.eq_of_toNat_eq; simpa [BitVec.toNat_ofNat] using h
  have together : (high = BitVec.ofNat 8 (n/256) ∧ low = BitVec.ofNat 8 n) ↔ lengthValue high low = n := by
    rw [highEq,lowEq];simp only [lengthValue];omega
  change (ByteAuth.eqMask ByteAuth.concrete high (BitVec.ofNat 8 (n/256)) &&&
    ByteAuth.eqMask ByteAuth.concrete low (BitVec.ofNat 8 n)) = _
  rw [ByteAuth.eqMask_value,ByteAuth.eqMask_value]
  by_cases h1 : high = BitVec.ofNat 8 (n/256) <;>
    by_cases h2 : low = BitVec.ofNat 8 n <;>
    simp_all

def buildSpec (high low : BitVec 8) (offset : Nat) (data : List (BitVec 8)) : Built (BitVec 8) :=
  let length := lengthValue high low
  if offset ≤ length ∧ length ≤ offset+data.length then
    ⟨255,data.take (length-offset) ++ [23] ++ List.replicate (data.length-(length-offset)) 0⟩
  else ⟨0,List.replicate (data.length+1) 0⟩

private theorem or_zero (x : BitVec 8) : orMask ByteAuth.concrete 0 x = x := by
  change ~~~((~~~(0:BitVec 8)) &&& ~~~x) = x
  bv_decide
private theorem or_ones (x : BitVec 8) : orMask ByteAuth.concrete 255 x = 255 := by
  change ~~~((~~~(255:BitVec 8)) &&& ~~~x) = 255
  bv_decide

theorem build_correct (high low : BitVec 8) (offset : Nat) (data : List (BitVec 8))
    (bound : offset+data.length < 65536) :
    build ByteAuth.concrete high low offset data = buildSpec high low offset data := by
  induction data generalizing offset with
  | nil =>
      have ho : offset<65536 := by simpa using bound
      rw [build,eqLength_value high low offset ho]
      by_cases heq : lengthValue high low = offset
      · simp [buildSpec,heq,ByteAuth.concrete]
      · have bad : ¬(offset≤lengthValue high low ∧ lengthValue high low≤offset) := by omega
        simp [buildSpec,heq,bad,ByteAuth.concrete]
  | cons byte rest ih =>
      have ho : offset<65536 := by simp only [List.length_cons] at bound;omega
      have ht : offset+1+rest.length<65536 := by simp only [List.length_cons] at bound;omega
      rw [build,ih (offset+1) ht,eqLength_value high low offset ho]
      by_cases heq : lengthValue high low = offset
      · have tailBad : ¬(offset+1≤lengthValue high low ∧ lengthValue high low≤offset+1+rest.length) := by omega
        have fullGood : offset≤lengthValue high low ∧ lengthValue high low≤offset+(byte::rest).length := by
          simp [heq]
        have tailEq : buildSpec high low (offset+1) rest = ⟨0,List.replicate (rest.length+1) 0⟩ := by
          simp only [buildSpec,if_neg tailBad]
        simp only [tailEq,if_pos heq,or_ones,TlsInner.select_reject]
        simp only [buildSpec,if_pos fullGood]
        simp [heq,ByteAuth.concrete]
      · by_cases inside : offset≤lengthValue high low ∧ lengthValue high low≤offset+(byte::rest).length
        · have tailGood : offset+1≤lengthValue high low ∧ lengthValue high low≤offset+1+rest.length := by
            simp only [List.length_cons] at inside;omega
          have tailEq : buildSpec high low (offset+1) rest =
              ⟨255,rest.take (lengthValue high low-(offset+1)) ++ [23] ++
                List.replicate (rest.length-(lengthValue high low-(offset+1))) 0⟩ := by
            simp only [buildSpec,if_pos tailGood]
          have delta : lengthValue high low-offset = (lengthValue high low-(offset+1))+1 := by omega
          simp only [tailEq,if_neg heq,or_zero,TlsInner.select_accept]
          simp only [buildSpec,if_pos inside]
          simp [delta]
        · have tailBad : ¬(offset+1≤lengthValue high low ∧ lengthValue high low≤offset+1+rest.length) := by
            simp only [List.length_cons] at inside;omega
          have tailEq : buildSpec high low (offset+1) rest = ⟨0,List.replicate (rest.length+1) 0⟩ := by
            simp only [buildSpec,if_neg tailBad]
          simp only [tailEq,if_neg heq,or_zero,TlsInner.select_reject]
          simp only [buildSpec,if_neg inside]
          simp [ByteAuth.concrete,List.replicate_succ]

theorem build_valid (high low : BitVec 8) (data : List (BitVec 8)) (bound : data.length<65536) :
    (build ByteAuth.concrete high low 0 data).valid = if lengthValue high low≤data.length then 255 else 0 := by
  rw [build_correct high low 0 data (by simpa using bound)]
  simp only [buildSpec,Nat.zero_le,Nat.zero_add,true_and]
  split <;> rfl

theorem seal_status (key iv sequence : List (BitVec 8)) (valid high low : BitVec 8)
    (data : List (BitVec 8)) (bound : data.length<65536) :
    (sealCore Gcm.concrete ByteAuth.concrete key iv sequence valid high low data).head? =
      some (if valid=255 ∧ lengthValue high low≤data.length then 255 else 0) := by
  simp only [sealCore,List.head?_cons]
  rw [build_valid high low data bound]
  change some (ByteAuth.eqMask ByteAuth.concrete valid 255 &&& _) = _
  rw [ByteAuth.eqMask_value]
  by_cases hv : valid=255 <;> by_cases hl : lengthValue high low≤data.length <;> simp [hv,hl]
  all_goals bv_decide

theorem seal_valid_record (key iv sequence : List (BitVec 8)) (high low : BitVec 8)
    (data : List (BitVec 8)) (bound : data.length<65536) (within : lengthValue high low≤data.length) :
    sealCore Gcm.concrete ByteAuth.concrete key iv sequence 255 high low data =
      255 :: TlsRecord.sealCore Gcm.concrete key iv sequence
        (data.take (lengthValue high low)) 23 (data.length-lengthValue high low) := by
  have built := build_correct high low 0 data (by simpa using bound)
  simp only [buildSpec,Nat.zero_le,Nat.zero_add,Nat.sub_zero,true_and,if_pos within] at built
  simp only [sealCore,built,ByteAuth.eqMask_value]
  change (255 &&& 255) :: (_ ++ _) = _
  simp only [TlsRecord.sealCore,TlsRecord.inner,Gcm.zeros]
  have arithmetic : lengthValue high low + (data.length-lengthValue high low+1)+16 = data.length+17 := by omega
  simp [arithmetic,Gcm.concrete,Aes.concrete,List.length_take,Nat.min_eq_left within]

theorem compiled_seal_correct (key iv sequence : List (BVExpr 8)) (valid high low : BVExpr 8)
    (data : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(sealCore Gcm.symbolic ByteAuth.symbolic key iv sequence valid high low data).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (sealCore Gcm.symbolic ByteAuth.symbolic key iv sequence valid high low data))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (sealCore Gcm.symbolic ByteAuth.symbolic key iv sequence valid high low data))).vec.get index hi)) =
    (ByteCircuit.joinValue (sealCore Gcm.concrete ByteAuth.concrete
      (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign))
      (valid.eval assign) (high.eval assign) (low.eval assign) (data.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,seal_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.TlsPrivateSeal
