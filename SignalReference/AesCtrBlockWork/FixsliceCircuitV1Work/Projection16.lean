import AesCtrBlockWork.FixsliceCircuitV1Work.Core
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def project (block : Fin 4) (word : BitVec 64) : BitVec 16 :=
 BitVec.ofFn (fun i=>word.getLsbD (4*i.val+block.val))

@[simp] theorem project_bit (block : Fin 4) (word : BitVec 64) (i : Nat) (hi : i<16) :
 (project block word).getLsbD i=word.getLsbD (4*i+block.val) := by
 rw [BitVec.getLsbD_eq_getElem hi]
 simp only [project,BitVec.getElem_ofFn]

theorem project_get (block : Fin 4) (word : BitVec 64) (i : Nat) :
 (project block word).getLsbD i=if i<16 then word.getLsbD (4*i+block.val) else false := by
 by_cases hi:i<16
 · simp only [hi,if_pos,project_bit]
 · rw [if_neg hi]
   exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem project_zero (block : Fin 4) : project block 0=0 := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 rw [project_bit _ _ _ hi]
 change (0#64).getLsbD (4*i+block.val)=(0#16).getLsbD i
 simp only [BitVec.getLsbD_zero]

theorem project_xor (block : Fin 4) (x y : BitVec 64) :
 project block (x^^^y)=project block x ^^^ project block y := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [BitVec.getLsbD_xor,project_bit _ _ _ hi]

theorem project_and (block : Fin 4) (x y : BitVec 64) :
 project block (x&&&y)=project block x &&& project block y := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [BitVec.getLsbD_and,project_bit _ _ _ hi]

theorem project_or (block : Fin 4) (x y : BitVec 64) :
 project block (x|||y)=project block x ||| project block y := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [BitVec.getLsbD_or,project_bit _ _ _ hi]

theorem project_not (block : Fin 4) (x : BitVec 64) :
 project block (~~~x) = ~~~project block x := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 have h64 : 4*i+block.val<64 := by omega
 simp only [project_bit _ _ _ hi,BitVec.getLsbD_not,hi,h64,decide_true,Bool.true_and]

theorem project_right4 (block : Fin 4) (x : BitVec 64) (n : Fin 16) :
 project block (x >>> (4*n.val))=project block x >>> n.val := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 rw [project_bit _ _ _ hi]
 simp only [BitVec.getLsbD_ushiftRight,project_get]
 by_cases hn:n.val+i<16
 · rw [if_pos hn]
   congr 1
   omega
 · rw [if_neg hn]
   exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem project_left4 (block : Fin 4) (x : BitVec 64) (n : Fin 16) :
 project block (x <<< (4*n.val))=project block x <<< n.val := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 have h64 : 4*i+block.val<64 := by omega
 rw [project_bit _ _ _ hi]
 by_cases hn : n.val ≤ i
 · have hn4 : ¬4*i+block.val<4*n.val := by omega
   have hni : ¬i<n.val := by omega
   have hid : i-n.val<16 := by omega
   simp only [BitVec.getLsbD_shiftLeft,h64,hi,hn4,hni,decide_true,decide_false,Bool.not_false,Bool.true_and,project_bit _ _ _ hid]
   congr 1
   omega
 · have hn4 : 4*i+block.val<4*n.val := by omega
   have hni : i<n.val := by omega
   simp only [BitVec.getLsbD_shiftLeft,h64,hi,hn4,hni,decide_true,Bool.not_true,Bool.true_and,Bool.false_and]

theorem project_rotate4 (block : Fin 4) (x : BitVec 64) (n : Fin 16) :
 project block (x.rotateRight (4*n.val))=(project block x).rotateRight n.val := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 have hn64 : 4*n.val<64 := by omega
 rw [project_bit _ _ _ hi]
 simp only [BitVec.getLsbD_rotateRight,Nat.mod_eq_of_lt hn64,Nat.mod_eq_of_lt n.isLt]
 by_cases hn : i<16-n.val
 · have hn4 : 4*i+block.val<64-4*n.val := by omega
   have hni : n.val+i<16 := by omega
   simp only [hn,hn4,decide_true,cond_true,project_bit _ _ _ hni]
   congr 1
   omega
 · have hn4 : ¬4*i+block.val<64-4*n.val := by omega
   have hni : i-(16-n.val)<16 := by omega
   have hi64 : 4*i+block.val<64 := by omega
   simp only [hn,hn4,hi,hi64,decide_false,decide_true,cond_false,Bool.true_and,project_bit _ _ _ hni]
   congr 1
   omega

def concrete16 (block : Fin 4) : Ops (BitVec 16) where
 bits := ⟨0,(· ^^^ ·),(· &&& ·),(~~~ ·)⟩
 mask x m := x &&& project block m
 bor := (· ||| ·)
 rotate4 x n := x.rotateRight n.val
 left4 x n := x <<< n.val
 right4 x n := x >>> n.val

theorem projectionHom (block : Fin 4) : Hom concrete64 (concrete16 block) (project block) := by
 constructor
 · constructor
   · exact project_zero block
   · exact project_xor block
   · exact project_and block
   · exact project_not block
 · exact project_and block
 · exact project_or block
 · exact project_rotate4 block
 · exact project_left4 block
 · exact project_right4 block

theorem projected_encrypt (block : Fin 4) (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 mapWords (project block) (encrypt concrete64 keys words)=
 encrypt (concrete16 block) (fun i=>mapWords (project block) (keys i)) (mapWords (project block) words) :=
 encrypt_map (projectionHom block) keys words
end LibSignalReference.Candidate.FixsliceCircuitV1
