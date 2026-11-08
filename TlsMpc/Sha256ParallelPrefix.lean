import TlsMpc.Sha256CarrySave
import Init.Data.List.Scan.Lemmas
import TlsMpc.Signal.PrivateBufferSemantics

/-! Isolated parallel-prefix final adder; no default changes. -/
namespace TlsMpc.Sha256ParallelPrefix
open Std.Tactic.BVDecide
namespace Prefix

def scan (op : M → M → M) (zero : M) : Nat → List M → List M
  | 0,items => items.scanl op zero
  | fuel+1,items =>
    if items.length≤1 then items.scanl op zero else
      let half := items.length/2
      let left := scan op zero fuel (items.take half)
      let right := scan op zero fuel (items.drop half)
      left ++ right.tail.map (op (left.getLastD zero))

theorem map_left (op : M → M → M) (assoc : ∀ x y z, op (op x y) z=op x (op y z))
    (acc seed : M) (items : List M) :
    (items.scanl op seed).map (op acc)=items.scanl op (op acc seed) := by
  induction items generalizing seed with
  | nil => rfl
  | cons x rest ih => simp only [List.scanl_cons,List.map_cons,ih,assoc]

theorem last_scanl (op : M → M → M) (zero : M) (items : List M) :
    (items.scanl op zero).getLastD zero=items.foldl op zero := by
  simp only [List.getLastD_eq_getLast?,List.getLast?_scanl,Option.getD_some]

theorem scan_correct (op : M → M → M) (zero : M)
    (assoc : ∀ x y z, op (op x y) z=op x (op y z)) (rightId : ∀ x, op x zero=x)
    (fuel : Nat) (items : List M) : scan op zero fuel items=items.scanl op zero := by
  induction fuel generalizing items with
  | zero => rfl
  | succ fuel ih =>
    unfold scan
    split
    · rfl
    · dsimp only
      rw [ih,ih,last_scanl]
      rw [List.map_tail,map_left op assoc,rightId]
      rw [←List.scanl_append]
      rw [List.take_append_drop]

theorem scan_map (op : M → M → M) (op' : N → N → N) (zero : M) (f : M → N)
    (hom : ∀ x y, f (op x y)=op' (f x) (f y)) (fuel : Nat) (items : List M) :
    (scan op zero fuel items).map f=scan op' (f zero) fuel (items.map f) := by
  have scanlMap (items : List M) (seed : M) :
      (items.scanl op seed).map f=(items.map f).scanl op' (f seed) := by
    induction items generalizing seed with
    | nil => rfl
    | cons x rest ih => simp only [List.scanl_cons,List.map_cons,ih,hom]
  induction fuel generalizing items with
  | zero => exact scanlMap items zero
  | succ fuel ih =>
    unfold scan
    simp only [List.length_map]
    split
    · exact scanlMap items zero
    · simp only [List.map_append,List.map_map,←List.map_take,←List.map_drop,←ih]
      rw [←List.map_tail]
      have last:=List.getLastD_map (f:=f) (l:=scan op zero fuel (items.take (items.length/2))) (a:=zero)
      rw [last]
      apply congrArg (List.append _)
      simp only [List.map_map,Function.comp_def,hom]

end Prefix
open Signal.PrivateBuffer.Semantics

abbrev Pair (W : Type) := W × W

def combine (o : Sha256.Ops B W) (low high : Pair W) : Pair W :=
  (o.xor high.1 (o.and high.2 low.1),o.and high.2 low.2)

def identity (o : Sha256.Ops B W) : Pair W := (o.wordConst 0,o.wordConst 1)

def bit (o : Sha256.Ops B W) (x : W) (index : Nat) : W :=
  o.and (o.rotr x index) (o.wordConst 1)

def packFlags (o : Sha256.Ops B W) : List W → W
  | [] => o.wordConst 0
  | flag::rest =>
    let tail := packFlags o rest
    o.add flag (o.add tail tail)

def add (o : Sha256.Ops B W) (x y : W) : W :=
  let pairs := (List.range 32).map (fun i =>
    let a := bit o x i
    let b := bit o y i
    (o.and a b,o.xor a b))
  let carries := Prefix.scan (combine o) (identity o) 6 pairs
  packFlags o ((List.range 32).map (fun i =>
    o.xor (o.xor (bit o x i) (bit o y i)) ((carries[i]?.getD (identity o)).1)))

namespace Concrete

def flag (b : Bool) : BitVec 32 := BitVec.ofNat 32 b.toNat

def boolCombine (low high : Pair Bool) : Pair Bool :=
  (high.1 ^^ (high.2 && low.1),high.2 && low.2)

def boolIdentity : Pair Bool := (false,true)

def flagPair (p : Pair Bool) : Pair (BitVec 32) := (flag p.1,flag p.2)

theorem flag_xor (a b : Bool) : flag a ^^^ flag b=flag (a ^^ b) := by cases a <;> cases b <;> decide

theorem flag_and (a b : Bool) : flag a &&& flag b=flag (a && b) := by cases a <;> cases b <;> decide

theorem combine_flag (low high : Pair Bool) :
    combine Sha256.concrete (flagPair low) (flagPair high)=flagPair (boolCombine low high) := by
  simp only [combine,flagPair,boolCombine,Sha256.concrete,flag_xor,flag_and]

theorem boolCombine_assoc (a b c : Pair Bool) : boolCombine (boolCombine a b) c=boolCombine a (boolCombine b c) := by
  simp [boolCombine,Bool.and_xor_distrib_left,Bool.and_assoc]

theorem boolCombine_right (a : Pair Bool) : boolCombine a boolIdentity=a := by
  cases a
  simp [boolCombine,boolIdentity]

theorem bit_correct (x : BitVec 32) (i : Nat) (hi : i<32) :
    bit Sha256.concrete x i=flag (x.getLsbD i) := by
  change x.rotateRight i &&& BitVec.twoPow 32 0=_
  rw [BitVec.and_twoPow]
  have h : (x.rotateRight i).getLsbD 0=x.getLsbD i := by
    simp only [BitVec.getLsbD_rotateRight,Nat.mod_eq_of_lt hi,Nat.add_zero]
    simp [show 0<32-i by omega]
  rw [h]
  cases x.getLsbD i <;> rfl

theorem pack_flags (bits : List Bool) :
    packFlags Sha256.concrete (bits.map flag)=BitVec.ofNat 32 (value bits) := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.map_cons,packFlags,ih]
    change flag b+(BitVec.ofNat 32 (value rest)+BitVec.ofNat 32 (value rest))=BitVec.ofNat 32 (value (b::rest))
    simp only [flag,←BitVec.ofNat_add,value,Nat.two_mul]

def bitPair (x y : BitVec 32) (i : Nat) : Pair Bool :=
  (x.getLsbD i && y.getLsbD i,x.getLsbD i ^^ y.getLsbD i)

theorem carry_digit (a b c : Bool) : ((a && b) ^^ ((a ^^ b) && c))=Bool.atLeastTwo a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem fold_carry (x y : BitVec 32) (n : Nat) :
    (((List.range n).map (bitPair x y)).foldl boolCombine boolIdentity).1=BitVec.carry n x y false := by
  induction n with
  | zero => simp [boolIdentity,BitVec.carry_zero]
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.foldl_append]
    simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,boolCombine,bitPair]
    rw [ih,carry_digit,BitVec.carry_succ]

theorem prefix_carry (x y : BitVec 32) (i : Nat) (hi : i<32) :
    ((Prefix.scan boolCombine boolIdentity 6 ((List.range 32).map (bitPair x y)))[i]?.getD boolIdentity).1=
      BitVec.carry i x y false := by
  rw [Prefix.scan_correct boolCombine boolIdentity boolCombine_assoc boolCombine_right]
  rw [List.getElem?_scanl,if_pos (by simp;omega)]
  simp only [Option.getD_some,←List.map_take,List.take_range,Nat.min_eq_left (Nat.le_of_lt hi)]
  exact fold_carry x y i

theorem value_testBit (bits : List Bool) (i : Nat) : (value bits).testBit i=bits[i]?.getD false := by
  induction bits generalizing i with
  | nil => simp [value]
  | cons b rest ih =>
    cases i with
    | zero => cases b <;> simp [value,Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_add_one]
      have half : value (b::rest)/2=value rest := by
        simp only [value]
        cases b <;> simp [Bool.toNat] <;> omega
      rw [half,ih]
      rfl

theorem word_pairs (x y : BitVec 32) :
    (List.range 32).map (fun i => (Sha256.concrete.and (bit Sha256.concrete x i) (bit Sha256.concrete y i),
      Sha256.concrete.xor (bit Sha256.concrete x i) (bit Sha256.concrete y i)))=
      ((List.range 32).map (bitPair x y)).map flagPair := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [bit_correct x i (List.mem_range.mp hi),bit_correct y i (List.mem_range.mp hi)]
  simp only [Sha256.concrete,flag_and,flag_xor,flagPair,bitPair,Function.comp_def]

theorem word_carry (x y : BitVec 32) (i : Nat) (hi : i<32) :
    ((Prefix.scan (combine Sha256.concrete) (identity Sha256.concrete) 6
      ((List.range 32).map (fun j => flagPair (bitPair x y j))))[i]?.getD (identity Sha256.concrete)).1=
      flag (BitVec.carry i x y false) := by
  have mapped:=Prefix.scan_map boolCombine (combine Sha256.concrete) boolIdentity flagPair
    (fun a b => (combine_flag a b).symm) 6 ((List.range 32).map (bitPair x y))
  change (Prefix.scan _ _ _ _).map flagPair=Prefix.scan _ (identity Sha256.concrete) _ _ at mapped
  simp only [List.map_map,Function.comp_def] at mapped
  rw [←mapped,List.getElem?_map]
  change ((Option.map flagPair _).getD (flagPair boolIdentity)).1=_
  rw [Option.getD_map]
  change flag (_[i]?.getD boolIdentity).1=_
  rw [prefix_carry x y i hi]

theorem add_correct (x y : BitVec 32) : add Sha256.concrete x y=x+y := by
  let bits := (List.range 32).map (fun i => x.getLsbD i ^^ y.getLsbD i ^^ BitVec.carry i x y false)
  have representation : add Sha256.concrete x y=packFlags Sha256.concrete (bits.map flag) := by
    unfold add
    rw [word_pairs]
    apply congrArg (packFlags Sha256.concrete)
    dsimp only [bits]
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro i hi
    have bound:=List.mem_range.mp hi
    rw [bit_correct x i bound,bit_correct y i bound,word_carry x y i bound]
    simp only [Sha256.concrete,flag_xor]
  rw [representation,pack_flags]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat,hi,decide_true,Bool.true_and,value_testBit]
  simp only [bits,List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]
  rw [BitVec.getLsbD_add hi]
  exact Bool.xor_assoc _ _ _

end Concrete
def mapPair (f : W → W') (p : Pair W) : Pair W' := (f p.1,f p.2)

section Refinement
variable {o : Sha256.Ops B W} {o' : Sha256.Ops B' W'} {fb : B → B'} {fw : W → W'}
variable (hom : Sha256.Hom o o' fb fw)
include hom

theorem combine_map (low high : Pair W) :
    mapPair fw (combine o low high)=combine o' (mapPair fw low) (mapPair fw high) := by
  simp only [mapPair,combine,hom.xor,hom.and]

theorem identity_map : mapPair fw (identity o)=identity o' := by
  simp only [mapPair,identity,hom.wordConst]

theorem bit_map (x : W) (i : Nat) : fw (bit o x i)=bit o' (fw x) i := by
  simp only [bit,hom.and,hom.rotr,hom.wordConst]

theorem packFlags_map (bits : List W) : fw (packFlags o bits)=packFlags o' (bits.map fw) := by
  induction bits with
  | nil => exact hom.wordConst 0
  | cons b rest ih => simp only [packFlags,List.map_cons,hom.add,ih]

theorem prefix_carry_map (pairs : List (Pair W)) (i : Nat) :
    fw (((Prefix.scan (combine o) (identity o) 6 pairs)[i]?.getD (identity o)).1)=
      ((Prefix.scan (combine o') (identity o') 6 (pairs.map (mapPair fw)))[i]?.getD (identity o')).1 := by
  have h:=Prefix.scan_map (combine o) (combine o') (identity o) (mapPair fw)
    (fun a b => combine_map hom a b) 6 pairs
  rw [identity_map hom] at h
  rw [←h,List.getElem?_map]
  rw [←identity_map hom,Option.getD_map]
  rfl

theorem add_map (x y : W) : fw (add o x y)=add o' (fw x) (fw y) := by
  unfold add
  rw [packFlags_map hom]
  simp only [List.map_map,Function.comp_def]
  apply congrArg (packFlags o')
  apply List.map_congr_left
  intro i hi
  simp only [hom.xor,bit_map hom,prefix_carry_map hom]
  simp only [List.map_map,Function.comp_def,mapPair,hom.and,hom.xor,bit_map hom]
end Refinement

def prefixOps (o : Sha256.Ops B W) : Sha256.Ops B W := {o with add:=add o}

theorem prefixOps_map {o : Sha256.Ops B W} {o' : Sha256.Ops B' W'} {fb : B → B'} {fw : W → W'}
    (hom : Sha256.Hom o o' fb fw) : Sha256.Hom (prefixOps o) (prefixOps o') fb fw :=
  {hom with add:=add_map hom}

theorem prefixOps_concrete : prefixOps Sha256.concrete=Sha256.concrete := by
  have h : add Sha256.concrete=Sha256.concrete.add := funext fun x => funext fun y => Concrete.add_correct x y
  unfold prefixOps
  rw [h]

theorem compress_correct (s : Sha256.State (BitVec 32)) (block : List (BitVec 32)) :
    Sha256CarrySave.compress (prefixOps Sha256.concrete) s block=Sha256.compress Sha256.concrete s block := by
  rw [prefixOps_concrete,Sha256CarrySave.compress_correct]

theorem compiled_compress_correct (state : Sha256.State (BVExpr 32)) (block : List (BVExpr 32))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(Sha256.digest Sha256.symbolic (Sha256CarrySave.compress (prefixOps Sha256.symbolic) state block)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (Sha256.digest Sha256.symbolic (Sha256CarrySave.compress (prefixOps Sha256.symbolic) state block)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (Sha256.digest Sha256.symbolic (Sha256CarrySave.compress (prefixOps Sha256.symbolic) state block)))).vec.get index hi)) =
    (ByteCircuit.joinValue (Sha256.digest Sha256.concrete (Sha256.compress Sha256.concrete
      (state.map (BVExpr.eval assign)) (block.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,Sha256.digest_map (Sha256.evaluationHom assign),
    Sha256CarrySave.compress_map (prefixOps_map (Sha256.evaluationHom assign)),compress_correct]

end TlsMpc.Sha256ParallelPrefix
