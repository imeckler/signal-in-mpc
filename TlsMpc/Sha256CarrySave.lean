import TlsMpc.Sha256
import TlsMpc.ByteCircuit

/-! Isolated carry-save multioperand sums; defaults remain unchanged. -/
namespace TlsMpc.Sha256CarrySave
open Std.Tactic.BVDecide

def carryNat (a b c : Nat) : Nat := (a &&& b) ^^^ ((a ^^^ b) &&& c)

theorem digit_identity (a b c : Nat) :
    a%2+b%2+c%2=((a ^^^ b ^^^ c)%2)+2*(carryNat a b c%2) := by
  have ha : a%2=0 ∨ a%2=1 := by omega
  have hb : b%2=0 ∨ b%2=1 := by omega
  have hc : c%2=0 ∨ c%2=1 := by omega
  have xorMod (x y : Nat) : (x ^^^ y)%2=(x%2) ^^^ (y%2) := Nat.xor_mod_two_pow (n:=1)
  have andMod (x y : Nat) : (x &&& y)%2=(x%2) &&& (y%2) := Nat.and_mod_two_pow (n:=1)
  simp only [carryNat,xorMod,andMod]
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;> simp only [ha,hb,hc] <;> decide

theorem natural_identity (a b c : Nat) : a+b+c=(a ^^^ b ^^^ c)+2*carryNat a b c := by
  have all : ∀ sum a b c, a+b+c=sum → a+b+c=(a ^^^ b ^^^ c)+2*carryNat a b c := by
    intro sum
    induction sum using Nat.strongRecOn with
    | ind sum ih =>
      intro a b c hs
      by_cases hz : sum=0
      · have ha : a=0 := by omega
        have hb : b=0 := by omega
        have hc : c=0 := by omega
        subst a;subst b;subst c;rfl
      · have smaller : a/2+b/2+c/2<sum := by omega
        have tail:=ih _ smaller (a/2) (b/2) (c/2) rfl
        have tail' : a/2+b/2+c/2=(a ^^^ b ^^^ c)/2+2*(carryNat a b c/2) := by
          simpa only [carryNat,Nat.xor_div_two,Nat.and_div_two] using tail
        have digit:=digit_identity a b c
        have ad:=Nat.mod_add_div a 2
        have bd:=Nat.mod_add_div b 2
        have cd:=Nat.mod_add_div c 2
        have sd:=Nat.mod_add_div (a ^^^ b ^^^ c) 2
        have kd:=Nat.mod_add_div (carryNat a b c) 2
        omega
  exact all (a+b+c) a b c rfl

def three (o : Sha256.Ops B W) (a b c : W) : W × W :=
  let ab := o.xor a b
  let carry := o.xor (o.and a b) (o.and ab c)
  (o.xor ab c,o.add carry carry)

def sum3 (o : Sha256.Ops B W) (a b c : W) : W :=
  let p := three o a b c
  o.add p.1 p.2

def sum4 (o : Sha256.Ops B W) (a b c d : W) : W :=
  let p := three o a b c
  sum3 o p.1 p.2 d

def sum5 (o : Sha256.Ops B W) (a b c d e : W) : W :=
  let p := three o a b c
  sum4 o p.1 p.2 d e

theorem sum3_correct (a b c : BitVec 32) : sum3 Sha256.concrete a b c=(a+b)+c := by
  apply BitVec.eq_of_toNat_eq
  simp only [sum3,three,Sha256.concrete,BitVec.toNat_add,BitVec.toNat_xor,BitVec.toNat_and]
  rw [Nat.add_mod_mod,Nat.mod_add_mod]
  rw [natural_identity]
  simp only [carryNat,Nat.two_mul]

theorem sum4_correct (a b c d : BitVec 32) : sum4 Sha256.concrete a b c d=((a+b)+c)+d := by
  unfold sum4
  rw [sum3_correct]
  exact congrArg (fun x => x+d) (sum3_correct a b c)

theorem sum5_correct (a b c d e : BitVec 32) : sum5 Sha256.concrete a b c d e=(((a+b)+c)+d)+e := by
  unfold sum5
  rw [sum4_correct]
  exact congrArg (fun x => (x+d)+e) (sum3_correct a b c)

def scheduleStep (o : Sha256.Ops B W) (ws : List W) : List W :=
  let back := fun n => ws[ws.length-n]?.getD (o.wordConst 0)
  ws ++ [sum4 o (Sha256.small1 o (back 2)) (back 7) (Sha256.small0 o (back 15)) (back 16)]

def extendSchedule (o : Sha256.Ops B W) : Nat → List W → List W
  | 0,ws => ws
  | n+1,ws => extendSchedule o n (scheduleStep o ws)

def round (o : Sha256.Ops B W) (k : Nat) (w : W) (s : Sha256.State W) : Sha256.State W :=
  let t1 := sum5 o s.h (Sha256.big1 o s.e) (Sha256.choose o s.e s.f s.g) (o.wordConst k) w
  let t2 := o.add (Sha256.big0 o s.a) (Sha256.majority o s.a s.b s.c)
  ⟨o.add t1 t2,s.a,s.b,s.c,o.add s.d t1,s.e,s.f,s.g⟩

def rounds (o : Sha256.Ops B W) : List Nat → List W → Sha256.State W → Sha256.State W
  | k::ks,w::ws,s => rounds o ks ws (round o k w s)
  | _,_,s => s

def compress (o : Sha256.Ops B W) (s : Sha256.State W) (block : List W) : Sha256.State W :=
  Sha256.feedForward o s (rounds o Sha256.constants (extendSchedule o 48 block) s)

theorem scheduleStep_correct (ws : List (BitVec 32)) :
    scheduleStep Sha256.concrete ws=Sha256.scheduleStep Sha256.concrete ws := by
  simp only [scheduleStep,Sha256.scheduleStep,sum4_correct]
  rfl

theorem extendSchedule_correct (n : Nat) (ws : List (BitVec 32)) :
    extendSchedule Sha256.concrete n ws=Sha256.extendSchedule Sha256.concrete n ws := by
  induction n generalizing ws with
  | zero => rfl
  | succ n ih => simp only [extendSchedule,Sha256.extendSchedule,ih,scheduleStep_correct]

theorem round_correct (k : Nat) (w : BitVec 32) (s : Sha256.State (BitVec 32)) :
    round Sha256.concrete k w s=Sha256.round Sha256.concrete k w s := by
  simp only [round,Sha256.round,sum5_correct]
  rfl

theorem rounds_correct (ks : List Nat) (ws : List (BitVec 32)) (s : Sha256.State (BitVec 32)) :
    rounds Sha256.concrete ks ws s=Sha256.rounds Sha256.concrete ks ws s := by
  induction ks generalizing ws s with
  | nil => rfl
  | cons k ks ih => cases ws with
    | nil => rfl
    | cons w ws => simp only [rounds,Sha256.rounds,ih,round_correct]

theorem compress_correct (s : Sha256.State (BitVec 32)) (block : List (BitVec 32)) :
    compress Sha256.concrete s block=Sha256.compress Sha256.concrete s block := by
  simp only [compress,Sha256.compress,rounds_correct,extendSchedule_correct]

section Refinement
variable {o : Sha256.Ops B W} {o' : Sha256.Ops B' W'} {fb : B → B'} {fw : W → W'}
variable (hom : Sha256.Hom o o' fb fw)
include hom

theorem sum3_map (a b c : W) : fw (sum3 o a b c)=sum3 o' (fw a) (fw b) (fw c) := by
  simp only [sum3,three,hom.xor,hom.and,hom.add]

theorem sum4_map (a b c d : W) : fw (sum4 o a b c d)=sum4 o' (fw a) (fw b) (fw c) (fw d) := by
  simp only [sum4,sum3_map hom,three,hom.xor,hom.and,hom.add]

theorem sum5_map (a b c d e : W) : fw (sum5 o a b c d e)=sum5 o' (fw a) (fw b) (fw c) (fw d) (fw e) := by
  simp only [sum5,sum4_map hom,three,hom.xor,hom.and,hom.add]

theorem scheduleStep_map (ws : List W) :
    (scheduleStep o ws).map fw=scheduleStep o' (ws.map fw) := by
  have get (i : Nat) : fw (ws[i]?.getD (o.wordConst 0))=(ws.map fw)[i]?.getD (o'.wordConst 0) := by
    simp only [List.getElem?_map]
    cases ws[i]? <;> simp [hom.wordConst]
  simp only [scheduleStep,List.map_append,List.map_cons,List.map_nil,List.length_map,sum4_map hom,
    Sha256.small0,Sha256.small1,Sha256.xor3,hom.xor,hom.rotr,hom.shr,get]

theorem extendSchedule_map (n : Nat) (ws : List W) :
    (extendSchedule o n ws).map fw=extendSchedule o' n (ws.map fw) := by
  induction n generalizing ws with
  | zero => rfl
  | succ n ih => simp only [extendSchedule,ih,scheduleStep_map hom]

theorem round_map (k : Nat) (w : W) (s : Sha256.State W) :
    (round o k w s).map fw=round o' k (fw w) (s.map fw) := by
  simp only [round,Sha256.State.map,sum5_map hom,Sha256.big0,Sha256.big1,Sha256.choose,
    Sha256.majority,Sha256.xor3,hom.add,hom.xor,hom.and,hom.not,hom.rotr,hom.wordConst]

theorem rounds_map (ks : List Nat) (ws : List W) (s : Sha256.State W) :
    (rounds o ks ws s).map fw=rounds o' ks (ws.map fw) (s.map fw) := by
  induction ks generalizing ws s with
  | nil => rfl
  | cons k ks ih => cases ws with
    | nil => rfl
    | cons w ws => simp only [rounds,List.map_cons,ih,round_map hom]

theorem compress_map (s : Sha256.State W) (block : List W) :
    (compress o s block).map fw=compress o' (s.map fw) (block.map fw) := by
  have feed (s t : Sha256.State W) : (Sha256.feedForward o s t).map fw=
      Sha256.feedForward o' (s.map fw) (t.map fw) := by simp [Sha256.feedForward,Sha256.State.map,hom.add]
  simp only [compress,feed,rounds_map hom,extendSchedule_map hom]
end Refinement

theorem compiled_compress_correct (state : Sha256.State (BVExpr 32)) (block : List (BVExpr 32))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(Sha256.digest Sha256.symbolic (compress Sha256.symbolic state block)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (Sha256.digest Sha256.symbolic (compress Sha256.symbolic state block)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (Sha256.digest Sha256.symbolic (compress Sha256.symbolic state block)))).vec.get index hi)) =
    (ByteCircuit.joinValue (Sha256.digest Sha256.concrete (Sha256.compress Sha256.concrete
      (state.map (BVExpr.eval assign)) (block.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,Sha256.digest_map (Sha256.evaluationHom assign),
    compress_map (Sha256.evaluationHom assign),compress_correct]

end TlsMpc.Sha256CarrySave
