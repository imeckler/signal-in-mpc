import TlsMpc.Signal.SkippedKeys

/-! Fixed-capacity retained receiver chains, oldest first. Invalid slots form a
prefix in reachable states; insertion drops the oldest physical slot and appends
a new chain, exactly representing append-and-trim with dummy prefix slots.
Pinned libsignal retains at most five chains; the circuit capacity is public.
Every chain key, ratchet identifier, counter and skipped seed remains shared. -/
namespace TlsMpc.Signal.ReceiverStore
open Std.Tactic.BVDecide SkippedKeys

structure Entry (B : Type) (skips : Nat) where
  valid : B
  ratchet : Bytes B 32
  chain : Bytes B 32
  counter : Bytes B 4
  skipped : Fin skips → Slot B

def Entry.map (f : B → B') (e : Entry B n) : Entry B' n :=
  ⟨f e.valid,f ∘ e.ratchet,f ∘ e.chain,f ∘ e.counter,fun i => (e.skipped i).map f⟩
def empty (a : ByteAuth.Ops B) : Entry B n :=
  ⟨a.const 0,fun _ => a.const 0,fun _ => a.const 0,fun _ => a.const 0,fun _ => SkippedKeys.empty a⟩
def choose (a : ByteAuth.Ops B) (mask : B) (yes no : Entry B n) : Entry B n :=
  ⟨Unpad.chooseByte a mask yes.valid no.valid,chooseBytes a mask yes.ratchet no.ratchet,
    chooseBytes a mask yes.chain no.chain,chooseBytes a mask yes.counter no.counter,
    fun i => chooseSlot a mask (yes.skipped i) (no.skipped i)⟩
def matchMask (a : ByteAuth.Ops B) (key : Bytes B 32) (e : Entry B n) : B :=
  a.and (ByteAuth.eqMask a e.valid (a.const 255)) (ByteAuth.equalMask a (List.ofFn e.ratchet) (List.ofFn key))
def lookup (a : ByteAuth.Ops B) (key : Bytes B 32) : List (Entry B n) → Entry B n
  | [] => empty a
  | e :: rest => choose a (matchMask a key e) e (lookup a key rest)

def replaceFirst (a : ByteAuth.Ops B) (allow : B) (key : Bytes B 32) (next : Entry B n) : List (Entry B n) → List (Entry B n)
  | [] => []
  | e :: rest =>
    let hit := matchMask a key e
    choose a (a.and allow hit) next e :: replaceFirst a (a.and allow (a.not hit)) key next rest

def commit (a : ByteAuth.Ops B) (auth : B) (key : Bytes B 32) (next : Entry B n) (old : List (Entry B n)) : List (Entry B n) :=
  replaceFirst a (ByteAuth.eqMask a auth (a.const 255)) key next old

def insert (a : ByteAuth.Ops B) (auth : B) (next : Entry B n) (old : List (Entry B n)) : List (Entry B n) :=
  let candidate := (old.drop 1 ++ [next]).take old.length
  List.zipWith (choose a (ByteAuth.eqMask a auth (a.const 255))) candidate old

def entryBytes (e : Entry B n) : List B :=
  e.valid :: (List.ofFn e.ratchet ++ List.ofFn e.chain ++ List.ofFn e.counter ++ storeBytes (List.ofFn e.skipped))
def bytes (store : List (Entry B n)) : List B := store.flatMap entryBytes

theorem choose_accept (yes no : Entry (BitVec 8) n) : choose ByteAuth.concrete 255 yes no = yes := by
  unfold choose SkippedKeys.chooseBytes
  simp only [Unpad.chooseByte_accept, chooseSlot_accept]
theorem choose_reject (yes no : Entry (BitVec 8) n) : choose ByteAuth.concrete 0 yes no = no := by
  unfold choose SkippedKeys.chooseBytes
  simp only [Unpad.chooseByte_reject, chooseSlot_reject]

def Matches (key : Bytes (BitVec 8) 32) (e : Entry (BitVec 8) n) : Prop :=
  e.valid = 255 ∧ List.ofFn e.ratchet = List.ofFn key
instance (key : Bytes (BitVec 8) 32) (e : Entry (BitVec 8) n) : Decidable (Matches key e) := inferInstanceAs (Decidable (_ ∧ _))
theorem matchMask_value (key : Bytes (BitVec 8) 32) (e : Entry (BitVec 8) n) :
    matchMask ByteAuth.concrete key e = if Matches key e then 255 else 0 := by
  simp only [matchMask, ByteAuth.eqMask_value, ByteAuth.equalMask_value, Matches]
  change (if e.valid = 255 then 255 else 0) &&& (if List.ofFn e.ratchet = List.ofFn key then 255 else 0) = _
  by_cases hv : e.valid = 255 <;> by_cases hk : List.ofFn e.ratchet = List.ofFn key <;>
    simp only [hv,hk,if_true,if_false,true_and,false_and,and_false] <;> rfl

def lookupSpec (key : Bytes (BitVec 8) 32) : List (Entry (BitVec 8) n) → Entry (BitVec 8) n
  | [] => empty ByteAuth.concrete
  | e :: rest => if Matches key e then e else lookupSpec key rest

theorem lookup_correct (key : Bytes (BitVec 8) 32) (old : List (Entry (BitVec 8) n)) :
    lookup ByteAuth.concrete key old = lookupSpec key old := by
  induction old with
  | nil => rfl
  | cons e rest ih =>
    simp only [lookup,lookupSpec,matchMask_value]
    split <;> simp only [choose_accept,choose_reject,ih]

theorem replaceFirst_reject (key : Bytes (BitVec 8) 32) (next : Entry (BitVec 8) n) (old : List (Entry (BitVec 8) n)) :
    replaceFirst ByteAuth.concrete 0 key next old = old := by
  induction old with
  | nil => rfl
  | cons e rest ih =>
    have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
    simp only [replaceFirst,hz,choose_reject,ih]

theorem commit_reject (auth : BitVec 8) (key : Bytes (BitVec 8) 32) (next : Entry (BitVec 8) n) (old : List (Entry (BitVec 8) n))
    (h : auth ≠ 255) : commit ByteAuth.concrete auth key next old = old := by
  have hmask : ByteAuth.eqMask ByteAuth.concrete auth (ByteAuth.concrete.const 255) = 0 := by
    rw [ByteAuth.eqMask_value]
    exact if_neg h
  rw [commit,hmask,replaceFirst_reject]

theorem replaceFirst_length (a : ByteAuth.Ops B) (allow : B) (key : Bytes B 32) (next : Entry B n) (old : List (Entry B n)) :
    (replaceFirst a allow key next old).length = old.length := by
  induction old generalizing allow with
  | nil => rfl
  | cons e rest ih => simp only [replaceFirst,List.length_cons,ih]
theorem insert_length (a : ByteAuth.Ops B) (auth : B) (next : Entry B n) (old : List (Entry B n)) :
    (insert a auth next old).length = old.length := by
  simp [insert]
  omega

theorem entryBytes_length (e : Entry B n) : (entryBytes e).length = 69 + 69*n := by
  simp only [entryBytes,List.length_cons,List.length_append,List.length_ofFn,storeBytes_length]
  omega

theorem bytes_length (store : List (Entry B n)) : (bytes store).length = store.length * (69+69*n) := by
  induction store with
  | nil => simp [bytes]
  | cons e rest ih =>
    simp only [bytes,List.flatMap_cons,List.length_append,entryBytes_length,List.length_cons] at *
    rw [ih]
    simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm]

theorem chooseList_reject (yes no : List (Entry (BitVec 8) n)) (h : yes.length = no.length) :
    List.zipWith (choose ByteAuth.concrete 0) yes no = no := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all
  | cons e rest ih =>
    cases no with
    | nil => rfl
    | cons x xs => simp only [List.zipWith_cons_cons,choose_reject]; rw [ih xs (by simpa using h)]

theorem insert_reject (auth : BitVec 8) (next : Entry (BitVec 8) n) (old : List (Entry (BitVec 8) n))
    (h : auth ≠ 255) : insert ByteAuth.concrete auth next old = old := by
  have hm : ByteAuth.eqMask ByteAuth.concrete auth (ByteAuth.concrete.const 255) = 0 := by
    rw [ByteAuth.eqMask_value]; exact if_neg h
  rw [insert,hm,chooseList_reject]
  simp
  omega

inductive Operation where
  | lookup | replace | insert
  deriving BEq

def run (a : ByteAuth.Ops B) (operation : Operation) (auth : B) (key : Bytes B 32)
    (next : Entry B n) (old : List (Entry B n)) : List B :=
  match operation with
  | .lookup => entryBytes (lookup a key old)
  | .replace => bytes (commit a auth key next old)
  | .insert => bytes (insert a auth next old)

section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem empty_map : (empty a : Entry B n).map f = empty a' := by
  simp only [empty,Entry.map,Function.comp_def,ha.const,SkippedKeys.empty_map ha]
theorem choose_map (mask : B) (yes no : Entry B n) :
    (choose a mask yes no).map f = choose a' (f mask) (yes.map f) (no.map f) := by
  unfold choose Entry.map SkippedKeys.chooseBytes
  simp only [Function.comp_def,Unpad.chooseByte_map ha,chooseSlot_map ha]
theorem matchMask_map (key : Bytes B 32) (e : Entry B n) :
    f (matchMask a key e) = matchMask a' (f ∘ key) (e.map f) := by
  simp only [matchMask,Entry.map,ha.and,ByteAuth.eqMask_map ha,ha.const,ByteAuth.equalMask_map ha,List.map_ofFn]
theorem lookup_map (key : Bytes B 32) (old : List (Entry B n)) :
    (lookup a key old).map f = lookup a' (f ∘ key) (old.map (Entry.map f)) := by
  induction old with
  | nil => exact empty_map ha
  | cons e rest ih => simp only [lookup,List.map_cons,choose_map ha,matchMask_map ha,ih]
theorem replaceFirst_map (allow : B) (key : Bytes B 32) (next : Entry B n) (old : List (Entry B n)) :
    (replaceFirst a allow key next old).map (Entry.map f) = replaceFirst a' (f allow) (f ∘ key) (next.map f) (old.map (Entry.map f)) := by
  induction old generalizing allow with
  | nil => rfl
  | cons e rest ih => simp only [replaceFirst,List.map_cons,choose_map ha,ha.and,matchMask_map ha,ha.not,ih]
theorem commit_map (auth : B) (key : Bytes B 32) (next : Entry B n) (old : List (Entry B n)) :
    (commit a auth key next old).map (Entry.map f) = commit a' (f auth) (f ∘ key) (next.map f) (old.map (Entry.map f)) := by
  simp only [commit,replaceFirst_map ha,ByteAuth.eqMask_map ha,ha.const]
theorem chooseList_map (mask : B) (yes no : List (Entry B n)) :
    (List.zipWith (choose a mask) yes no).map (Entry.map f) =
      List.zipWith (choose a' (f mask)) (yes.map (Entry.map f)) (no.map (Entry.map f)) := by
  simp only [List.map_zipWith,List.zipWith_map,choose_map ha]
theorem insert_map (auth : B) (next : Entry B n) (old : List (Entry B n)) :
    (insert a auth next old).map (Entry.map f) = insert a' (f auth) (next.map f) (old.map (Entry.map f)) := by
  simp only [insert,chooseList_map ha,List.map_take,List.map_append,List.map_drop,List.map_cons,List.map_nil,
    ByteAuth.eqMask_map ha,ha.const,List.length_map]
omit ha in
theorem entryBytes_map (e : Entry B n) : (entryBytes e).map f = entryBytes (e.map f) := by
  simp only [entryBytes,Entry.map,List.map_cons,List.map_append,List.map_ofFn,storeBytes_map]
  rfl
omit ha in
theorem bytes_map (old : List (Entry B n)) : (bytes old).map f = bytes (old.map (Entry.map f)) := by
  simp only [bytes,List.map_flatMap,List.flatMap_map,Function.comp_def,entryBytes_map]
include ha in
theorem run_map (operation : Operation) (auth : B) (key : Bytes B 32) (next : Entry B n) (old : List (Entry B n)) :
    (run a operation auth key next old).map f = run a' operation (f auth) (f ∘ key) (next.map f) (old.map (Entry.map f)) := by
  cases operation <;> simp only [run,entryBytes_map,lookup_map ha,bytes_map,commit_map ha,insert_map ha]
end

theorem compiled_run_correct (operation : Operation) (auth : BVExpr 8) (key : Bytes (BVExpr 8) 32)
    (next : Entry (BVExpr 8) n) (old : List (Entry (BVExpr 8) n)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (run ByteAuth.symbolic operation auth key next old).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic operation auth key next old))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic operation auth key next old))).vec.get bit hi)) =
      (ByteCircuit.joinValue (run ByteAuth.concrete operation (BVExpr.eval assign auth) (BVExpr.eval assign ∘ key)
        (next.map (BVExpr.eval assign)) (old.map (Entry.map (BVExpr.eval assign))))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.ReceiverStore
