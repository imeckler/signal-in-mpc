import TlsMpc.TlsChatResponse
namespace TlsMpc.TlsPrivateRequestId
open Std.Tactic.BVDecide
open Signal
open TlsWebSocketUpgrade (get)
-- Fresh joint random bytes are supplied only by the internal VM wrapper. The
-- prefix10 leaves at least2^62 reservations and gives canonical uint64 width10.
def seedBytes (a : ByteAuth.Ops B) (raw : List B) : List B :=
  a.xor (a.const 128) (a.and (get a raw 0) (a.const 63)) ::
    (List.range 7).map (fun i => get a raw (i+1))
def allowed (o : Word64.Ops B W) (a : ByteAuth.Ops B) (id : W) : B :=
  a.and (o.ule (o.const (2^63)) id) (o.ule id (o.const (2^64-2)))
def next (o : Word64.Ops B W) (a : ByteAuth.Ops B) (id : W) : B × W :=
  let valid := allowed o a id
  (valid,o.select valid (o.add id (o.const 1)) (o.const 0))
theorem seedBytes_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C}
    (ha : ByteAuth.Hom a b f) (raw : List B) :
    (seedBytes a raw).map f = seedBytes b (raw.map f) := by
  simp only [seedBytes,List.map_cons,List.map_map,Function.comp_def,ha.xor,ha.and,ha.const,
    TlsWebSocketUpgrade.get_map ha]
theorem allowed_map {o : Word64.Ops B W} {o' : Word64.Ops C V}
    {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} {fw : W → V}
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a b f) (id : W) :
    f (allowed o a id) = allowed o' b (fw id) := by
  simp only [allowed,ha.and,ho.ule,ho.const]
theorem next_map {o : Word64.Ops B W} {o' : Word64.Ops C V}
    {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} {fw : W → V}
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a b f) (id : W) :
    (f (next o a id).1,fw (next o a id).2) = next o' b (fw id) := by
  simp only [next,allowed_map ho ha,ho.select,ho.add,ho.const]
theorem allowed_value (id : BitVec 64) :
    allowed Word64.concrete ByteAuth.concrete id =
      if 2^63≤id.toNat ∧ id.toNat≤2^64-2 then 255 else 0 := by
  have lower : (Word64.concrete.const (2^63)).toNat=2^63 := by decide
  have upper : (Word64.concrete.const (2^64-2)).toNat=2^64-2 := by decide
  simp only [allowed,Word64.ule_value,lower,upper]
  change ((if 2^63≤id.toNat then (255:BitVec 8) else 0) &&&
    (if id.toNat≤2^64-2 then (255:BitVec 8) else 0)) = _
  split <;> split <;> simp_all
theorem next_increases (id : BitVec 64) (bound : 2^63≤id.toNat ∧ id.toNat≤2^64-2) :
    (next Word64.concrete ByteAuth.concrete id).1=255 ∧
    (next Word64.concrete ByteAuth.concrete id).2.toNat=id.toNat+1 := by
  have noWrap : id.toNat+1<2^64 := by omega
  simp only [next,allowed_value,if_pos bound,Word64.select_accept]
  change True ∧ (id+(1:BitVec 64)).toNat=id.toNat+1
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  simp [Nat.mod_eq_of_lt noWrap]
theorem seed_prefix (x : BitVec 8) :
    128≤(ByteAuth.concrete.xor (ByteAuth.concrete.const 128)
      (ByteAuth.concrete.and x (ByteAuth.concrete.const 63))).toNat ∧
    (ByteAuth.concrete.xor (ByteAuth.concrete.const 128)
      (ByteAuth.concrete.and x (ByteAuth.concrete.const 63))).toNat<192 := by
  have checked : ∀ x : BitVec 8, 128≤((128#8) ^^^ (x &&& 63)).toNat ∧
      ((128#8) ^^^ (x &&& 63)).toNat<192 := by decide +kernel
  exact checked x
def seedWord (raw : List (BitVec 8)) : BitVec 64 :=
  Word64.concrete.pack (seedBytes ByteAuth.concrete raw)
private theorem append_nat (x : BitVec m) (y : BitVec n) : (x++y).toNat=x.toNat*2^n+y.toNat := by
  rw [BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt y.isLt,Nat.shiftLeft_eq]
theorem seed_range (raw : List (BitVec 8)) : 2^63≤(seedWord raw).toNat ∧ (seedWord raw).toNat<3*2^62 := by
  let first := (128#8) ^^^ ((get ByteAuth.concrete raw 0) &&& 63)
  have h0 := seed_prefix (get ByteAuth.concrete raw 0)
  have h1 := (get ByteAuth.concrete raw 1).isLt
  have h2 := (get ByteAuth.concrete raw 2).isLt
  have h3 := (get ByteAuth.concrete raw 3).isLt
  have h4 := (get ByteAuth.concrete raw 4).isLt
  have h5 := (get ByteAuth.concrete raw 5).isLt
  have h6 := (get ByteAuth.concrete raw 6).isLt
  have h7 := (get ByteAuth.concrete raw 7).isLt
  change 128≤first.toNat ∧ first.toNat<192 at h0
  let value : BitVec 64 := ((first ++ get ByteAuth.concrete raw 1) ++
    (get ByteAuth.concrete raw 2 ++ get ByteAuth.concrete raw 3)) ++
    ((get ByteAuth.concrete raw 4 ++ get ByteAuth.concrete raw 5) ++
    (get ByteAuth.concrete raw 6 ++ get ByteAuth.concrete raw 7))
  change 2^63≤value.toNat ∧ value.toNat<3*2^62
  simp only [value,append_nat]
  omega
def runNext (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let output := next o a (o.pack raw)
  output.1 :: Word64.bytes o output.2
theorem runNext_map {o : Word64.Ops B W} {o' : Word64.Ops C V}
    {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} {fw : W → V}
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a b f) (raw : List B) :
    (runNext o a raw).map f = runNext o' b (raw.map f) := by
  have mapped := next_map ho ha (o.pack raw)
  rw [ho.pack] at mapped
  have first := congrArg Prod.fst mapped
  have second := congrArg Prod.snd mapped
  dsimp only at first second
  simp only [runNext,List.map_cons,Word64.bytes_map ho]
  rw [first,second]
theorem compiled_seed_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(seedBytes ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (seedBytes ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (seedBytes ByteAuth.symbolic raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (seedBytes ByteAuth.concrete (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,seedBytes_map (ByteAuth.evaluationHom assign)]
theorem compiled_next_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(runNext Word64.symbolic ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (runNext Word64.symbolic ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (runNext Word64.symbolic ByteAuth.symbolic raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (runNext Word64.concrete ByteAuth.concrete (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runNext_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.TlsPrivateRequestId
