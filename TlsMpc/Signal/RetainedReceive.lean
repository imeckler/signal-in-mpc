import TlsMpc.Signal.ReceiverStore
import TlsMpc.Signal.BoundedReceive

/-! Authenticated receive across a fixed retained-chain store. The parsed remote
ratchet is selected inside MPC, including first-match semantics; no matching
chain rejects. A single selected chain's key/counter/skipped seeds are updated
only on acceptance. The sender/root state is unaffected by this path. -/
namespace TlsMpc.Signal.RetainedReceive
open Std.Tactic.BVDecide SkippedKeys ReceiverStore

def nextEntry (a : ByteAuth.Ops B) (key : Bytes B 32) (opened : List B) : Entry B n :=
  ⟨a.const 255,key,SkippedReceive.bytesAt a opened 1,SkippedReceive.bytesAt a opened 33,
    fun i => ⟨OpenResult.get a opened (37+69*i.val),SkippedReceive.bytesAt a opened (38+69*i.val),
      SkippedReceive.bytesAt a opened (70+69*i.val),SkippedReceive.bytesAt a opened (74+69*i.val)⟩⟩

def finish (a : ByteAuth.Ops B) (found : B) (key : Bytes B 32) (old : List (Entry B n)) (opened : List B) : List B :=
  let accepted := a.and (ByteAuth.eqMask a found (a.const 255)) (OpenResult.get a opened 0)
  accepted :: (ReceiverStore.bytes (ReceiverStore.commit a accepted key (nextEntry a key opened) old) ++
    ByteAuth.release a accepted (opened.drop (37+69*n)))

def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat) (present : B)
    (old : List (Entry B n)) (pqKey sender receiver wire expected : List B) : List B :=
  let parsed := ProtoParse.parseCore d o a wire
  let key : Bytes B 32 := SkippedReceive.bytesAt a parsed 1
  let selected := ReceiverStore.lookup a key old
  let opened := BoundedReceive.openCore d o aes s a maxJump present selected.ratchet selected.chain selected.counter
    (List.ofFn selected.skipped) pqKey sender receiver wire expected
  finish a selected.valid key old opened

section
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha in
theorem nextEntry_map (key : Bytes B 32) (opened : List B) :
    (nextEntry a key opened : Entry B n).map f = nextEntry a' (f ∘ key) (opened.map f) := by
  simp only [nextEntry,Entry.map,Slot.map,ha.const,OpenResult.get_map ha,SkippedReceive.bytesAt_map ha]
include ha in
theorem finish_map (found : B) (key : Bytes B 32) (old : List (Entry B n)) (opened : List B) :
    (finish a found key old opened).map f = finish a' (f found) (f ∘ key) (old.map (Entry.map f)) (opened.map f) := by
  simp only [finish,List.map_cons,List.map_append,ReceiverStore.bytes_map,ReceiverStore.commit_map ha,
    ha.and,ByteAuth.eqMask_map ha,ha.const,OpenResult.get_map ha,nextEntry_map ha,ByteAuth.release_map ha,List.map_drop]
include hd ho he hs ha in
theorem openCore_map (maxJump : Nat) (present : B) (old : List (Entry B n)) (pqKey sender receiver wire expected : List B) :
    (openCore d o aes s a maxJump present old pqKey sender receiver wire expected).map f =
      openCore d' o' aes' s' a' maxJump (f present) (old.map (Entry.map f))
        (pqKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  have h := ReceiverStore.lookup_map ha (SkippedReceive.bytesAt a (ProtoParse.parseCore d o a wire) 1) old
  simp only [SkippedReceive.bytesAt_map ha,ProtoParse.parseCore_map hd ho ha] at h
  have hv := congrArg Entry.valid h
  have hk := congrArg Entry.ratchet h
  have hc := congrArg Entry.chain h
  have hn := congrArg Entry.counter h
  have ht := congrArg Entry.skipped h
  simp only [Entry.map] at hv hk hc hn ht
  simp only [openCore,finish_map ha,SkippedReceive.bytesAt_map ha,ProtoParse.parseCore_map hd ho ha,
    BoundedReceive.openCore_map hd ho he hs ha,hv,hk,hc,hn,List.map_ofFn,←ht]
  rfl
end

theorem finish_reject (found : BitVec 8) (key : Bytes (BitVec 8) 32) (old : List (Entry (BitVec 8) n)) (opened : List (BitVec 8))
    (h : OpenResult.get ByteAuth.concrete opened 0 = 0) :
    finish ByteAuth.concrete found key old opened = 0 :: (ReceiverStore.bytes old ++ List.replicate (opened.drop (37+69*n)).length 0) := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [finish,h,hz,ReceiverStore.commit_reject _ _ _ _ (by decide : (0 : BitVec 8) ≠ 255),ByteAuth.release_reject]

theorem compiled_openCore_correct (maxJump : Nat) (present : BVExpr 8) (old : List (Entry (BVExpr 8) n))
    (pqKey sender receiver wire expected : List (BVExpr 8)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump present old pqKey sender receiver wire expected).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        maxJump present old pqKey sender receiver wire expected))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
          maxJump present old pqKey sender receiver wire expected))).vec.get bit hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        maxJump (BVExpr.eval assign present) (old.map (Entry.map (BVExpr.eval assign)))
        (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
        (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct,openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.RetainedReceive
