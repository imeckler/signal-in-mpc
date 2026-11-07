import TlsMpc.Signal.SkippedReceive
import TlsMpc.Signal.ReceiveAdvance

/-! Selected receiving-chain transaction with bounded forward jumps and old
skipped seeds. Parsing selects the counter and ratchet key inside MPC. A future
counter on the current chain uses ReceiveAdvance and caches intermediate seeds;
a past counter or retained old ratchet uses first-match skipped-key lookup.
Only authenticated acceptance commits the selected chain and store. Unknown DH
ratchets, SPQR state evolution and persistent session selection remain separate. -/
namespace TlsMpc.Signal.BoundedReceive
open Std.Tactic.BVDecide
open SkippedKeys

def counter64 (o : Word64.Ops B V) (a : ByteAuth.Ops B) (counter : Bytes B 4) : V :=
  o.pack (List.replicate 4 (a.const 0) ++ List.ofFn counter)

def candidate (o : Word64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat)
    (parsed : List B) (ratchet chain : Bytes B 32) (current : Bytes B 4) (slots : List (Slot B)) : ReceiveAdvance.Candidate B :=
  let key : Bytes B 32 := SkippedReceive.bytesAt a parsed 1
  let target : Bytes B 4 := SkippedReceive.bytesAt a parsed 33
  let same := ByteAuth.equalMask a (List.ofFn key) (List.ofFn ratchet)
  let forward := a.and same (o.ule (counter64 o a current) (counter64 o a target))
  let skipped := lookupCore a key target slots
  let cached : ReceiveAdvance.Candidate B := ⟨skipped.found,skipped.seed,chain,current,skipped.slots⟩
  let advanced := ReceiveAdvance.advance s a maxJump ratchet chain (Varint.pack s a (List.ofFn current)) (Varint.pack s a (List.ofFn target)) slots
  ReceiveAdvance.choose a forward advanced cached

def finish (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (auth : B) (selected : ReceiveAdvance.Candidate B)
    (chain : Bytes B 32) (counter : Bytes B 4) (slots : List (Slot B)) (opened : List B) : List B :=
  let committed := ReceiveAdvance.commit s a auth selected chain (Varint.pack s a (List.ofFn counter)) slots
  committed.found :: (List.ofFn committed.nextChain ++
    ChainSend.selectState a committed.found (List.ofFn committed.nextCounter) (List.ofFn counter) ++
    storeBytes committed.slots ++ ByteAuth.release a committed.found (opened.drop 1))

def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat) (present : B)
    (ratchet chain : Bytes B 32) (current : Bytes B 4) (slots : List (Slot B))
    (pqKey sender receiver wire expected : List B) : List B :=
  let parsed := ProtoParse.parseCore d o a wire
  let selected := candidate o s a maxJump parsed ratchet chain current slots
  let material := Symmetric.messageMaterialFast s (List.ofFn selected.seed) (ChainSend.salt a present pqKey)
  let opened := ProtoReceive.openCore d o aes s a material.cipherKey material.iv material.macKey sender receiver wire expected
  finish s a (a.and (OpenResult.get a opened 0) (ChainSend.flagMask a present)) selected chain current slots opened

section
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho ha in
theorem counter64_map (counter : Bytes B 4) : fv (counter64 o a counter) = counter64 o' a' (f ∘ counter) := by
  simp only [counter64, ho.pack, List.map_append, List.map_replicate, ha.const, List.map_ofFn]
include ho hs ha in
theorem candidate_map (maxJump : Nat) (parsed : List B) (ratchet chain : Bytes B 32) (current : Bytes B 4) (slots : List (Slot B)) :
    (candidate o s a maxJump parsed ratchet chain current slots).map f =
      candidate o' s' a' maxJump (parsed.map f) (f ∘ ratchet) (f ∘ chain) (f ∘ current) (slots.map (Slot.map f)) := by
  have h := lookup_map ha (SkippedReceive.bytesAt a parsed 1) (SkippedReceive.bytesAt a parsed 33) slots
  have hf := congrArg Candidate.found h
  have hseed := congrArg Candidate.seed h
  have hslots := congrArg Candidate.slots h
  simp only [Candidate.map, SkippedReceive.bytesAt_map ha] at hf hseed hslots
  unfold candidate
  rw [ReceiveAdvance.choose_map ha, ReceiveAdvance.advance_map hs ha]
  simp only [ha.and, ByteAuth.equalMask_map ha,
    ho.ule, counter64_map ho ha, ReceiveAdvance.advance_map hs ha, Varint.pack_map hs ha, List.map_ofFn,
    SkippedReceive.bytesAt_map ha, ReceiveAdvance.Candidate.map, hf, hseed, hslots]
include hs ha in
theorem finish_map (auth : B) (selected : ReceiveAdvance.Candidate B) (chain : Bytes B 32) (counter : Bytes B 4)
    (slots : List (Slot B)) (opened : List B) :
    (finish s a auth selected chain counter slots opened).map f =
      finish s' a' (f auth) (selected.map f) (f ∘ chain) (f ∘ counter) (slots.map (Slot.map f)) (opened.map f) := by
  have h := ReceiveAdvance.commit_map hs ha auth selected chain (Varint.pack s a (List.ofFn counter)) slots
  simp only [Varint.pack_map hs ha, List.map_ofFn] at h
  have hf := congrArg ReceiveAdvance.Candidate.found h
  have hk := congrArg ReceiveAdvance.Candidate.nextChain h
  have hc := congrArg ReceiveAdvance.Candidate.nextCounter h
  have ht := congrArg ReceiveAdvance.Candidate.slots h
  simp only [ReceiveAdvance.Candidate.map] at hf hk hc ht
  simp only [finish, List.map_cons, List.map_append, List.map_ofFn, ChainSend.selectState_map ha, storeBytes_map, ByteAuth.release_map ha, List.map_drop, hf, hk, hc, ht]
  rfl
include hd ho he hs ha in
theorem openCore_map (maxJump : Nat) (present : B) (ratchet chain : Bytes B 32) (current : Bytes B 4)
    (slots : List (Slot B)) (pqKey sender receiver wire expected : List B) :
    (openCore d o aes s a maxJump present ratchet chain current slots pqKey sender receiver wire expected).map f =
      openCore d' o' aes' s' a' maxJump (f present) (f ∘ ratchet) (f ∘ chain) (f ∘ current) (slots.map (Slot.map f))
        (pqKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  have hp := candidate_map ho hs ha maxJump (ProtoParse.parseCore d o a wire) ratchet chain current slots
  simp only [ProtoParse.parseCore_map hd ho ha] at hp
  have hseed := congrArg ReceiveAdvance.Candidate.seed hp
  simp only [ReceiveAdvance.Candidate.map] at hseed
  have hm := SkippedReceive.materialFast_map hs
    (List.ofFn (candidate o s a maxJump (ProtoParse.parseCore d o a wire) ratchet chain current slots).seed) (ChainSend.salt a present pqKey)
  simp only [Symmetric.Material.map, List.map_ofFn, hseed, ChainSend.salt_map ha] at hm
  have hc := congrArg Symmetric.Material.cipherKey hm
  have hk := congrArg Symmetric.Material.macKey hm
  have hi := congrArg Symmetric.Material.iv hm
  simp only at hc hk hi
  simp only [openCore, finish_map hs ha, ha.and, OpenResult.get_map ha, ChainSend.flagMask_map ha,
    ProtoReceive.openCore_map hd ho he hs ha, hc, hk, hi, hp]
end

theorem finish_reject (selected : ReceiveAdvance.Candidate (BitVec 8))
    (chain : Bytes (BitVec 8) 32) (counter : Bytes (BitVec 8) 4) (slots : List (Slot (BitVec 8)))
    (opened : List (BitVec 8)) (hlen : selected.slots.length = slots.length) :
    finish Sha256.concrete ByteAuth.concrete 0 selected chain counter slots opened =
      0 :: (List.ofFn chain ++ List.ofFn counter ++ storeBytes slots ++ List.replicate (opened.drop 1).length 0) := by
  have he : ByteAuth.eqMask ByteAuth.concrete 0 (ByteAuth.concrete.const 255) = 0 := by decide
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [finish, ReceiveAdvance.commit, he, hz, SkippedKeys.chooseBytes, Unpad.chooseByte_reject,
    ChainSend.selectState_reject, chooseSlots_reject _ _ hlen, ByteAuth.release_reject]
  have hc : SkippedKeys.chooseBytes ByteAuth.concrete 0 selected.nextChain chain = chain := by
    funext i
    exact Unpad.chooseByte_reject _ _
  rw [hc]

theorem compiled_openCore_correct (maxJump : Nat) (present : BVExpr 8)
    (ratchet chain : Bytes (BVExpr 8) 32) (current : Bytes (BVExpr 8) 4) (slots : List (Slot (BVExpr 8)))
    (pqKey sender receiver wire expected : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump present ratchet chain current slots pqKey sender receiver wire expected).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump present ratchet chain current slots pqKey sender receiver wire expected))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        maxJump present ratchet chain current slots pqKey sender receiver wire expected))).vec.get index hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        maxJump (BVExpr.eval assign present) (BVExpr.eval assign ∘ ratchet) (BVExpr.eval assign ∘ chain) (BVExpr.eval assign ∘ current)
        (slots.map (Slot.map (BVExpr.eval assign))) (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.BoundedReceive
