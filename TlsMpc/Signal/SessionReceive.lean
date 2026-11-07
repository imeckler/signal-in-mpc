import TlsMpc.Signal.RetainedReceive
import TlsMpc.Signal.NewRatchetReceive

/-! Bounded established-session receive combines retained-chain selection and a
new DH-ratchet first-message transaction. Selection is entirely secret. Public
shape requires a nonempty receiver store (at most five slots in exporters).
New agreements and pair are supplied by a same-VM X25519 stage whose remote key
must be the parsed key; the new path also checks it against the wire. This is the
classical session transaction with an externally supplied SPQR message key;
full triple-ratchet/SPQR evolution, legacy keys and persistence remain separate. -/
namespace TlsMpc.Signal.SessionReceive
open Std.Tactic.BVDecide SkippedKeys ReceiverStore

def finish (a : ByteAuth.Ops B) (useRetained : B) (oldSender : RatchetStep.State B) (old : List (Entry B n))
    (remote retained fresh : List B) : List B :=
  let newStatus := OpenResult.get a fresh 0
  let next := RetainedReceive.nextEntry a (SkippedReceive.bytesAt a remote 0) (newStatus :: fresh.drop 169)
  let updated := ReceiverStore.insert a newStatus next old
  let newResult := fresh.take 137 ++ ReceiverStore.bytes updated ++ fresh.drop (205+69*n)
  let retainedResult := OpenResult.get a retained 0 :: (oldSender.bytes ++ retained.drop 1)
  ChainSend.selectState a useRetained retainedResult newResult

def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (maxJump : Nat) (present : B)
    (oldSender : RatchetStep.State B) (old : List (Entry B n))
    (newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected : List B) : List B :=
  let parsed := ProtoParse.parseCore d o a wire
  let selected := ReceiverStore.lookup a (SkippedReceive.bytesAt a parsed 1) old
  let useRetained := ByteAuth.eqMask a selected.valid (a.const 255)
  let retained := RetainedReceive.openCore d o aes s a maxJump present old pqKey sender receiver wire expected
  let fresh := NewRatchetReceive.openCore d o aes s a maxJump n present oldSender
    newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected
  finish a useRetained oldSender old remote retained fresh

section
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha in
theorem finish_map (useRetained : B) (oldSender : RatchetStep.State B) (old : List (Entry B n)) (remote retained fresh : List B) :
    (finish a useRetained oldSender old remote retained fresh).map f =
      finish a' (f useRetained) (oldSender.map f) (old.map (Entry.map f)) (remote.map f) (retained.map f) (fresh.map f) := by
  simp only [finish,ChainSend.selectState_map ha,List.map_cons,List.map_append,OpenResult.get_map ha,
    RatchetStep.bytes_map,List.map_drop,List.map_take,ReceiverStore.bytes_map,ReceiverStore.insert_map ha,
    RetainedReceive.nextEntry_map ha,SkippedReceive.bytesAt_map ha,List.map_cons,List.map_drop,OpenResult.get_map ha]
include hd ho he hs ha in
theorem openCore_map (maxJump : Nat) (present : B) (oldSender : RatchetStep.State B) (old : List (Entry B n))
    (newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected : List B) :
    (openCore d o aes s a maxJump present oldSender old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected).map f =
      openCore d' o' aes' s' a' maxJump (f present) (oldSender.map f) (old.map (Entry.map f))
        (newPrivate.map f) (newPublic.map f) (receiveAgreement.map f) (sendAgreement.map f) (remote.map f)
        (pqKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  have h := ReceiverStore.lookup_map ha (SkippedReceive.bytesAt a (ProtoParse.parseCore d o a wire) 1) old
  have hv := congrArg Entry.valid h
  simp only [Entry.map,SkippedReceive.bytesAt_map ha,ProtoParse.parseCore_map hd ho ha] at hv
  simp only [openCore,finish_map ha,RetainedReceive.openCore_map hd ho he hs ha,NewRatchetReceive.openCore_map hd ho he hs ha,
    ByteAuth.eqMask_map ha,ha.const,hv]
end

theorem compiled_openCore_correct (maxJump : Nat) (present : BVExpr 8) (oldSender : RatchetStep.State (BVExpr 8))
    (old : List (Entry (BVExpr 8) n)) (newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected : List (BVExpr 8))
    (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      maxJump present oldSender old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        maxJump present oldSender old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
          maxJump present oldSender old newPrivate newPublic receiveAgreement sendAgreement remote pqKey sender receiver wire expected))).vec.get bit hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        maxJump (BVExpr.eval assign present) (oldSender.map (BVExpr.eval assign)) (old.map (Entry.map (BVExpr.eval assign)))
        (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign)) (receiveAgreement.map (BVExpr.eval assign))
        (sendAgreement.map (BVExpr.eval assign)) (remote.map (BVExpr.eval assign)) (pqKey.map (BVExpr.eval assign))
        (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct,openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.SessionReceive
