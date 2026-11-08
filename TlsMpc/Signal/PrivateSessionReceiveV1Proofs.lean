import TlsMpc.Signal.PrivateSessionReceiveV1

namespace TlsMpc.Signal.PrivateSessionReceiveV1

theorem finish_reject (known : BitVec 8) (hknown : known=0 ∨ known=255)
    (old next : RatchetStep.State (BitVec 8))
    (receivers : List (ReceiverStore.Entry (BitVec 8) 0))
    (oldPq remote chain counter pq plain : List (BitVec 8))
    (selected : ReceiverStore.Entry (BitVec 8) 0) :
 finish ByteAuth.concrete 0 known old next receivers oldPq remote chain counter pq plain selected =
   0 :: (old.bytes ++ ReceiverStore.bytes receivers ++ oldPq ++
     List.replicate (2+(plain.take 80).length) 0) := by
 unfold finish
 dsimp only
 rw [ChainSend.selectState_reject,ReceiverStore.insert_reject 0 _ receivers (by decide)]
 simp only [replace,ReceiverStore.replaceFirst_reject,ChainSend.selectState_reject,ByteAuth.release_reject]
 have hs : List.zipWith (ReceiverStore.choose ByteAuth.concrete known) receivers receivers=receivers := by
  rcases hknown with h|h <;> subst known <;> induction receivers with
  | nil => rfl
  | cons e rest ih => simp only [List.zipWith,ReceiverStore.choose_reject,ReceiverStore.choose_accept,ih]
 rw [hs]
 simp only [List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_zero]

-- This exact expression is the sender/root selection in finish. In particular
-- the136-byte root/private/public/sending-chain state cannot change on known path.
theorem known_sender_preserved (old next : RatchetStep.State (BitVec 8))
    (h : old.bytes.length=next.bytes.length) :
 ChainSend.selectState ByteAuth.concrete 255
   (ChainSend.selectState ByteAuth.concrete 255 old.bytes next.bytes) old.bytes=old.bytes := by
 rw [ChainSend.selectState_accept _ _ h,ChainSend.selectState_accept _ _ rfl]

end TlsMpc.Signal.PrivateSessionReceiveV1
