import TlsMpc.Sha256

/-! Prepared HMAC states with a proof of equality to the direct RFC 2104
definition. Reusing the two prefix compression states also keeps symbolic
expression sharing explicit when a key is used more than once. -/

namespace TlsMpc.HmacPrepared

open Sha256

def hashAfterBlock (o : Ops B W) (state : State W) (message : List B) : List B :=
  let words := packWords o (message ++ padding o (64 + message.length))
  digest o (processBlocks o (words.length / 16) words state)

theorem packWords_append (o : Ops B W) (blockBytes suffix : List B) (h : blockBytes.length % 4 = 0) :
    packWords o (blockBytes ++ suffix) = packWords o blockBytes ++ packWords o suffix := by
  induction blockBytes using packWords.induct with
  | case1 a b c d rest ih =>
      simp only [List.cons_append, packWords]
      rw [ih (by simp only [List.length_cons] at h; omega)]
  | case2 blockBytes hn =>
      match blockBytes with
      | [] => rfl
      | [_] | [_, _] | [_, _, _] => simp at h
      | a :: b :: c :: d :: rest => exact False.elim (hn a b c d rest rfl)

theorem hash_block_prefix (o : Ops B W) (blockBytes suffix : List B) (hp : blockBytes.length = 64) :
    hash o (blockBytes ++ suffix) = hashAfterBlock o (compress o (initial o) (packWords o blockBytes)) suffix := by
  have hpw : (packWords o blockBytes).length = 16 := by rw [packed_length, hp]
  have hp4 : blockBytes.length % 4 = 0 := by rw [hp]
  simp only [Sha256.hash, hashAfterBlock, List.length_append, hp, List.append_assoc,
    packWords_append o blockBytes _ hp4]
  simp only [hpw]
  have count (n : Nat) : (16 + n) / 16 = n / 16 + 1 := by omega
  rw [count, processBlocks, List.drop_left' hpw, List.take_left' hpw]

def keyBlock (o : Ops B W) (key : List B) : List B :=
  let key := if key.length > 64 then hash o key else key
  key ++ List.replicate (64 - key.length) (o.byteConst 0)

theorem keyBlock_length (o : Ops B W) (key : List B) : (keyBlock o key).length = 64 :=
  hmac_block_key_length o key

def padBlock (o : Ops B W) (key : List B) (pad : Nat) : List B :=
  (keyBlock o key).map (fun byte => o.byteXor byte (o.byteConst pad))

theorem padBlock_length (o : Ops B W) (key : List B) (pad : Nat) :
    (padBlock o key pad).length = 64 := by simp [padBlock, keyBlock_length]

structure Prepared (W : Type) where
  inner : State W
  outer : State W

def prepare (o : Ops B W) (key : List B) : Prepared W :=
  ⟨compress o (initial o) (packWords o (padBlock o key 0x36)),
   compress o (initial o) (packWords o (padBlock o key 0x5c))⟩

def run (o : Ops B W) (key : Prepared W) (message : List B) : List B :=
  hashAfterBlock o key.outer (hashAfterBlock o key.inner message)

theorem run_prepare (o : Ops B W) (key message : List B) :
    run o (prepare o key) message = hmac o key message := by
  change hashAfterBlock o (compress o (initial o) (packWords o (padBlock o key 0x5c)))
    (hashAfterBlock o (compress o (initial o) (packWords o (padBlock o key 0x36))) message) = _
  rw [← hash_block_prefix o _ _ (padBlock_length o key 0x5c),
    ← hash_block_prefix o _ _ (padBlock_length o key 0x36)]
  rfl

end TlsMpc.HmacPrepared
