import TlsMpc.KernelSpecs.ParseWebSocketControlFrame

/-!
# What `replies` sends for a queued control answer (RFC 6455 sections 5.5.2, 5.5.3, 5.3)

New file; it changes no definition and no emitter imports it. Kept apart from
`ParseWebSocketControlFrame` because it depends on `PublicReceive.replies` (written against the
version that takes one masking key per queued frame, `masks : List (List Byte)`).

**`replies_one`**: from a fresh control queue (`TlsWebSocketControl.initial`), after one Ping or
Close with payload `p` (1 to 125 bytes) arrived (`control_queue`'s result, serialised as the
controller keeps it), `replies` with the masking keys `mask :: rest` (`mask` of length 4) sends
exactly one frame: `clientFrame` (RFC 6455's final masked client frame) with the opcode `reply`
gives (Pong 10 for a Ping, Close 8 for a Close), the key `mask` and the same payload.
**`control_reply`**: the same, end to end from the frame's bytes (`control_queue`).
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open TlsMpc.KernelSpecs.ParseWebSocketControl (Idle kindOf blockSet clientFrame encode_frame framesOf)
open TlsWebSocketControl (State)

set_option linter.unusedSimpArgs false

namespace TlsMpc.KernelSpecs.ParseWebSocketReplies

abbrev Byte := BitVec 8

theorem const0 : fast.const 0 = 0#8 := by rw [PublicReceive.PassOver.fast_const]

theorem initial_idle : Idle (TlsWebSocketControl.initial fast) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp only [TlsWebSocketControl.initial, List.length_replicate, const0] <;> (try decide)

/-- The queue after one Ping/Close with payload `p` from a fresh queue (`control_queue` with
`Q = TlsWebSocketControl.initial fast`). -/
def afterOne (o : Nat) (p : List Byte) : State Byte :=
  { valid := 255#8, count := 0#8, data := List.replicate 125 0#8, queued := 1#8,
    kinds := [kindOf (BitVec.ofNat 8 o), 0#8, 0#8, 0#8],
    lengths := [BitVec.ofNat 8 p.length, 0#8, 0#8, 0#8],
    payloads := blockSet (List.replicate 500 0#8) 0 (p ++ List.replicate (125 - p.length) 0#8) }

/-- `control_queue`'s result from a fresh queue is `afterOne`. -/
theorem control_queue_initial (o : Nat) (p : List Byte) :
    ({ valid := (TlsWebSocketControl.initial fast).valid, count := 0#8, data := List.replicate 125 0#8,
       queued := BitVec.ofNat 8 ((TlsWebSocketControl.initial fast).queued.toNat + 1),
       kinds := (TlsWebSocketControl.initial fast).kinds.set (TlsWebSocketControl.initial fast).queued.toNat
         (kindOf (BitVec.ofNat 8 o)),
       lengths := (TlsWebSocketControl.initial fast).lengths.set (TlsWebSocketControl.initial fast).queued.toNat
         (BitVec.ofNat 8 p.length),
       payloads := blockSet (TlsWebSocketControl.initial fast).payloads (TlsWebSocketControl.initial fast).queued.toNat
         (p ++ List.replicate (125 - p.length) 0#8) } : State Byte) = afterOne o p := by
  simp only [TlsWebSocketControl.initial, const0, afterOne]
  rfl

theorem take_blockSet (blk : List Byte) (hb : blk.length = 125) :
    (blockSet (List.replicate 500 0#8) 0 blk).take 125 = blk := by
  apply List.ext_getElem
  · simp only [blockSet, List.length_take, List.length_map, List.length_range, hb]; omega
  · intro i h1 h2
    have hi : i < 125 := by omega
    simp only [blockSet, List.getElem_take, List.getElem_map, List.getElem_range]
    rw [if_pos (Nat.div_eq_of_lt hi), Nat.mod_eq_of_lt hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    rfl

theorem kind_ok (o : Nat) (ho : o = 8 ∨ o = 9) :
    kindOf (BitVec.ofNat 8 o) = 8#8 ∨ kindOf (BitVec.ofNat 8 o) = 10#8 := by
  rcases ho with rfl | rfl <;> decide

/-- **`replies_one`.** With the queue `afterOne o p` in the controller's state, `replies` sends one
frame: RFC 6455's masked client frame with `reply`'s opcode and the payload `p`. -/
theorem replies_one (s : PublicReceive.State) (o : Nat) (ho : o = 8 ∨ o = 9) (p : List Byte)
    (hp : p.length ≤ 125) (mask : List Byte) (hmask : mask.length = 4) (rest : List (List Byte))
    (hs : s.control = TlsWebSocketControl.stateBytes (afterOne o p)) :
    framesOf (PublicReceive.replies s (mask :: rest)) =
      [((kindOf (BitVec.ofNat 8 o)).toNat, clientFrame (kindOf (BitVec.ofNat 8 o)).toNat mask p)] := by
  have hblk : (p ++ List.replicate (125 - p.length) 0#8).length = 125 := by simp; omega
  have hlen : (BitVec.ofNat 8 p.length).toNat = p.length := by simp; omega
  have e := encode_frame (kindOf (BitVec.ofNat 8 o)) (BitVec.ofNat 8 p.length) (kind_ok o ho) (by omega) mask
    (p ++ List.replicate (125 - p.length) 0#8) hmask hblk
  rw [hlen] at e
  have htake : (p ++ List.replicate (125 - p.length) 0#8).take p.length = p := by simp
  rw [htake] at e
  obtain ⟨e3, ef⟩ := e
  have hsplit : ∀ l : List Byte, l = l.take 3 ++ l.drop 3 := fun l => (List.take_append_drop 3 l).symm
  have g0 : PublicReceive.get (TlsWebSocketControl.encode fast ([255#8, 0#8, BitVec.ofNat 8 p.length,
      kindOf (BitVec.ofNat 8 o)] ++ mask ++ (p ++ List.replicate (125 - p.length) 0#8))) 0 = 255#8 := by
    rw [hsplit (TlsWebSocketControl.encode fast _), e3]; rfl
  have g1 : PublicReceive.get (TlsWebSocketControl.encode fast ([255#8, 0#8, BitVec.ofNat 8 p.length,
      kindOf (BitVec.ofNat 8 o)] ++ mask ++ (p ++ List.replicate (125 - p.length) 0#8))) 1 = 0#8 := by
    rw [hsplit (TlsWebSocketControl.encode fast _), e3]; rfl
  have g2 : PublicReceive.get (TlsWebSocketControl.encode fast ([255#8, 0#8, BitVec.ofNat 8 p.length,
      kindOf (BitVec.ofNat 8 o)] ++ mask ++ (p ++ List.replicate (125 - p.length) 0#8))) 2 =
      BitVec.ofNat 8 (p.length + 6) := by
    rw [hsplit (TlsWebSocketControl.encode fast _), e3]; rfl
  have h6 : (BitVec.ofNat 8 (p.length + 6)).toNat = p.length + 6 := by simp; omega
  have hk : (kindOf (BitVec.ofNat 8 o) == 8#8 || kindOf (BitVec.ofNat 8 o) == 10#8) = true := by
    rcases kind_ok o ho with k | k <;> simp [k]
  have c0 : PublicReceive.get s.control 0 = 255#8 := by rw [hs]; rfl
  have c127 : PublicReceive.get s.control 127 = 1#8 := by rw [hs]; rfl
  have c128 : PublicReceive.get s.control (128 + 0) = kindOf (BitVec.ofNat 8 o) := by rw [hs]; rfl
  have c132 : PublicReceive.get s.control (132 + 0) = BitVec.ofNat 8 p.length := by rw [hs]; rfl
  have cblk : (s.control.drop (136 + 125 * 0)).take 125 = p ++ List.replicate (125 - p.length) 0#8 := by
    rw [hs, show 136 + 125 * 0 = 136 from rfl]
    have hd : (TlsWebSocketControl.stateBytes (afterOne o p)).drop 136 =
        blockSet (List.replicate 500 0#8) 0 (p ++ List.replicate (125 - p.length) 0#8) := by
      simp only [TlsWebSocketControl.stateBytes, afterOne]
      exact List.drop_left' (by simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate])
    rw [hd, take_blockSet _ hblk]
  simp only [Nat.add_zero, Nat.mul_zero] at c128 c132 cblk
  have z : (0 : Byte) = 0#8 := rfl
  unfold PublicReceive.replies
  simp only [c0, c127, show (BitVec.toNat (1#8) : Nat) = 1 from rfl, show List.range 1 = [0] from rfl,
    List.mapM_cons, List.mapM_nil, Nat.add_zero, Nat.mul_zero, c128, c132, cblk, hk, z]
  have hm4 : (mask.length == 4) = true := by simp [hmask]
  have hon : ((255#8 : Byte) == (255 : Byte)) = true := by decide
  have hz0 : ((0#8 : Byte) == (0 : Byte)) = true := by decide
  have hk' : (kindOf (BitVec.ofNat 8 o) == (8 : Byte) || kindOf (BitVec.ofNat 8 o) == (10 : Byte)) = true := by
    rcases kind_ok o ho with k | k <;> rw [k] <;> decide
  simp only [g0, g1, g2, h6, ef, hm4, hon, hz0, hk', List.getElem?_cons_zero, PublicReceive.on, beq_self_eq_true,
    Bool.and_self, Bool.and_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
    pure_bind, bind_pure, Bool.false_eq_true, reduceIte]
  rfl

open TlsMpc.KernelSpecs.ParseWebSocketAccept (Boundary Ctx CloseBody cin)
open TlsMpc.KernelSpecs.ParseWebSocketControlFrame (controlFrame control_queue)
open TlsMpc.KernelSpecs.ParseWebSocketFrame (events)

/-- **`control_reply`.** End to end: a Ping or Close (payload `q ++ [b]`, 1 to 125 bytes) read by the
frame parser from a frame boundary, its outputs fed to a fresh control queue; with that queue in the
controller's state, `replies` sends exactly RFC 6455's masked client frame carrying `reply`'s answer
(Pong for a Ping, Close echoing a Close) with the first masking key. -/
theorem control_reply (cap : Nat) (hcap : cap < 65536) (S : TlsWebSocketFrame.State Byte) (c : Ctx)
    (hS : Boundary S c false) (o : Nat) (ho : o = 8 ∨ o = 9) (q : List Byte) (b : Byte)
    (hp : (q ++ [b]).length ≤ 125) (hc : (q ++ [b]).length ≤ cap) (hclose : o = 8 → CloseBody (q ++ [b]))
    (s : PublicReceive.State) (mask : List Byte) (hmask : mask.length = 4) (rest : List (List Byte))
    (hs : s.control = TlsWebSocketControl.stateBytes (TlsMpc.KernelSpecs.ParseWebSocketControl.runC
      (TlsWebSocketControl.initial fast)
      (List.zipWith cin (events cap S (controlFrame o (q ++ [b]))) (controlFrame o (q ++ [b]))))) :
    framesOf (PublicReceive.replies s (mask :: rest)) =
      [((kindOf (BitVec.ofNat 8 o)).toNat, clientFrame (kindOf (BitVec.ofNat 8 o)).toNat mask (q ++ [b]))] ∧
    TlsMpc.KernelSpecs.ParseWebSocketControl.reply o (q ++ [b]) =
      some ((kindOf (BitVec.ofNat 8 o)).toNat, q ++ [b]) := by
  obtain ⟨hq, hr⟩ := control_queue cap hcap S c hS _ initial_idle o ho q b hp hc hclose
  rw [hq, control_queue_initial] at hs
  exact ⟨replies_one s o ho _ hp mask hmask rest hs, hr⟩

end TlsMpc.KernelSpecs.ParseWebSocketReplies
