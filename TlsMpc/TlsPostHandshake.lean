import TlsMpc.TlsReceive
import TlsMpc.Signal.Word64

/-! Shared streaming post-handshake framing for the no-resumption client.
RFC9846 4.7.1, 4.7.3, 5.1 and 6: ignore NewSessionTicket bodies; accept only
KeyUpdate otherwise; no content-type interleaving within a fragmented message;
KeyUpdate ends at the record boundary. Alert severity is determined by its
description, not its legacy level. All loops use public buffer capacity.

Input is the authenticated shared TlsReceive result, never host-decrypted data.
Output: event byte (0 reject,1 application,2 ignored control/fragment,3 update,
4 close), request byte (0/1), shared state11, shared application length2/buffer.
Only the first TWO output bytes may be opened. Ticket headers, parser state,
application length and application contents stay shared. An error state is
sticky. This module does not implement resumption or post-handshake client auth.
Word64 is reused only as a generic shared-word circuit utility. -/
namespace TlsMpc.TlsPostHandshake
open Std.Tactic.BVDecide
open Signal.Word64

structure State (B W : Type) where
  phase : B
  kind : B
  remaining : W
  bad : B

def State.map (f : B → B') (fw : W → W') (s : State B W) : State B' W' :=
  ⟨f s.phase,f s.kind,fw s.remaining,f s.bad⟩

structure Scan (B W : Type) where
  state : State B W
  update : B
  request : B

def Scan.map (f : B → B') (fw : W → W') (s : Scan B W) : Scan B' W' :=
  ⟨s.state.map f fw,f s.update,f s.request⟩

def initial (o : Ops B W) (a : ByteAuth.Ops B) : State B W :=
  ⟨a.const 0,a.const 0,o.const 0,a.const 0⟩

def choose (o : Ops B W) (a : ByteAuth.Ops B) (mask : B) (yes no : Scan B W) : Scan B W :=
  ⟨⟨TlsInner.select a mask yes.state.phase no.state.phase,
    TlsInner.select a mask yes.state.kind no.state.kind,
    o.select mask yes.state.remaining no.state.remaining,
    TlsInner.select a mask yes.state.bad no.state.bad⟩,
    TlsInner.select a mask yes.update no.update,TlsInner.select a mask yes.request no.request⟩

def appendByte (o : Ops B W) (word : W) (byte : B) : W :=
  o.pack ((bytes o word).drop 1 ++ [byte])

/-- One public-position byte. State, all branching masks and counters are shared. -/
def step (o : Ops B W) (a : ByteAuth.Ops B) (s : Scan B W) (byte : B) : Scan B W :=
  let p := s.state.phase
  let ku := ByteAuth.eqMask a s.state.kind (a.const 24)
  let length := appendByte o s.state.remaining byte
  let start : Scan B W := ⟨⟨a.const 1,byte,o.const 0,
    bor a s.state.bad (a.not (bor a (ByteAuth.eqMask a byte (a.const 4))
      (ByteAuth.eqMask a byte (a.const 24))))⟩,s.update,s.request⟩
  let first : Scan B W := ⟨{ s.state with phase := a.const 2, remaining := length },s.update,s.request⟩
  let second : Scan B W := ⟨{ s.state with phase := a.const 3, remaining := length },s.update,s.request⟩
  let last : Scan B W := ⟨{ s.state with
    phase := TlsInner.select a (eq o a length (o.const 0)) (a.const 0) (a.const 4)
    remaining := length
    bad := bor a s.state.bad (a.and ku (a.not (eq o a length (o.const 1)))) },s.update,s.request⟩
  let body : Scan B W := ⟨{ s.state with
    phase := TlsInner.select a (eq o a s.state.remaining (o.const 1)) (a.const 0) (a.const 4)
    remaining := o.sub s.state.remaining (o.const 1)
    bad := bor a s.state.bad (bor a (eq o a s.state.remaining (o.const 0))
      (a.and ku (a.not (bor a (ByteAuth.eqMask a byte (a.const 0)) (ByteAuth.eqMask a byte (a.const 1)))))) },
    bor a s.update ku, TlsInner.select a ku (ByteAuth.eqMask a byte (a.const 1)) s.request⟩
  let invalid : Scan B W := ⟨{ s.state with bad := a.const 255 },s.update,s.request⟩
  let next := choose o a (ByteAuth.eqMask a p (a.const 0)) start
    (choose o a (ByteAuth.eqMask a p (a.const 1)) first
      (choose o a (ByteAuth.eqMask a p (a.const 2)) second
        (choose o a (ByteAuth.eqMask a p (a.const 3)) last
          (choose o a (ByteAuth.eqMask a p (a.const 4)) body invalid))))
  { next with state := { next.state with bad := bor a next.state.bad s.update } }

def scan (o : Ops B W) (a : ByteAuth.Ops B) (enabled : B) (length : W) :
    Nat → List B → Scan B W → Scan B W
  | _, [], state => state
  | index, byte :: rest, state =>
      let active := a.and enabled (o.ule (o.const (index+1)) length)
      scan o a enabled length (index+1) rest (choose o a active (step o a state byte) state)

def encodeState (o : Ops B W) (s : State B W) : List B :=
  [s.phase,s.kind] ++ bytes o s.remaining ++ [s.bad]

def get (a : ByteAuth.Ops B) (data : List B) (index : Nat) : B := data[index]?.getD (a.const 0)

def decodeState (o : Ops B W) (a : ByteAuth.Ops B) (data : List B) : State B W :=
  ⟨get a data 0,get a data 1,o.pack ((data.drop 2).take 8),get a data 10⟩

def finish (o : Ops B W) (a : ByteAuth.Ops B) (s : State B W) (parsed : List B)
    (after : Scan B W) : List B :=
  let length := o.pack (List.replicate 6 (a.const 0) ++ [get a parsed 2,get a parsed 3])
  let content := parsed.drop 4
  let hs := ByteAuth.eqMask a (get a parsed 1) (a.const 22)
  let valid := a.and (ByteAuth.eqMask a (get a parsed 0) (a.const 255))
    (a.and (ByteAuth.zeroMask a s.bad) (a.and (o.ule length (o.const content.length))
      (o.ule length (o.const 16384))))
  let boundary := ByteAuth.zeroMask a s.phase
  let application := a.and valid (a.and boundary (ByteAuth.eqMask a (get a parsed 1) (a.const 23)))
  let handshake := a.and valid (a.and hs (a.and (a.not (eq o a length (o.const 0))) (ByteAuth.zeroMask a after.state.bad)))
  let alert := a.and valid (a.and boundary (a.and (ByteAuth.eqMask a (get a parsed 1) (a.const 21)) (eq o a length (o.const 2))))
  let close := a.and alert (ByteAuth.eqMask a (get a content 1) (a.const 0))
  let canceled := a.and alert (ByteAuth.eqMask a (get a content 1) (a.const 90))
  let good := bor a application (bor a handshake (bor a close canceled))
  let event := a.xor (a.and application (a.const 1))
    (a.xor (a.and handshake (TlsInner.select a after.update (a.const 3) (a.const 2)))
      (a.xor (a.and close (a.const 4)) (a.and canceled (a.const 2))))
  let request := a.and (a.and handshake after.update) (a.and after.request (a.const 1))
  let state := { after.state with bad := a.not good }
  [event,request] ++ encodeState o state ++ ByteAuth.release a application ((parsed.drop 2).take 2 ++ content)

def process (o : Ops B W) (a : ByteAuth.Ops B) (s : State B W) (parsed : List B) : List B :=
  let length := o.pack (List.replicate 6 (a.const 0) ++ [get a parsed 2,get a parsed 3])
  let hs := ByteAuth.eqMask a (get a parsed 1) (a.const 22)
  finish o a s parsed (scan o a hs length 0 (parsed.drop 4) ⟨s,a.const 0,a.const 0⟩)

def core (o : Ops B W) (a : ByteAuth.Ops B) (state parsed : List B) : List B :=
  process o a (decodeState o a state) parsed

def checked (o : Ops B W) (a : ByteAuth.Ops B) (state parsed : List B) : Option (List B) :=
  if state.length = 11 ∧ 5 ≤ parsed.length ∧ parsed.length ≤ 16389 then
    some (core o a state parsed)
  else none

def openCore (g : Gcm.Ops B G) (o : Ops B W) (a : ByteAuth.Ops B)
    (state key iv sequence wire : List B) : List B :=
  core o a state (TlsReceive.openCore g a key iv sequence wire)

section Refinement
variable {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include ho ha

theorem choose_map (mask : B) (yes no : Scan B W) :
    (choose o a mask yes no).map f fw = choose o' a' (f mask) (yes.map f fw) (no.map f fw) := by
  simp only [choose,Scan.map,State.map,TlsInner.select_map ha,ho.select]

omit ha in
theorem appendByte_map (word : W) (byte : B) :
    fw (appendByte o word byte) = appendByte o' (fw word) (f byte) := by
  simp only [appendByte,ho.pack,List.map_append,List.map_cons,List.map_nil,List.map_drop,bytes_map ho]

theorem step_map (s : Scan B W) (byte : B) :
    (step o a s byte).map f fw = step o' a' (s.map f fw) (f byte) := by
  simp only [step,choose,Scan.map,State.map,appendByte_map ho,
    TlsInner.select_map ha,bor_map ha,ByteAuth.eqMask_map ha,eq_map ho ha,
    ha.const,ha.and,ha.not,ho.const,ho.sub,ho.select]

theorem scan_map (enabled : B) (length : W) (index : Nat) (content : List B) (s : Scan B W) :
    (scan o a enabled length index content s).map f fw =
      scan o' a' (f enabled) (fw length) index (content.map f) (s.map f fw) := by
  induction content generalizing index s with
  | nil => rfl
  | cons b rest ih =>
      simp only [scan,List.map_cons,ih,choose_map ho ha,step_map ho ha,ha.and,ho.ule,ho.const]

omit ha in
theorem encodeState_map (s : State B W) :
    (encodeState o s).map f = encodeState o' (s.map f fw) := by
  simp only [encodeState,State.map,List.map_append,List.map_cons,List.map_nil,bytes_map ho]

omit ho in
theorem get_map (data : List B) (index : Nat) :
    f (get a data index) = get a' (data.map f) index := by
  simp only [get,List.getElem?_map]
  cases data[index]? <;> simp [ha.const]

theorem decodeState_map (data : List B) :
    (decodeState o a data).map f fw = decodeState o' a' (data.map f) := by
  simp only [decodeState,State.map,get_map ha,ho.pack,← List.map_take,← List.map_drop]

theorem finish_map (s : State B W) (parsed : List B) (after : Scan B W) :
    (finish o a s parsed after).map f = finish o' a' (s.map f fw) (parsed.map f) (after.map f fw) := by
  simp only [finish,List.map_append,List.map_cons,List.map_nil,ByteAuth.release_map ha,
    encodeState_map ho,State.map,Scan.map,ha.and,ha.xor,ha.not,ha.const,ByteAuth.eqMask_map ha,
    ByteAuth.zeroMask_map ha,bor_map ha,TlsInner.select_map ha,eq_map ho ha,
    ho.ule,ho.const,ho.pack,get_map ha,List.map_replicate,← List.map_take,← List.map_drop,List.length_map]

theorem process_map (s : State B W) (parsed : List B) :
    (process o a s parsed).map f = process o' a' (s.map f fw) (parsed.map f) := by
  unfold process
  rw [finish_map ho ha,scan_map ho ha]
  simp only [ByteAuth.eqMask_map ha,get_map ha,
    ho.pack,List.map_append,List.map_cons,List.map_nil,List.map_replicate,ha.const,
    List.map_drop,Scan.map]

theorem core_map (state parsed : List B) :
    (core o a state parsed).map f = core o' a' (state.map f) (parsed.map f) := by
  simp only [core,process_map ho ha,decodeState_map ho ha]

end Refinement

theorem encodeState_length (o : Ops B W) (s : State B W) : (encodeState o s).length = 11 := by
  simp [encodeState,bytes_length]

theorem process_length (o : Ops B W) (a : ByteAuth.Ops B) (s : State B W) (parsed : List B)
    (h : 4 ≤ parsed.length) : (process o a s parsed).length = parsed.length+11 := by
  simp only [process,finish,List.length_append,List.length_cons,List.length_nil,encodeState_length,
    ByteAuth.release,List.length_map,List.length_take,List.length_drop]
  omega

/-- An unauthenticated input cannot disclose a control event or request flag. -/
theorem reject_unauthenticated (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (h : get ByteAuth.concrete parsed 0 ≠ 255) :
    (process concrete ByteAuth.concrete s parsed).take 2 = [0,0] := by
  have hz : ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 0) (ByteAuth.concrete.const 255) = 0 := by
    change ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 0) 255 = 0
    rw [ByteAuth.eqMask_value,if_neg h]
  unfold process finish
  simp only [hz]
  simp [ByteAuth.concrete,bor]

/-- Failure is sticky even if later records are correctly authenticated. -/
theorem reject_failed (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (h : s.bad ≠ 0) :
    (process concrete ByteAuth.concrete s parsed).take 2 = [0,0] := by
  have hz : ByteAuth.zeroMask ByteAuth.concrete s.bad = 0 := by rw [ByteAuth.zeroMask_value,if_neg h]
  unfold process finish
  simp only [hz]
  simp [ByteAuth.concrete,bor]

/-- The only public bytes for application records are independent of the
payload (at fixed public capacity and fixed authentication/length metadata).
Even arbitrary private scan intermediates cannot affect those two bytes. -/
theorem application_event_independent (s : State (BitVec 8) (BitVec 64))
    (status high low : BitVec 8) (xs ys : List (BitVec 8))
    (left right : Scan (BitVec 8) (BitVec 64)) (h : xs.length = ys.length) :
    (finish concrete ByteAuth.concrete s (status :: 23 :: high :: low :: xs) left).take 2 =
    (finish concrete ByteAuth.concrete s (status :: 23 :: high :: low :: ys) right).take 2 := by
  simp only [finish,get,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    List.drop_succ_cons,List.drop_zero]
  have h22 : ByteAuth.eqMask ByteAuth.concrete (23 : BitVec 8) (ByteAuth.concrete.const 22) = 0 := by decide
  have h21 : ByteAuth.eqMask ByteAuth.concrete (23 : BitVec 8) (ByteAuth.concrete.const 21) = 0 := by decide
  simp only [h22,h21]
  simp [ByteAuth.concrete,bor,h]

theorem process_application_event_independent (s : State (BitVec 8) (BitVec 64))
    (status high low : BitVec 8) (xs ys : List (BitVec 8)) (h : xs.length = ys.length) :
    (process concrete ByteAuth.concrete s (status :: 23 :: high :: low :: xs)).take 2 =
    (process concrete ByteAuth.concrete s (status :: 23 :: high :: low :: ys)).take 2 := by
  unfold process
  apply application_event_independent
  exact h

theorem compiled_core_correct (state parsed : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(core symbolic ByteAuth.symbolic state parsed).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (core symbolic ByteAuth.symbolic state parsed))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (core symbolic ByteAuth.symbolic state parsed))).vec.get index hi)) =
      (ByteCircuit.joinValue (core concrete ByteAuth.concrete
        (state.map (BVExpr.eval assign)) (parsed.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,core_map (evaluationHom assign) (ByteAuth.evaluationHom assign)]

/-- Authenticated record decryption and private control framing compose without
opening an intermediate plaintext. This theorem covers the numeric output. -/
theorem compiled_openCore_correct (state key iv sequence wire : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(openCore Gcm.symbolic symbolic ByteAuth.symbolic state key iv sequence wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (openCore Gcm.symbolic symbolic ByteAuth.symbolic state key iv sequence wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore Gcm.symbolic symbolic ByteAuth.symbolic state key iv sequence wire))).vec.get index hi)) =
      (ByteCircuit.joinValue (core concrete ByteAuth.concrete (state.map (BVExpr.eval assign))
        (TlsReceive.spec (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign))
          (sequence.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  unfold openCore
  rw [core_map (evaluationHom assign) (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_correct _ _ _ _ (by simpa using hk)]

end TlsMpc.TlsPostHandshake
