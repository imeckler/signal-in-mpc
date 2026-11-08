import TlsMpc.TlsWebSocketFrame

/-! Bounded private control payload collection/response queue. Four queued ping
or close responses per drain,125-byte control payloads. Queue count/kinds are
explicit protocol-control metadata; payload bytes and actual lengths stay shared.
Overflow or malformed masks reject rather than dropping controls. -/
namespace TlsMpc.TlsWebSocketControl
open Std.Tactic.BVDecide
open TlsWebSocketUpgrade (get eq either any member)
def inc (a : ByteAuth.Ops B) (x : B) : B := a.not (TlsWebSocketFrame.decByte a (a.not x))
def addSix (a : ByteAuth.Ops B) (x : B) : B := inc a (inc a (inc a (inc a (inc a (inc a x)))))
structure State (B : Type) where
  valid : B
  count : B
  data : List B
  queued : B
  kinds : List B
  lengths : List B
  payloads : List B
def initial (a : ByteAuth.Ops B) : State B :=
  ⟨a.const 255,a.const 0,List.replicate 125 (a.const 0),a.const 0,
   List.replicate 4 (a.const 0),List.replicate 4 (a.const 0),List.replicate 500 (a.const 0)⟩
def step (a : ByteAuth.Ops B) (s : State B) (data done opcode byte : B) : State B :=
  let nextCount := TlsInner.select a data (inc a s.count) s.count
  let nextData := (List.range 125).map (fun i =>
    TlsInner.select a (a.and data (eq a s.count i)) byte (get a s.data i))
  let enqueue := a.and done (member a opcode [8,9])
  let kind := TlsInner.select a (eq a opcode 9) (a.const 10) (a.const 8)
  let valid := a.and s.valid
    (a.and (member a data [0,255]) (a.and (member a done [0,255])
    (a.and (member a s.count (List.range 126)) (a.and (member a s.queued (List.range 5))
    (a.and (a.not (a.and data (eq a s.count 125)))
    (a.and (a.not (a.and enqueue (eq a s.queued 4)))
      (a.not (a.and done (a.not (member a opcode [8,9,10]))))))))))
  ⟨valid,TlsInner.select a done (a.const 0) nextCount,
   TlsWebSocketUpgrade.choose a done (List.replicate 125 (a.const 0)) nextData,
   TlsInner.select a enqueue (inc a s.queued) s.queued,
   (List.range 4).map (fun i => TlsInner.select a (a.and enqueue (eq a s.queued i)) kind (get a s.kinds i)),
   (List.range 4).map (fun i => TlsInner.select a (a.and enqueue (eq a s.queued i)) nextCount (get a s.lengths i)),
   (List.range 500).map (fun i => TlsInner.select a (a.and enqueue (eq a s.queued (i/125)))
     (get a nextData (i%125)) (get a s.payloads i))⟩
def stateBytes (s : State B) : List B :=
  [s.valid,s.count] ++ s.data ++ [s.queued] ++ s.kinds ++ s.lengths ++ s.payloads
def readState (a : ByteAuth.Ops B) (raw : List B) : State B :=
  ⟨get a raw 0,get a raw 1,(raw.drop 2).take 125,get a raw 127,
   (raw.drop 128).take 4,(raw.drop 132).take 4,(raw.drop 136).take 500⟩
def run (a : ByteAuth.Ops B) (raw : List B) : List B :=
  stateBytes (step a (readState a (raw.take 636)) (get a raw 636) (get a raw 637) (get a raw 638) (get a raw 639))

/-- Fresh mask4 is generated inside the native wrapper, never supplied by an
external API. Input valid1,lengthBE2,opcode1,mask4,payload125; output standard
private buffer valid1,lengthBE2,capacity131 data. TLS must preserve validity. -/
def encode (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let valid := a.and (eq a (get a raw 0) 255)
    (a.and (TlsWebSocketFrame.fits a 125 (get a raw 1) (get a raw 2)) (member a (get a raw 3) [8,10]))
  let header := a.xor (a.const 128) (get a raw 3) :: a.xor (a.const 128) (get a raw 2) :: (raw.drop 4).take 4
  let payload := (List.range 125).map (fun i => a.xor (get a raw (8+i)) (get a raw (4+i%4)))
  valid :: ByteAuth.release a valid (a.const 0 :: addSix a (get a raw 2) :: (header ++ payload))

def State.map (f : B → C) (s : State B) : State C :=
  ⟨f s.valid,f s.count,s.data.map f,f s.queued,s.kinds.map f,s.lengths.map f,s.payloads.map f⟩
section Mapping
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (h : ByteAuth.Hom a b f)
include h
theorem inc_map (x : B) : f (inc a x) = inc b (f x) := by
  simp only [inc,h.not,TlsWebSocketFrame.decByte_map h]
theorem addSix_map (x : B) : f (addSix a x) = addSix b (f x) := by simp only [addSix,inc_map h]
theorem initial_map : (initial a).map f = initial b := by simp only [initial,State.map,h.const,List.map_replicate]
theorem step_map (s : State B) (data done opcode byte : B) :
    (step a s data done opcode byte).map f = step b (s.map f) (f data) (f done) (f opcode) (f byte) := by
  simp only [step,State.map,h.and,h.not,h.const,inc_map h,TlsInner.select_map h,
    TlsWebSocketUpgrade.member_map h,TlsWebSocketUpgrade.eq_map h,TlsWebSocketUpgrade.get_map h,
    TlsWebSocketUpgrade.choose_map h,List.map_map,Function.comp_def,List.map_replicate]
theorem stateBytes_map (s : State B) : (stateBytes s).map f = stateBytes (s.map f) := by
  simp only [stateBytes,State.map,List.map_append,List.map_cons,List.map_nil]
theorem readState_map (raw : List B) : (readState a raw).map f = readState b (raw.map f) := by
  simp only [readState,State.map,List.map_take,List.map_drop,TlsWebSocketUpgrade.get_map h]
theorem run_map (raw : List B) : (run a raw).map f = run b (raw.map f) := by
  simp only [run,stateBytes_map h,step_map h,readState_map h,TlsWebSocketUpgrade.get_map h,List.map_take]
theorem encode_map (raw : List B) : (encode a raw).map f = encode b (raw.map f) := by
  simp only [encode,List.map_cons,h.and,h.xor,h.const,TlsWebSocketUpgrade.eq_map h,
    TlsWebSocketFrame.fits_map h,TlsWebSocketUpgrade.get_map h,TlsWebSocketUpgrade.member_map h,
    ByteAuth.release_map h,addSix_map h,List.map_append,List.map_take,List.map_drop,List.map_map,Function.comp_def]
end Mapping
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem addSix_value (x : BitVec 8) : addSix ByteAuth.concrete x = BitVec.ofNat 8 (x.toNat+6) := by
  have all : ∀ x : BitVec 8, addSix ByteAuth.concrete x = BitVec.ofNat 8 (x.toNat+6) := by decide +kernel
  exact all x
theorem compiled_run_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(run ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (run ByteAuth.concrete (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)]
theorem compiled_encode_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(encode ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (encode ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (encode ByteAuth.symbolic raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (encode ByteAuth.concrete (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,encode_map (ByteAuth.evaluationHom assign)]
end TlsMpc.TlsWebSocketControl
