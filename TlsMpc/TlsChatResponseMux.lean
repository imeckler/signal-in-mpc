import TlsMpc.TlsChatResponse
import TlsMpc.TlsWebSocketControl

/-! Four outstanding opaque conversation slots, one response per slot. The
parser runs once. At a private message end it validates schema/status with its
own parsed ID, then separately requires exactly one eligible pending ID match.
Slot eligibility is latched at message start: a newly admitted request cannot
match a response that began before its admission. Completed slots are consumed
inside the circuit, before a host can drain the queue, so coalesced replay fails.
Body/header events are uncommitted private prefixes until final validity.
-/
namespace TlsMpc.TlsChatResponseMux
open Std.Tactic.BVDecide
open Signal
open TlsWebSocketUpgrade (get eq either any)
abbrev Core := TlsChatResponse.State
structure Slot (B W : Type) where
  active : B
  eligible : B
  consumed : B
  id : W
structure State (B W : Type) where
  valid : B
  parser : Core B W
  slots : List (Slot B W)
  queued : B
  rows : List B
structure Event (B W : Type) where
  state : State B W
  bodyData : B
  bodyReset : B
  headerData : B
def slotInitial (o : Word64.Ops B W) (a : ByteAuth.Ops B) : Slot B W :=
  ⟨a.const 0,a.const 0,a.const 0,o.const 0⟩
def initial (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat) : State B W :=
  ⟨a.const 255,TlsChatResponse.initial o a capacity (o.const 0),
    List.replicate 4 (slotInitial o a),a.const 0,List.replicate 4 (a.const 0)⟩
def prepareSlot (a : ByteAuth.Ops B) (beginning : B) (s : Slot B W) : Slot B W :=
  {s with
    eligible := TlsInner.select a (eq a beginning 255)
      (a.and (eq a s.active 255) (a.not (eq a s.consumed 255))) s.eligible}
def matchSlot (o : Word64.Ops B W) (a : ByteAuth.Ops B) (id : W) (s : Slot B W) : B :=
  a.and (eq a s.active 255) (a.and (eq a s.eligible 255)
    (a.and (a.not (eq a s.consumed 255)) (Word64.eq o a id s.id)))
def tally (a : ByteAuth.Ops B) : List B → B × B
  | [] => (a.const 0,a.const 0)
  | x::xs => let tail := tally a xs
             (either a x tail.1,either a tail.2 (a.and x tail.1))
def exactlyOne (a : ByteAuth.Ops B) (masks : List B) : B :=
  let count := tally a masks
  a.and count.1 (a.not count.2)
def slotCodeFrom (a : ByteAuth.Ops B) (index : Nat) : List B → B
  | [] => a.const 0
  | x::xs => a.xor (a.and x (a.const (index+1))) (slotCodeFrom a (index+1) xs)
def slotCode (a : ByteAuth.Ops B) (masks : List B) : B := slotCodeFrom a 0 masks
def selfExpected (s : Core B W) : Core B W := {s with expected := s.id}
def validCore (s : Core B W) (valid : B) : Core B W := {s with valid := valid}
def consumeSlot (o : Word64.Ops B W) (a : ByteAuth.Ops B) (done mask : B) (s : Slot B W) : Slot B W :=
  {s with
    eligible := TlsInner.select a done (a.const 0) s.eligible,
    consumed := either a s.consumed (a.and done mask),
    id := o.select (a.and done mask) (o.const 0) s.id}
def process (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (s : State B W) (active beginning ending x : B) : Event B W :=
  let parsed := TlsChatResponse.process d o a capacity s.parser active beginning (a.const 0) x
  let finished := TlsChatResponse.finish o a (selfExpected parsed.state)
  let slots := s.slots.map (prepareSlot a beginning)
  let masks := slots.map (matchSlot o a parsed.state.id)
  let eligible := any a (slots.map (fun slot => a.and (eq a slot.active 255)
    (a.and (eq a slot.eligible 255) (a.not (eq a slot.consumed 255)))))
  let beginReady := either a (a.not (eq a beginning 255)) eligible
  let done := eq a ending 255
  let canonical := either a (eq a ending 0) done
  let room := TlsWebSocketUpgrade.member a s.queued [0,1,2,3]
  -- Current application policy closes the connection on a non2xx response.
  let accepted := a.and finished.valid (a.and finished.successful (a.and (exactlyOne a masks) room))
  let valid := a.and s.valid (a.and parsed.state.valid
    (a.and canonical (a.and beginReady (either a (a.not done) accepted))))
  let enqueue := a.and done valid
  let reset := validCore (TlsChatResponse.initial o a capacity (o.const 0)) valid
  let parser := validCore (TlsChatResponse.stateSelect o a done reset parsed.state) valid
  let next : State B W := {
    valid := valid,parser := parser,
    slots := List.zipWith (fun slot mask => consumeSlot o a done (a.and valid mask) slot) slots masks,
    queued := TlsInner.select a enqueue (TlsWebSocketControl.inc a s.queued) s.queued,
    rows := (List.range 4).map (fun i => TlsInner.select a (a.and enqueue (eq a s.queued i))
      (slotCode a masks) (get a s.rows i))}
  ⟨next,a.and valid parsed.bodyData,a.and valid parsed.bodyReset,a.and valid parsed.headerData⟩

def admit (o : Word64.Ops B W) (a : ByteAuth.Ops B) (s : State B W)
    (index : B) (id : W) (computed_validity : B) : State B W :=
  let duplicate := any a (s.slots.map (fun slot => a.and (eq a slot.active 255) (a.and (a.not (eq a slot.consumed 255)) (Word64.eq o a slot.id id))))
  let free := any a ((s.slots.zipIdx).map (fun pair => a.and (eq a index pair.2) (eq a pair.1.active 0)))
  let valid := a.and s.valid (a.and (eq a computed_validity 255)
    (a.and (TlsWebSocketUpgrade.member a index [0,1,2,3]) (a.and free (a.not duplicate))))
  {s with
    valid := valid,
    slots := (s.slots.zipIdx).map (fun pair =>
      let selected := a.and valid (eq a index pair.2)
      {
       active := TlsInner.select a selected (a.const 255) pair.1.active,
       eligible := TlsInner.select a selected (a.const 0) pair.1.eligible,
       consumed := TlsInner.select a selected (a.const 0) pair.1.consumed,
       id := o.select selected id pair.1.id})}

def stateSize : Nat := 982
def slotBytes (o : Word64.Ops B W) (slot : Slot B W) : List B :=
  [slot.active,slot.eligible,slot.consumed] ++ Word64.bytes o slot.id
def readSlot (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : Slot B W :=
  ⟨get a raw 0,get a raw 1,get a raw 2,o.pack ((raw.drop 3).take 8)⟩
def stateBytes (o : Word64.Ops B W) (s : State B W) : List B :=
  [s.valid] ++ TlsChatResponse.stateBytes o s.parser ++ s.slots.flatMap (slotBytes o) ++ [s.queued] ++ s.rows
def readState (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : State B W :=
  ⟨get a raw 0,TlsChatResponse.readState o a ((raw.drop 1).take 932),
    (List.range 4).map (fun i => readSlot o a ((raw.drop (933+11*i)).take 11)),
    get a raw 977,(List.range 4).map (fun i => get a raw (978+i))⟩
def runByte (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (raw : List B) : List B :=
  let event := process d o a capacity (readState o a (raw.take stateSize))
    (get a raw stateSize) (get a raw (stateSize+1)) (get a raw (stateSize+2)) (get a raw (stateSize+3))
  stateBytes o event.state ++ [event.bodyData,event.bodyReset,event.headerData]
def runAdmit (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  stateBytes o (admit o a (readState o a (raw.take stateSize)) (get a raw stateSize)
    (o.pack ((raw.drop (stateSize+1)).take 8)) (get a raw (stateSize+9)))

def Slot.map (f : B → C) (fw : W → V) (s : Slot B W) : Slot C V :=
  ⟨f s.active,f s.eligible,f s.consumed,fw s.id⟩
def State.map (f : B → C) (fw : W → V) (s : State B W) : State C V :=
  ⟨f s.valid,s.parser.map f fw,s.slots.map (Slot.map f fw),f s.queued,s.rows.map f⟩
def Event.map (f : B → C) (fw : W → V) (e : Event B W) : Event C V :=
  ⟨e.state.map f fw,f e.bodyData,f e.bodyReset,f e.headerData⟩
theorem selfExpected_map (s : Core B W) (f : B → C) (fw : W → V) :
    (selfExpected s).map f fw = selfExpected (s.map f fw) := rfl
theorem validCore_map (s : Core B W) (valid : B) (f : B → C) (fw : W → V) :
    (validCore s valid).map f fw = validCore (s.map f fw) (f valid) := rfl
theorem exactlyOne_four (a b c d : Bool) :
    exactlyOne ByteAuth.concrete ([a,b,c,d].map (fun value => if value then (255:BitVec 8) else 0)) =
      if ([a,b,c,d].filter id).length=1 then 255 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
section Mapping
variable {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops C V}
  {o : Word64.Ops B W} {o' : Word64.Ops C V} {a : ByteAuth.Ops B} {b : ByteAuth.Ops C}
  {f : B → C} {fw : W → V}
  (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a b f)
include ho ha in
 theorem slotInitial_map : (slotInitial o a).map f fw = slotInitial o' b := by
  simp only [slotInitial,Slot.map,ha.const,ho.const]
include ho ha in
 theorem initial_map (capacity : Nat) : (initial o a capacity).map f fw = initial o' b capacity := by
  simp only [initial,State.map,TlsChatResponse.initial_map ho ha,ho.const,ha.const,List.map_replicate,slotInitial_map ho ha]
include ha in
 theorem prepareSlot_map (beginning : B) (s : Slot B W) :
    (prepareSlot a beginning s).map f fw = prepareSlot b (f beginning) (s.map f fw) := by
  simp only [prepareSlot,Slot.map,TlsInner.select_map ha,TlsWebSocketUpgrade.eq_map ha,ha.and,ha.not]
include ha in
 theorem prepare_active_map (beginning : B) (s : Slot B W) :
    f (prepareSlot a beginning s).active = (prepareSlot b (f beginning) (s.map f fw)).active :=
  congrArg (fun slot : Slot C V => slot.active) (prepareSlot_map (fw:=fw) ha beginning s)
include ha in
 theorem prepare_eligible_map (beginning : B) (s : Slot B W) :
    f (prepareSlot a beginning s).eligible = (prepareSlot b (f beginning) (s.map f fw)).eligible :=
  congrArg (fun slot : Slot C V => slot.eligible) (prepareSlot_map (fw:=fw) ha beginning s)
include ha in
 theorem prepare_consumed_map (beginning : B) (s : Slot B W) :
    f (prepareSlot a beginning s).consumed = (prepareSlot b (f beginning) (s.map f fw)).consumed :=
  congrArg (fun slot : Slot C V => slot.consumed) (prepareSlot_map (fw:=fw) ha beginning s)
include ha in
 theorem prepare_id_map (beginning : B) (s : Slot B W) :
    fw (prepareSlot a beginning s).id = (prepareSlot b (f beginning) (s.map f fw)).id :=
  congrArg (fun slot : Slot C V => slot.id) (prepareSlot_map (fw:=fw) ha beginning s)
include ho ha in
 theorem matchSlot_map (id : W) (s : Slot B W) :
    f (matchSlot o a id s) = matchSlot o' b (fw id) (s.map f fw) := by
  simp only [matchSlot,Slot.map,TlsWebSocketUpgrade.eq_map ha,Word64.eq_map ho ha,ha.and,ha.not]
include ha in
 theorem tally_map (masks : List B) :
    (f (tally a masks).1,f (tally a masks).2) = tally b (masks.map f) := by
  induction masks with
  | nil => simp only [tally,List.map_nil,ha.const]
  | cons x xs ih =>
    have first := congrArg Prod.fst ih
    have second := congrArg Prod.snd ih
    simp only [Prod.fst,Prod.snd] at first second
    simp only [tally,List.map_cons,TlsWebSocketUpgrade.either_map ha,ha.and,first,second]
include ha in
 theorem exactlyOne_map (masks : List B) : f (exactlyOne a masks) = exactlyOne b (masks.map f) := by
  have first := congrArg Prod.fst (tally_map ha masks)
  have second := congrArg Prod.snd (tally_map ha masks)
  simp only [Prod.fst,Prod.snd] at first second
  simp only [exactlyOne,ha.and,ha.not,first,second]
include ha in
 theorem slotCodeFrom_map (masks : List B) (index : Nat) :
    f (slotCodeFrom a index masks) = slotCodeFrom b index (masks.map f) := by
  induction masks generalizing index with
  | nil => simp only [slotCodeFrom,List.map_nil,ha.const]
  | cons x xs ih => simp only [slotCodeFrom,List.map_cons,ha.xor,ha.and,ha.const,ih]
include ha in
 theorem slotCode_map (masks : List B) : f (slotCode a masks) = slotCode b (masks.map f) :=
  slotCodeFrom_map ha masks 0
include ho ha in
 theorem consumeSlot_map (done mask : B) (s : Slot B W) :
    (consumeSlot o a done mask s).map f fw = consumeSlot o' b (f done) (f mask) (s.map f fw) := by
  simp only [consumeSlot,Slot.map,TlsInner.select_map ha,TlsWebSocketUpgrade.either_map ha,
    ho.select,ho.const,ha.and,ha.const]
include hd ho ha in
 theorem process_map (capacity : Nat) (s : State B W) (active beginning ending x : B) :
    (process d o a capacity s active beginning ending x).map f fw =
      process d' o' b capacity (s.map f fw) (f active) (f beginning) (f ending) (f x) := by
  have hp := TlsChatResponse.process_map hd ho ha capacity s.parser active beginning (a.const 0) x
  rw [ha.const] at hp
  let p0 := TlsChatResponse.process d o a capacity s.parser active beginning (a.const 0) x
  let p1 := TlsChatResponse.process d' o' b capacity (s.parser.map f fw) (f active) (f beginning) (b.const 0) (f x)
  have ps : p0.state.map f fw = p1.state := congrArg (fun e => e.state) hp
  have pv : f p0.state.valid = p1.state.valid := congrArg (fun e => e.state.valid) hp
  have pi : fw p0.state.id = p1.state.id := congrArg (fun e => e.state.id) hp
  have pb : f p0.bodyData = p1.bodyData := congrArg (fun e => e.bodyData) hp
  have pr : f p0.bodyReset = p1.bodyReset := congrArg (fun e => e.bodyReset) hp
  have ph : f p0.headerData = p1.headerData := congrArg (fun e => e.headerData) hp
  have hf := TlsChatResponse.finish_map ho ha (selfExpected p0.state)
  rw [selfExpected_map,ps] at hf
  have fv : f (TlsChatResponse.finish o a (selfExpected p0.state)).valid =
      (TlsChatResponse.finish o' b (selfExpected p1.state)).valid := congrArg (fun state => state.valid) hf
  have fs : f (TlsChatResponse.finish o a (selfExpected p0.state)).successful =
      (TlsChatResponse.finish o' b (selfExpected p1.state)).successful := congrArg (fun state => state.successful) hf
  dsimp only [p0,p1] at ps pv pi pb pr ph fv fs
  simp only [process,Event.map,State.map,List.map_map,Function.comp_def,List.map_zipWith,
    TlsWebSocketUpgrade.eq_map ha,TlsWebSocketUpgrade.member_map ha,TlsWebSocketUpgrade.either_map ha,
    TlsWebSocketUpgrade.any_map ha,TlsWebSocketUpgrade.get_map ha,TlsInner.select_map ha,
    ha.and,ha.not,ha.const,prepareSlot_map ha,matchSlot_map ho ha,consumeSlot_map ho ha,
    exactlyOne_map ha,slotCode_map ha,TlsWebSocketControl.inc_map ha,
    validCore_map,TlsChatResponse.stateSelect_map ho ha,TlsChatResponse.initial_map ho ha,
    ho.const,ps,pv,pi,pb,pr,ph,fv,fs,List.zipWith_map,prepare_active_map (fw:=fw) ha,prepare_eligible_map (fw:=fw) ha,prepare_consumed_map (fw:=fw) ha,prepare_id_map (fw:=fw) ha]
include ho ha in
 theorem admit_map (s : State B W) (index : B) (id : W) (computed_validity : B) :
    (admit o a s index id computed_validity).map f fw =
      admit o' b (s.map f fw) (f index) (fw id) (f computed_validity) := by
  simp only [admit,State.map,Slot.map,List.map_map,Function.comp_def,List.zipIdx_map,
    Prod.map_fst,Prod.map_snd,id_eq,TlsWebSocketUpgrade.any_map ha,TlsWebSocketUpgrade.eq_map ha,
    TlsWebSocketUpgrade.member_map ha,TlsInner.select_map ha,Word64.eq_map ho ha,
    ha.and,ha.not,ha.const,ho.select]
include ho in
 theorem slotBytes_map (slot : Slot B W) : (slotBytes o slot).map f = slotBytes o' (slot.map f fw) := by
  simp only [slotBytes,Slot.map,List.map_append,List.map_cons,List.map_nil,Word64.bytes_map ho]
include ho ha in
 theorem readSlot_map (raw : List B) : (readSlot o a raw).map f fw = readSlot o' b (raw.map f) := by
  simp only [readSlot,Slot.map,TlsWebSocketUpgrade.get_map ha,ho.pack,List.map_take,List.map_drop]
include ho ha in
 theorem stateBytes_map (s : State B W) : (stateBytes o s).map f = stateBytes o' (s.map f fw) := by
  simp only [stateBytes,State.map,List.map_append,List.map_cons,List.map_nil,
    TlsChatResponse.stateBytes_map ho ha,List.map_flatMap,List.flatMap_map,Function.comp_def,slotBytes_map ho]
include ho ha in
 theorem readState_map (raw : List B) : (readState o a raw).map f fw = readState o' b (raw.map f) := by
  simp only [readState,State.map,TlsWebSocketUpgrade.get_map ha,List.map_take,List.map_drop,
    TlsChatResponse.readState_map ho ha,List.map_map,Function.comp_def,readSlot_map ho ha]
include hd ho ha in
 theorem runByte_map (capacity : Nat) (raw : List B) :
    (runByte d o a capacity raw).map f = runByte d' o' b capacity (raw.map f) := by
  have event := process_map hd ho ha capacity (readState o a (raw.take stateSize))
    (get a raw stateSize) (get a raw (stateSize+1)) (get a raw (stateSize+2)) (get a raw (stateSize+3))
  simp only [readState_map ho ha,List.map_take,TlsWebSocketUpgrade.get_map ha] at event
  have es := congrArg Event.state event
  have eb := congrArg Event.bodyData event
  have er := congrArg Event.bodyReset event
  have eh := congrArg Event.headerData event
  dsimp only [Event.map] at es eb er eh
  simp only [runByte,List.map_append,List.map_cons,List.map_nil,stateBytes_map ho ha,es,eb,er,eh]
include ho ha in
 theorem runAdmit_map (raw : List B) : (runAdmit o a raw).map f = runAdmit o' b (raw.map f) := by
  simp only [runAdmit,stateBytes_map ho ha,admit_map ho ha,readState_map ho ha,
    List.map_take,List.map_drop,TlsWebSocketUpgrade.get_map ha,ho.pack]
end Mapping
theorem compiled_runByte_correct (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
        (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runByte_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
theorem compiled_runAdmit_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(runAdmit Word64.symbolic ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runAdmit Word64.symbolic ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runAdmit Word64.symbolic ByteAuth.symbolic raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (runAdmit Word64.concrete ByteAuth.concrete
        (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runAdmit_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.TlsChatResponseMux
