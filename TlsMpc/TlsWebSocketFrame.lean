import TlsMpc.TlsWebSocketUpgrade

/-! Private server-to-client RFC6455 frame machine for the bounded binary chat
profile. No extension, masking or text opcode is negotiated. Payload capacity is
public and at most65535; canonical16-bit lengths, binary continuation, interleaved
controls and complete-message limits are checked without opening body lengths.
Frame/message/control events and payload activity stay shared. -/
namespace TlsMpc.TlsWebSocketFrame
open Std.Tactic.BVDecide
open TlsWebSocketUpgrade (get eq either any member)

def decLoop (a : ByteAuth.Ops B) (x : B) : List Nat → B → B → B
  | [],_,out => out
  | bit::rest,borrow,out =>
    let b := a.maskBit x bit
    decLoop a x rest (a.and borrow (a.not b))
      (a.xor out (a.and (a.xor b borrow) (a.const (2^bit))))
def decByte (a : ByteAuth.Ops B) (x : B) : B := decLoop a x (List.range 8) (a.const 255) (a.const 0)
def dec (a : ByteAuth.Ops B) (hi lo : B) : B × B :=
  (TlsInner.select a (eq a lo 0) (decByte a hi) hi,decByte a lo)
def zero (a : ByteAuth.Ops B) (hi lo : B) : B := a.and (eq a hi 0) (eq a lo 0)
def one (a : ByteAuth.Ops B) (hi lo : B) : B := a.and (eq a hi 0) (eq a lo 1)
def fits (a : ByteAuth.Ops B) (capacity : Nat) (hi lo : B) : B :=
  either a (member a hi (List.range (capacity/256)))
    (a.and (eq a hi (capacity/256)) (member a lo (List.range (capacity%256+1))))
def control (a : ByteAuth.Ops B) (opcode : B) : B := member a opcode [8,9,10]
def dataKind (a : ByteAuth.Ops B) (opcode : B) : B := member a opcode [0,2]

structure State (B : Type) where
  -- first header, second header, extended high, extended low, payload
  phases : List B
  valid : B
  closed : B
  opcode : B
  fin : B
  fragmented : B
  high : B
  low : B
  messageHigh : B
  messageLow : B
  -- close code/reason validation is attached before exposing close completion.
  payloadFirst : B
  payloadSecond : B
  closeCodeHigh : B
  closeCodeValid : B
  utfPhases : List B

structure Event (B : Type) where
  state : State B
  data : B
  controlData : B
  messageStart : B
  frameDone : B
  messageDone : B
  controlDone : B

def start (a : ByteAuth.Ops B) (capacity : Nat) : State B :=
  ⟨TlsWebSocketUpgrade.initial a 4,a.const 255,a.const 0,a.const 0,a.const 0,a.const 0,a.const 0,a.const 0,
   a.const (capacity/256),a.const capacity,a.const 255,a.const 0,a.const 0,a.const 0,
   TlsWebSocketUpgrade.initial a 7⟩

/-- UTF8 DFA: accepting, one/two/three generic continuation bytes, and E0/ED/F0/F4
first-continuation restrictions. Rejects overlongs, surrogates and >U+10FFFF. -/
def utfStep (a : ByteAuth.Ops B) (state : List B) (x : B) : List B :=
  let p := fun i => get a state i
  let range := fun low count => member a x ((List.range count).map (·+low))
  let continuation := range 128 64
  [either a (a.and (p 0) (range 0 128)) (a.and (p 1) continuation),
   either a (a.and (p 0) (range 194 30))
     (either a (a.and (p 2) continuation)
       (either a (a.and (p 4) (range 160 32)) (a.and (p 5) (range 128 32)))),
   either a (a.and (p 0) (either a (range 225 12) (range 238 2)))
     (either a (a.and (p 3) continuation)
       (either a (a.and (p 6) (range 144 48)) (a.and (p 7) (range 128 16)))),
   a.and (p 0) (range 241 3),a.and (p 0) (eq a x 224),a.and (p 0) (eq a x 237),
   a.and (p 0) (eq a x 240),a.and (p 0) (eq a x 244)]
def closeCode (a : ByteAuth.Ops B) (hi lo : B) : B :=
  either a (a.and (eq a hi 3) (member a lo [232,233,234,235,239,240,241,242,243,244,245,246]))
    (either a (a.and (eq a hi 11) (member a lo ((List.range 72).map (·+184))))
      (either a (member a hi ((List.range 7).map (·+12)))
        (a.and (eq a hi 19) (member a lo (List.range 136)))))

def step (a : ByteAuth.Ops B) (capacity : Nat) (s : State B) (x : B) : Event B :=
  let p := fun i => get a s.phases i
  let op := a.and x (a.const 15)
  let fin := a.maskBit x 7
  let ctl := control a s.opcode
  let dat := dataKind a s.opcode
  let small := a.and (p 1) (a.not (a.maskBit x 7))
  let length := a.and x (a.const 127)
  let extended := eq a length 126
  let short := a.not (member a length [126,127])
  let readyShort := a.and small short
  let readyLong := p 3
  let ready := either a readyShort readyLong
  let high := TlsInner.select a readyLong s.high (a.const 0)
  let low := TlsInner.select a readyLong x length
  let empty := zero a high low
  let payloadEnd := a.and (p 4) (one a s.high s.low)
  let frameDone := either a (a.and ready empty) payloadEnd
  let messageDone := a.and frameDone (a.and dat s.fin)
  let controlDone := a.and frameDone ctl
  let newMessage := a.and (p 0) (eq a op 2)
  let headerValid := a.and (eq a (a.and x (a.const 112)) 0)
    (a.and (member a op [0,2,8,9,10])
      (a.and (a.not (a.and (eq a op 0) (a.not s.fragmented)))
        (a.and (a.not (a.and (eq a op 2) s.fragmented))
          (a.not (a.and (control a op) (a.not fin))))))
  let lengthValid := a.and (fits a capacity high low)
    (a.and (a.not (a.and ctl (a.not (eq a high 0))))
      (a.and (a.not (a.and ctl (member a low [126,127])))
        (a.not (a.and (eq a s.opcode 8) (one a high low)))))
  let codeNow := closeCode a s.closeCodeHigh x
  let utfNext := utfStep a s.utfPhases x
  let reason := a.and (p 4) (a.and (eq a s.opcode 8)
    (a.not (either a s.payloadFirst s.payloadSecond)))
  let closeEndValid := either a (a.and ready empty)
    (a.and (either a s.closeCodeValid (a.and s.payloadSecond codeNow))
      (TlsInner.select a reason (get a utfNext 0) (get a s.utfPhases 0)))
  let valid := a.and (a.and s.valid (a.not s.closed))
    (a.and (a.not (a.and (p 0) (a.not headerValid)))
      (a.and (a.not (a.and (p 1) (either a (a.maskBit x 7)
        (either a (eq a length 127) (a.and ctl extended)))))
      (a.and (a.not (a.and ready (a.not lengthValid)))
      (a.and (a.not (a.and readyLong (a.and (eq a s.high 0) (member a x (List.range 126)))))
      (a.and (a.not (a.and (p 4) (a.and dat (zero a s.messageHigh s.messageLow))))
      (a.and (a.not (a.and reason (a.not (any a utfNext))))
        (a.not (a.and controlDone (a.and (eq a s.opcode 8) (a.not closeEndValid))))))))))
  let payloadNext := dec a s.high s.low
  let messageNext := dec a s.messageHigh s.messageLow
  let next : State B := {s with
    phases := [frameDone,p 0,a.and small extended,p 2,
      either a (a.and ready (a.not empty)) (a.and (p 4) (a.not payloadEnd))],valid := valid,closed := either a s.closed (a.and controlDone (eq a s.opcode 8)),
    opcode := TlsInner.select a (p 0) op s.opcode,fin := TlsInner.select a (p 0) fin s.fin,
    fragmented := TlsInner.select a (a.and frameDone dat) (a.not s.fin) s.fragmented,
    high := TlsInner.select a (p 2) x (TlsInner.select a ready high
      (TlsInner.select a (p 4) payloadNext.1 s.high)),
    low := TlsInner.select a ready low (TlsInner.select a (p 4) payloadNext.2 s.low),
    messageHigh := TlsInner.select a newMessage (a.const (capacity/256))
      (TlsInner.select a (a.and (p 4) dat) messageNext.1 s.messageHigh),
    messageLow := TlsInner.select a newMessage (a.const capacity)
      (TlsInner.select a (a.and (p 4) dat) messageNext.2 s.messageLow),
    payloadFirst := TlsInner.select a ready (a.const 255)
      (TlsInner.select a (p 4) (a.const 0) s.payloadFirst),
    payloadSecond := TlsInner.select a ready (a.const 0)
      (TlsInner.select a (p 4) s.payloadFirst s.payloadSecond),
    closeCodeHigh := TlsInner.select a (a.and (p 4) s.payloadFirst) x s.closeCodeHigh,
    closeCodeValid := TlsInner.select a ready (a.const 0)
      (TlsInner.select a (a.and (p 4) s.payloadSecond) codeNow s.closeCodeValid),
    utfPhases := TlsWebSocketUpgrade.choose a ready (TlsWebSocketUpgrade.initial a 7)
      (TlsWebSocketUpgrade.choose a reason utfNext s.utfPhases)}
  ⟨next,a.and valid (a.and (p 4) dat),a.and valid (a.and (p 4) ctl),
   a.and valid newMessage,a.and valid frameDone,a.and valid messageDone,a.and valid controlDone⟩

def State.map (f : B → C) (s : State B) : State C :=
  ⟨s.phases.map f,f s.valid,f s.closed,f s.opcode,f s.fin,f s.fragmented,f s.high,f s.low,
   f s.messageHigh,f s.messageLow,f s.payloadFirst,f s.payloadSecond,f s.closeCodeHigh,
   f s.closeCodeValid,s.utfPhases.map f⟩
def Event.map (f : B → C) (e : Event B) : Event C :=
  ⟨e.state.map f,f e.data,f e.controlData,f e.messageStart,f e.frameDone,f e.messageDone,f e.controlDone⟩
def stateSelect (a : ByteAuth.Ops B) (mask : B) (yes no : State B) : State B :=
  ⟨TlsWebSocketUpgrade.choose a mask yes.phases no.phases,
   TlsInner.select a mask yes.valid no.valid,TlsInner.select a mask yes.closed no.closed,
   TlsInner.select a mask yes.opcode no.opcode,TlsInner.select a mask yes.fin no.fin,
   TlsInner.select a mask yes.fragmented no.fragmented,TlsInner.select a mask yes.high no.high,
   TlsInner.select a mask yes.low no.low,TlsInner.select a mask yes.messageHigh no.messageHigh,
   TlsInner.select a mask yes.messageLow no.messageLow,TlsInner.select a mask yes.payloadFirst no.payloadFirst,
   TlsInner.select a mask yes.payloadSecond no.payloadSecond,TlsInner.select a mask yes.closeCodeHigh no.closeCodeHigh,
   TlsInner.select a mask yes.closeCodeValid no.closeCodeValid,
   TlsWebSocketUpgrade.choose a mask yes.utfPhases no.utfPhases⟩
def stateBytes (s : State B) : List B :=
  s.phases ++ [s.valid,s.closed,s.opcode,s.fin,s.fragmented,s.high,s.low,s.messageHigh,s.messageLow,
    s.payloadFirst,s.payloadSecond,s.closeCodeHigh,s.closeCodeValid] ++ s.utfPhases
def stateSize : Nat := 26
def readState (a : ByteAuth.Ops B) (raw : List B) : State B :=
  ⟨raw.take 5,get a raw 5,get a raw 6,get a raw 7,get a raw 8,get a raw 9,
   get a raw 10,get a raw 11,get a raw 12,get a raw 13,get a raw 14,get a raw 15,
   get a raw 16,get a raw 17,(raw.drop 18).take 8⟩
@[irreducible] def runByte (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : List B :=
  let s := readState a (raw.take stateSize)
  let active := get a raw stateSize
  let byte := get a raw (stateSize+1)
  let event := step a capacity s byte
  let selected := stateSelect a (eq a active 255) event.state s
  let valid := a.and selected.valid (either a (eq a active 0) (eq a active 255))
  let next := {selected with valid := valid}
  valid :: (ByteAuth.release a (a.and valid active)
    [event.data,event.controlData,event.messageStart,event.frameDone,event.messageDone,event.controlDone] ++ stateBytes next)

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (h : ByteAuth.Hom a b f)
include h
theorem decLoop_map (x : B) (is : List Nat) (borrow out : B) :
    f (decLoop a x is borrow out) = decLoop b (f x) is (f borrow) (f out) := by
  induction is generalizing borrow out with
  | nil => rfl
  | cons bit is ih => simp only [decLoop,ih,h.and,h.not,h.maskBit,h.xor,h.const]
theorem decByte_map (x : B) : f (decByte a x) = decByte b (f x) := by
  simp only [decByte,decLoop_map h,h.const]
theorem dec_map (hi lo : B) :
    (f (dec a hi lo).1,f (dec a hi lo).2) = dec b (f hi) (f lo) := by
  simp only [dec,TlsInner.select_map h,TlsWebSocketUpgrade.eq_map h,decByte_map h]
theorem zero_map (hi lo : B) : f (zero a hi lo) = zero b (f hi) (f lo) := by
  simp only [zero,h.and,TlsWebSocketUpgrade.eq_map h]
theorem one_map (hi lo : B) : f (one a hi lo) = one b (f hi) (f lo) := by
  simp only [one,h.and,TlsWebSocketUpgrade.eq_map h]
theorem fits_map (capacity : Nat) (hi lo : B) : f (fits a capacity hi lo) = fits b capacity (f hi) (f lo) := by
  simp only [fits,TlsWebSocketUpgrade.either_map h,TlsWebSocketUpgrade.member_map h,h.and,TlsWebSocketUpgrade.eq_map h]
theorem control_map (opcode : B) : f (control a opcode) = control b (f opcode) := TlsWebSocketUpgrade.member_map h _ _
theorem dataKind_map (opcode : B) : f (dataKind a opcode) = dataKind b (f opcode) := TlsWebSocketUpgrade.member_map h _ _
theorem utfStep_map (s : List B) (x : B) : (utfStep a s x).map f = utfStep b (s.map f) (f x) := by
  simp only [utfStep,List.map_cons,List.map_nil,TlsWebSocketUpgrade.either_map h,h.and,
    TlsWebSocketUpgrade.member_map h,TlsWebSocketUpgrade.get_map h,TlsWebSocketUpgrade.eq_map h]
theorem closeCode_map (hi lo : B) : f (closeCode a hi lo) = closeCode b (f hi) (f lo) := by
  simp only [closeCode,TlsWebSocketUpgrade.either_map h,TlsWebSocketUpgrade.eq_map h,
    TlsWebSocketUpgrade.member_map h,h.and]
theorem start_map (capacity : Nat) : (start a capacity).map f = start b capacity := by
  simp only [start,State.map,TlsWebSocketUpgrade.initial_map h,h.const]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem step_map (capacity : Nat) (s : State B) (x : B) :
    (step a capacity s x).map f = step b capacity (s.map f) (f x) := by
  have dh := congrArg Prod.fst (dec_map h s.high s.low)
  have dl := congrArg Prod.snd (dec_map h s.high s.low)
  have mh := congrArg Prod.fst (dec_map h s.messageHigh s.messageLow)
  have ml := congrArg Prod.snd (dec_map h s.messageHigh s.messageLow)
  simp only [Prod.fst,Prod.snd] at dh dl mh ml
  simp only [step,Event.map,State.map,h.and,h.not,h.const,h.maskBit,
    TlsWebSocketUpgrade.eq_map h,TlsWebSocketUpgrade.member_map h,TlsWebSocketUpgrade.either_map h,
    TlsWebSocketUpgrade.get_map h,control_map h,dataKind_map h,zero_map h,one_map h,
    fits_map h,TlsInner.select_map h,closeCode_map h,utfStep_map h,TlsWebSocketUpgrade.any_map h,
    List.map_cons,List.map_nil,TlsWebSocketUpgrade.choose_map h,TlsWebSocketUpgrade.initial_map h,
    dh,dl,mh,ml]
theorem stateSelect_map (mask : B) (yes no : State B) :
    (stateSelect a mask yes no).map f = stateSelect b (f mask) (yes.map f) (no.map f) := by
  simp only [stateSelect,State.map,TlsWebSocketUpgrade.choose_map h,TlsInner.select_map h]
theorem stateBytes_map (s : State B) : (stateBytes s).map f = stateBytes (s.map f) := by
  simp only [stateBytes,State.map,List.map_append,List.map_cons,List.map_nil]
theorem readState_map (raw : List B) : (readState a raw).map f = readState b (raw.map f) := by
  simp only [readState,State.map,List.map_take,List.map_drop,TlsWebSocketUpgrade.get_map h]
theorem validUpdate_map (s : State B) (value : B) :
    ({s with valid := value}).map f = {s.map f with valid := f value} := rfl
theorem runByte_map (capacity : Nat) (raw : List B) :
    (runByte a capacity raw).map f = runByte b capacity (raw.map f) := by
  let s := readState a (raw.take stateSize)
  let active := get a raw stateSize
  let byte := get a raw (stateSize+1)
  let event := step a capacity s byte
  have mapped := step_map h capacity s byte
  have estate := congrArg Event.state mapped
  have edata := congrArg Event.data mapped
  have econtrol := congrArg Event.controlData mapped
  have estart := congrArg Event.messageStart mapped
  have eframe := congrArg Event.frameDone mapped
  have emessage := congrArg Event.messageDone mapped
  have econtrolDone := congrArg Event.controlDone mapped
  change event.state.map f = _ at estate
  change f event.data = _ at edata
  change f event.controlData = _ at econtrol
  change f event.messageStart = _ at estart
  change f event.frameDone = _ at eframe
  change f event.messageDone = _ at emessage
  change f event.controlDone = _ at econtrolDone
  have selected := stateSelect_map h (eq a active 255) event.state s
  simp only [TlsWebSocketUpgrade.eq_map h,estate] at selected
  have sv := congrArg State.valid selected
  change f (stateSelect a (eq a active 255) event.state s).valid = _ at sv
  unfold runByte
  simp only [List.map_cons,List.map_append,ByteAuth.release_map h,h.and,TlsWebSocketUpgrade.eq_map h,
    TlsWebSocketUpgrade.either_map h,List.map_nil,stateBytes_map h]
  rw [validUpdate_map h]
  simp only [h.and,TlsWebSocketUpgrade.eq_map h,TlsWebSocketUpgrade.either_map h]
  simp only [event,s,active,byte] at selected sv edata econtrol estart eframe emessage econtrolDone
  rw [sv,selected,edata,econtrol,estart,eframe,emessage,econtrolDone]
  simp only [readState_map h,List.map_take,List.map_drop,TlsWebSocketUpgrade.get_map h]
omit h in
theorem compiled_runByte_correct (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(runByte ByteAuth.symbolic capacity raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runByte ByteAuth.symbolic capacity raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runByte ByteAuth.symbolic capacity raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (runByte ByteAuth.concrete capacity (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runByte_map (ByteAuth.evaluationHom assign)]
end Refinement

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decByte_value (x : BitVec 8) :
    decByte ByteAuth.concrete x = BitVec.ofNat 8 (x.toNat+255) := by
  have all : ∀ x : BitVec 8, decByte ByteAuth.concrete x = BitVec.ofNat 8 (x.toNat+255) := by decide +kernel
  exact all x

def wordValue (hi lo : BitVec 8) : Nat := 256*hi.toNat+lo.toNat
theorem dec_value (hi lo : BitVec 8) (positive : 0<wordValue hi lo) :
    wordValue (dec ByteAuth.concrete hi lo).1 (dec ByteAuth.concrete hi lo).2 = wordValue hi lo-1 := by
  have hh : hi.toNat<256 := hi.isLt
  have hl : lo.toNat<256 := lo.isLt
  change wordValue (TlsInner.select ByteAuth.concrete (ByteAuth.eqMask ByteAuth.concrete lo 0)
    (decByte ByteAuth.concrete hi) hi) (decByte ByteAuth.concrete lo) = _
  rw [ByteAuth.eqMask_value]
  by_cases hz : lo=0
  · subst lo
    rw [if_pos rfl,TlsInner.select_accept,decByte_value,decByte_value]
    have hp : 0<hi.toNat := by
      change 0<256*hi.toNat+0 at positive
      omega
    change 256*((hi.toNat+255)%256)+255 = 256*hi.toNat-1
    omega
  · rw [if_neg hz,TlsInner.select_reject,decByte_value]
    have hn : lo.toNat≠0 := by
      intro z;apply hz;apply BitVec.eq_of_toNat_eq;simpa using z
    change 256*hi.toNat+((lo.toNat+255)%256) = 256*hi.toNat+lo.toNat-1
    omega

end TlsMpc.TlsWebSocketFrame
