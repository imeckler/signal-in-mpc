import TlsMpc.Signal.Word64
import TlsMpc.Signal.VarintDecode.Spqr
import TlsMpc.TlsWebSocketFrame

/-! Bounded streaming ChatConnection response validation. Inputs are the private
binary-message activity/start/end masks from the checked WebSocket frame layer.
The expected uint64 request ID, status, body and headers stay shared. Only the
valid/finished/success decisions are eligible for authenticated declassification.

Schema/validation follows chat_websocket.proto and inspected chat/ws.rs/chat.rs.
Uint64 overflow rejects, uint32/type fields truncate like Prost, optional response
submessages merge, scalar duplicates replace, and unknown groups use100/99 depth
budgets. Response strings support UTF8, including Rust Unicode whitespace trimming in headers.
Invalid-state/error cursor refinement is not claimed: invalid outputs are gated.
-/
namespace TlsMpc.TlsChatResponse
open Std.Tactic.BVDecide
open Signal
open TlsWebSocketUpgrade (get either any eq)

def weq (o : Word64.Ops B W) (a : ByteAuth.Ops B) (x : W) (n : Nat) : B := Word64.eq o a x (o.const n)
def wmember (o : Word64.Ops B W) (a : ByteAuth.Ops B) (x : W) (ns : List Nat) : B :=
  any a (ns.map (weq o a x))
def contribution (d : VarintDecode.Spqr.Ops B W) (a : ByteAuth.Ops B) (positions : List B) (byte : B) : W :=
  (List.range 10).foldl (fun out i => d.orWord out (d.payload (a.and (get a positions i) byte) i)) d.zero

structure Header (B : Type) where
  valid : B
  name : B
  colon : B
  started : B
  trailingBad : B
  previous : B
  previous2 : B
def headerInitial (a : ByteAuth.Ops B) : Header B := ⟨a.const 255,a.const 0,a.const 0,a.const 0,a.const 0,a.const 0,a.const 0⟩
def unicodeTrim (a : ByteAuth.Ops B) (previous2 previous x : B) : B :=
  either a (a.and (eq a previous 194) (TlsWebSocketUpgrade.member a x [133,160]))
    (either a (a.and (eq a previous2 225) (a.and (eq a previous 154) (eq a x 128)))
      (either a (a.and (eq a previous2 226)
        (either a (a.and (eq a previous 128) (TlsWebSocketUpgrade.member a x
          ((List.range 11).map (·+128)++[168,169,175])))
          (a.and (eq a previous 129) (eq a x 159))))
        (a.and (eq a previous2 227) (a.and (eq a previous 128) (eq a x 128)))))
def headerStep (a : ByteAuth.Ops B) (h : Header B) (x complete : B) : Header B :=
  let colon := eq a x 58
  let trim := either a (TlsWebSocketUpgrade.member a x [9,10,11,12,13,32])
    (unicodeTrim a h.previous2 h.previous x)
  let badTrim := TlsWebSocketUpgrade.member a x [10,11,12,13]
  let field := TlsWebSocketUpgrade.field a x
  let nameGood := either a (TlsWebSocketUpgrade.token a x) (a.and colon h.name)
  let valueGood := a.and (either a field (TlsWebSocketUpgrade.member a x [9,10,11,12,13,32]))
    (a.not (a.and complete (a.and (a.not trim) h.trailingBad)))
  ⟨a.and h.valid (TlsInner.select a h.colon valueGood nameGood),
   either a h.name (a.and (a.not h.colon) (TlsWebSocketUpgrade.token a x)),
   either a h.colon colon,
   either a h.started (a.and h.colon (a.and complete (a.not trim))),
   either a h.trailingBad (a.and h.colon (a.and complete (a.and h.started badTrim))),
   TlsInner.select a h.colon x h.previous,TlsInner.select a h.colon h.previous h.previous2⟩

def headerSelect (a : ByteAuth.Ops B) (mask : B) (yes no : Header B) : Header B :=
  ⟨TlsInner.select a mask yes.valid no.valid,TlsInner.select a mask yes.name no.name,
   TlsInner.select a mask yes.colon no.colon,TlsInner.select a mask yes.started no.started,
   TlsInner.select a mask yes.trailingBad no.trailingBad,TlsInner.select a mask yes.previous no.previous,
   TlsInner.select a mask yes.previous2 no.previous2⟩

structure State (B W : Type) where
  valid : B
  seen : B
  finished : B
  successful : B
  modes : List B -- key,scalar,length,opaque bytes/fixed
  positions : List B -- ten varint groups
  value : W
  tag : W
  scalarKnown : B
  kinds : List B -- outer response,inner body,inner message,inner header
  inner : B
  responseRemaining : W
  budget : W
  skip : W
  depth : W
  stack : List W
  typeValue : W
  requestPresent : B
  responsePresent : B
  idPresent : B
  id : W
  expected : W
  status : W
  bodyPresent : B
  bodyLength : W
  messagePresent : B
  utf : List B
  header : Header B

structure Event (B W : Type) where
  state : State B W
  bodyData : B
  bodyReset : B
  headerData : B

def initial (o : Word64.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat) (expected : W) : State B W :=
  ⟨a.const 255,a.const 0,a.const 0,a.const 0,TlsWebSocketUpgrade.initial a 3,
   TlsWebSocketUpgrade.initial a 9,o.const 0,o.const 0,a.const 0,List.replicate 4 (a.const 0),
   a.const 0,o.const 0,o.const capacity,o.const 0,o.const 0,List.replicate 100 (o.const 0),
   o.const 0,a.const 0,a.const 0,a.const 0,o.const 0,expected,o.const 0,a.const 0,o.const 0,a.const 0,
   TlsWebSocketUpgrade.initial a 7,headerInitial a⟩

def lookup (o : Word64.Ops B W) (a : ByteAuth.Ops B) (index : W) : Nat → List W → W
  | _,[] => o.const 0
  | i,x::xs => o.select (weq o a index i) x (lookup o a index (i+1) xs)
def writeStack (o : Word64.Ops B W) (a : ByteAuth.Ops B) (mask : B) (index tag : W) (stack : List W) : List W :=
  stack.zipIdx.map (fun (old,i) => o.select (a.and mask (weq o a index i)) tag old)

def step (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (s : State B W) (x : B) : Event B W :=
  let p := fun i => get a s.modes i
  let varint := any a (s.modes.take 3)
  let terminal := a.not (a.maskBit x 7)
  let ended := a.and varint terminal
  let keyDone := a.and (p 0) terminal
  let scalarDone := a.and (p 1) terminal
  let lengthDone := a.and (p 2) terminal
  let decoded := d.orWord s.value (contribution d a s.positions x)
  let kind := o.band decoded (o.const 7)
  let tag := o.shift decoded 3
  let isKind := fun n => weq o a kind n
  let top := weq o a s.depth 0
  let scalar := a.and top (TlsInner.select a s.inner (wmember o a tag [1,2]) (weq o a tag 1))
  let bytesKnown := a.and top (TlsInner.select a s.inner (wmember o a tag [3,4,5]) (wmember o a tag [2,3]))
  let known := either a scalar bytesKnown
  let rightWire := either a (a.and scalar (isKind 0)) (a.and bytesKnown (isKind 2))
  let depthAllowed := o.ule s.depth (o.select s.inner (o.const 98) (o.const 99))
  let endGroup := a.and (a.not top)
    (Word64.eq o a tag (lookup o a (o.sub s.depth (o.const 1)) 0 s.stack))
  let keyGood := a.and (o.ule decoded (o.const 4294967295))
    (a.and (a.not (weq o a tag 0))
      (a.and (o.ule kind (o.const 5))
        (a.and (either a (a.not known) rightWire)
          (TlsInner.select a (isKind 4) endGroup depthAllowed))))
  let budgetNext := o.sub s.budget (o.const 1)
  let responseNext := o.sub s.responseRemaining (o.const 1)
  let available := o.select s.inner responseNext budgetNext
  let longFixed := isKind 1
  let fixed := either a longFixed (isKind 5)
  let fixedLength := o.select longFixed (o.const 8) (o.const 4)
  let fixedGood := o.ule fixedLength available
  let lengthGood := o.ule decoded available
  let outerResponse := get a s.kinds 0
  let enter := a.and lengthDone outerResponse
  let nonempty := a.not (weq o a decoded 0)
  let bytesEnd := a.and (p 3) (weq o a s.skip 1)
  let bytesNext := o.sub s.skip (o.const 1)
  let groupStart := a.and keyDone (isKind 3)
  let groupEnd := a.and keyDone (isKind 4)
  let depthNext := o.select groupStart (o.add s.depth (o.const 1))
    (o.select groupEnd (o.sub s.depth (o.const 1)) s.depth)
  let modes := [either a (a.and (p 0) (a.not terminal))
      (either a scalarDone (either a (a.and lengthDone (either a outerResponse (a.not nonempty)))
        (either a bytesEnd (a.and keyDone (either a (isKind 3) (isKind 4)))))),
    either a (a.and (p 1) (a.not terminal)) (a.and keyDone (isKind 0)),
    either a (a.and (p 2) (a.not terminal)) (a.and keyDone (isKind 2)),
    either a (a.and (p 3) (a.not bytesEnd))
      (either a (a.and lengthDone (a.and (a.not outerResponse) nonempty)) (a.and keyDone fixed))]
  let closeResponse := a.and s.inner (weq o a s.responseRemaining 1)
  let responseComplete := a.and (get a modes 0)
    (a.and (weq o a depthNext 0) (either a ended (p 3)))
  let string := either a (get a s.kinds 2) (get a s.kinds 3)
  let stringByte := a.and (p 3) string
  let utfNext := TlsWebSocketFrame.utfStep a s.utf x
  let headerNext := headerStep a s.header x (get a utfNext 0)
  let stringDoneGood := a.and (get a utfNext 0)
    (either a (a.not (get a s.kinds 3)) (a.and headerNext.valid headerNext.colon))
  let overflow := a.and (get a s.positions 9) (a.not (eq a (a.and x (a.const 254)) 0))
  let valid := a.and s.valid (a.and s.seen
    (a.and (a.not s.finished)
    (a.and (a.not (weq o a s.budget 0))
    (a.and (a.not (a.and varint (either a overflow (a.not (any a s.positions)))))
    (a.and (a.not (a.and keyDone (a.not keyGood)))
    (a.and (a.not (a.and (a.and keyDone fixed) (a.not fixedGood)))
    (a.and (a.not (a.and lengthDone (a.not lengthGood)))
    (a.and (a.not (a.and closeResponse (a.not responseComplete)))
    (a.and (a.not (a.and (a.and lengthDone (get a s.kinds 3)) (a.not nonempty)))
    (a.and (a.not (a.and stringByte (a.not (any a utfNext))))
      (a.not (a.and (a.and bytesEnd string) (a.not stringDoneGood)))))))))))))
  let fieldKinds := [a.and top (a.and (a.not s.inner) (weq o a tag 3)),
    a.and top (a.and s.inner (weq o a tag 4)),a.and top (a.and s.inner (weq o a tag 3)),
    a.and top (a.and s.inner (weq o a tag 5))]
  let knownScalar := a.and scalarDone s.scalarKnown
  let low32 := o.band decoded (o.const 4294967295)
  let bodyReset := a.and lengthDone (get a s.kinds 1)
  let next : State B W := {s with
    valid := valid,modes := modes,
    positions := TlsWebSocketUpgrade.choose a ended (TlsWebSocketUpgrade.initial a 9)
      (TlsWebSocketUpgrade.choose a varint (a.const 0::s.positions.take 9) s.positions),
    value := o.select ended (o.const 0) (o.select varint decoded s.value),
    tag := o.select keyDone tag s.tag,scalarKnown := TlsInner.select a keyDone scalar s.scalarKnown,
    kinds := TlsWebSocketUpgrade.choose a keyDone fieldKinds s.kinds,
    inner := TlsInner.select a enter nonempty (TlsInner.select a closeResponse (a.const 0) s.inner),
    responseRemaining := o.select enter decoded (o.select s.inner responseNext s.responseRemaining),
    budget := budgetNext,
    skip := o.select (a.and keyDone fixed) fixedLength (o.select lengthDone decoded (o.select (p 3) bytesNext s.skip)),
    depth := depthNext,stack := writeStack o a groupStart s.depth tag s.stack,
    typeValue := o.select (a.and knownScalar (a.and (a.not s.inner) (weq o a s.tag 1))) low32 s.typeValue,
    requestPresent := either a s.requestPresent (a.and keyDone (a.and top (a.and (a.not s.inner) (weq o a tag 2)))),
    responsePresent := either a s.responsePresent (a.and keyDone (get a fieldKinds 0)),
    idPresent := either a s.idPresent (a.and knownScalar (a.and s.inner (weq o a s.tag 1))),
    id := o.select (a.and knownScalar (a.and s.inner (weq o a s.tag 1))) decoded s.id,
    status := o.select (a.and knownScalar (a.and s.inner (weq o a s.tag 2))) low32 s.status,
    bodyPresent := either a s.bodyPresent bodyReset,bodyLength := o.select bodyReset decoded s.bodyLength,
    messagePresent := either a s.messagePresent (a.and lengthDone (get a s.kinds 2)),
    utf := TlsWebSocketUpgrade.choose a lengthDone (TlsWebSocketUpgrade.initial a 7)
      (TlsWebSocketUpgrade.choose a stringByte utfNext s.utf),
    header := headerSelect a lengthDone (headerInitial a)
      (headerSelect a (a.and (p 3) (get a s.kinds 3)) headerNext s.header)}
  ⟨next,a.and valid (a.and (p 3) (get a s.kinds 1)),a.and valid bodyReset,
   a.and valid (a.and (p 3) (get a s.kinds 3))⟩

def finish (o : Word64.Ops B W) (a : ByteAuth.Ops B) (s : State B W) : State B W :=
  let complete := a.and s.seen (a.and (a.not s.finished)
    (a.and (get a s.modes 0) (a.and (get a s.positions 0)
    (a.and (a.not s.inner) (a.and (weq o a s.depth 0)
    (a.and (weq o a s.typeValue 2) (a.and (a.not s.requestPresent)
    (a.and s.responsePresent (a.and s.idPresent
    (a.and (Word64.eq o a s.id s.expected)
      (a.and (o.ule (o.const 100) s.status) (o.ule s.status (o.const 999)))))))))))))
  let valid := a.and s.valid complete
  {s with
    valid := valid,finished := a.const 255,
    successful := a.and valid (a.and (o.ule (o.const 200) s.status) (o.ule s.status (o.const 299)))}

def Header.map (f : B → C) (h : Header B) : Header C :=
  ⟨f h.valid,f h.name,f h.colon,f h.started,f h.trailingBad,f h.previous,f h.previous2⟩
def State.map (f : B → C) (fw : W → V) (s : State B W) : State C V := {
  valid := f s.valid,
  seen := f s.seen,
  finished := f s.finished,
  successful := f s.successful,
  modes := s.modes.map f,
  positions := s.positions.map f,
  value := fw s.value,
  tag := fw s.tag,
  scalarKnown := f s.scalarKnown,
  kinds := s.kinds.map f,
  inner := f s.inner,
  responseRemaining := fw s.responseRemaining,
  budget := fw s.budget,
  skip := fw s.skip,
  depth := fw s.depth,
  stack := s.stack.map fw,
  typeValue := fw s.typeValue,
  requestPresent := f s.requestPresent,
  responsePresent := f s.responsePresent,
  idPresent := f s.idPresent,
  id := fw s.id,
  expected := fw s.expected,
  status := fw s.status,
  bodyPresent := f s.bodyPresent,
  bodyLength := fw s.bodyLength,
  messagePresent := f s.messagePresent,
  utf := s.utf.map f,
  header := s.header.map f}
def stateSelect (o : Word64.Ops B W) (a : ByteAuth.Ops B) (mask : B) (yes no : State B W) : State B W := {
  valid := TlsInner.select a mask yes.valid no.valid,
  seen := TlsInner.select a mask yes.seen no.seen,
  finished := TlsInner.select a mask yes.finished no.finished,
  successful := TlsInner.select a mask yes.successful no.successful,
  modes := TlsWebSocketUpgrade.choose a mask yes.modes no.modes,
  positions := TlsWebSocketUpgrade.choose a mask yes.positions no.positions,
  value := o.select mask yes.value no.value,
  tag := o.select mask yes.tag no.tag,
  scalarKnown := TlsInner.select a mask yes.scalarKnown no.scalarKnown,
  kinds := TlsWebSocketUpgrade.choose a mask yes.kinds no.kinds,
  inner := TlsInner.select a mask yes.inner no.inner,
  responseRemaining := o.select mask yes.responseRemaining no.responseRemaining,
  budget := o.select mask yes.budget no.budget,
  skip := o.select mask yes.skip no.skip,
  depth := o.select mask yes.depth no.depth,
  stack := List.zipWith (o.select mask) yes.stack no.stack,
  typeValue := o.select mask yes.typeValue no.typeValue,
  requestPresent := TlsInner.select a mask yes.requestPresent no.requestPresent,
  responsePresent := TlsInner.select a mask yes.responsePresent no.responsePresent,
  idPresent := TlsInner.select a mask yes.idPresent no.idPresent,
  id := o.select mask yes.id no.id,
  expected := o.select mask yes.expected no.expected,
  status := o.select mask yes.status no.status,
  bodyPresent := TlsInner.select a mask yes.bodyPresent no.bodyPresent,
  bodyLength := o.select mask yes.bodyLength no.bodyLength,
  messagePresent := TlsInner.select a mask yes.messagePresent no.messagePresent,
  utf := TlsWebSocketUpgrade.choose a mask yes.utf no.utf,
  header := headerSelect a mask yes.header no.header}

def process (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (s : State B W) (active beginning ending x : B) : Event B W :=
  let fresh := {initial o a capacity s.expected with valid := a.and s.valid (a.not s.seen),seen := a.const 255}
  let started := stateSelect o a (eq a beginning 255) fresh s
  let event := step d o a started x
  let selected := stateSelect o a (eq a active 255) event.state started
  let canonical := (active::beginning::ending::[]).foldl (fun valid mask =>
    a.and valid (either a (eq a mask 0) (eq a mask 255))) (a.const 255)
  let selected := {selected with valid := a.and selected.valid canonical}
  let ended := stateSelect o a (eq a ending 255) (finish o a selected) selected
  let visible := a.and ended.valid (eq a active 255)
  ⟨ended,a.and visible event.bodyData,a.and visible event.bodyReset,a.and visible event.headerData⟩

def headerBytes (h : Header B) : List B := [h.valid,h.name,h.colon,h.started,h.trailingBad,h.previous,h.previous2]
def readHeader (a : ByteAuth.Ops B) (raw : List B) : Header B :=
  ⟨get a raw 0,get a raw 1,get a raw 2,get a raw 3,get a raw 4,get a raw 5,get a raw 6⟩
def stateBytes (o : Word64.Ops B W) (s : State B W) : List B :=
  [s.valid] ++
  [s.seen] ++
  [s.finished] ++
  [s.successful] ++
  s.modes ++
  s.positions ++
  Word64.bytes o s.value ++
  Word64.bytes o s.tag ++
  [s.scalarKnown] ++
  s.kinds ++
  [s.inner] ++
  Word64.bytes o s.responseRemaining ++
  Word64.bytes o s.budget ++
  Word64.bytes o s.skip ++
  Word64.bytes o s.depth ++
  s.stack.flatMap (Word64.bytes o) ++
  Word64.bytes o s.typeValue ++
  [s.requestPresent] ++
  [s.responsePresent] ++
  [s.idPresent] ++
  Word64.bytes o s.id ++
  Word64.bytes o s.expected ++
  Word64.bytes o s.status ++
  [s.bodyPresent] ++
  Word64.bytes o s.bodyLength ++
  [s.messagePresent] ++
  s.utf ++
  headerBytes s.header
def stateSize : Nat := 932
def expectedOffset : Nat := 891
def readState (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : State B W := {
  valid := get a raw 0,
  seen := get a raw 1,
  finished := get a raw 2,
  successful := get a raw 3,
  modes := (raw.drop 4).take 4,
  positions := (raw.drop 8).take 10,
  value := o.pack ((raw.drop 18).take 8),
  tag := o.pack ((raw.drop 26).take 8),
  scalarKnown := get a raw 34,
  kinds := (raw.drop 35).take 4,
  inner := get a raw 39,
  responseRemaining := o.pack ((raw.drop 40).take 8),
  budget := o.pack ((raw.drop 48).take 8),
  skip := o.pack ((raw.drop 56).take 8),
  depth := o.pack ((raw.drop 64).take 8),
  stack := (List.range 100).map (fun i => o.pack ((raw.drop (72+8*i)).take 8)),
  typeValue := o.pack ((raw.drop 872).take 8),
  requestPresent := get a raw 880,
  responsePresent := get a raw 881,
  idPresent := get a raw 882,
  id := o.pack ((raw.drop 883).take 8),
  expected := o.pack ((raw.drop 891).take 8),
  status := o.pack ((raw.drop 899).take 8),
  bodyPresent := get a raw 907,
  bodyLength := o.pack ((raw.drop 908).take 8),
  messagePresent := get a raw 916,
  utf := (raw.drop 917).take 8,
  header := readHeader a ((raw.drop 925).take 7)}

@[irreducible] def runByte (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (raw : List B) : List B :=
  let event := process d o a capacity (readState o a (raw.take stateSize))
    (get a raw stateSize) (get a raw (stateSize+1)) (get a raw (stateSize+2)) (get a raw (stateSize+3))
  [event.state.valid,event.state.finished,event.state.successful,event.bodyData,event.bodyReset,event.headerData] ++
    stateBytes o event.state

def Event.map (f : B → C) (fw : W → V) (e : Event B W) : Event C V :=
  ⟨e.state.map f fw,f e.bodyData,f e.bodyReset,f e.headerData⟩

section ByteMapping
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (ha : ByteAuth.Hom a b f)
include ha
theorem unicodeTrim_map (p2 p x : B) : f (unicodeTrim a p2 p x) = unicodeTrim b (f p2) (f p) (f x) := by
  simp only [unicodeTrim,TlsWebSocketUpgrade.either_map ha,TlsWebSocketUpgrade.eq_map ha,
    TlsWebSocketUpgrade.member_map ha,ha.and]
theorem headerInitial_map : (headerInitial a).map f = headerInitial b := by
  simp only [headerInitial,Header.map,ha.const]
theorem headerStep_map (h : Header B) (x complete : B) :
    (headerStep a h x complete).map f = headerStep b (h.map f) (f x) (f complete) := by
  simp only [headerStep,Header.map,ha.and,ha.not,TlsInner.select_map ha,
    TlsWebSocketUpgrade.eq_map ha,TlsWebSocketUpgrade.either_map ha,TlsWebSocketUpgrade.member_map ha,
    TlsWebSocketUpgrade.field_map ha,TlsWebSocketUpgrade.token_map ha,unicodeTrim_map ha]
theorem headerSelect_map (mask : B) (yes no : Header B) :
    (headerSelect a mask yes no).map f = headerSelect b (f mask) (yes.map f) (no.map f) := by
  simp only [headerSelect,Header.map,TlsInner.select_map ha]
theorem headerBytes_map (h : Header B) : (headerBytes h).map f = headerBytes (h.map f) := by
  simp only [headerBytes,Header.map,List.map_cons,List.map_nil]
theorem readHeader_map (raw : List B) : (readHeader a raw).map f = readHeader b (raw.map f) := by
  simp only [readHeader,Header.map,TlsWebSocketUpgrade.get_map ha]
end ByteMapping

section Mapping
variable {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops C V}
  {o : Word64.Ops B W} {o' : Word64.Ops C V} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops C}
  {f : B → C} {fw : W → V}
  (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include ho ha in
theorem weq_map (x : W) (n : Nat) : f (weq o a x n) = weq o' a' (fw x) n := by
  simp only [weq,Word64.eq_map ho ha,ho.const]
include ho ha in
theorem wmember_map (x : W) (ns : List Nat) : f (wmember o a x ns) = wmember o' a' (fw x) ns := by
  simp only [wmember,TlsWebSocketUpgrade.any_map ha,List.map_map,Function.comp_def,weq_map ho ha]
include hd ha in
theorem contribution_fold_map (positions : List B) (byte : B) (indices : List Nat) (out : W) :
    fw (indices.foldl (fun out i => d.orWord out (d.payload (a.and (get a positions i) byte) i)) out) =
      indices.foldl (fun out i => d'.orWord out (d'.payload (a'.and (get a' (positions.map f) i) (f byte)) i)) (fw out) := by
  induction indices generalizing out with
  | nil => rfl
  | cons i indices ih => simp only [List.foldl_cons,ih,hd.orWord,hd.payload,ha.and,TlsWebSocketUpgrade.get_map ha]
include hd ha in
theorem contribution_map (positions : List B) (byte : B) :
    fw (contribution d a positions byte) = contribution d' a' (positions.map f) (f byte) := by
  simp only [contribution,contribution_fold_map hd ha,hd.zero]
include ho ha in
theorem lookup_map (index : W) (start : Nat) (rows : List W) :
    fw (lookup o a index start rows) = lookup o' a' (fw index) start (rows.map fw) := by
  induction rows generalizing start with
  | nil => simp only [lookup,List.map_nil,ho.const]
  | cons row rest ih => simp only [lookup,List.map_cons,ho.select,weq_map ho ha,ih]
include ho ha in
theorem writeStack_map (mask : B) (index tag : W) (stack : List W) :
    (writeStack o a mask index tag stack).map fw = writeStack o' a' (f mask) (fw index) (fw tag) (stack.map fw) := by
  simp only [writeStack,List.zipIdx_map,List.map_map,Function.comp_def,ho.select,ha.and,weq_map ho ha,
    Prod.map_fst,Prod.map_snd,id_eq]
include ho ha in
theorem initial_map (capacity : Nat) (expected : W) :
    (initial o a capacity expected).map f fw = initial o' a' capacity (fw expected) := by
  simp only [initial,State.map,TlsWebSocketUpgrade.initial_map ha,ha.const,ho.const,
    List.map_replicate,headerInitial_map ha]
include ho ha in
theorem stateSelect_map (mask : B) (yes no : State B W) :
    (stateSelect o a mask yes no).map f fw = stateSelect o' a' (f mask) (yes.map f fw) (no.map f fw) := by
  simp only [stateSelect,State.map,TlsInner.select_map ha,TlsWebSocketUpgrade.choose_map ha,
    ho.select,List.map_zipWith,List.zipWith_map,headerSelect_map ha]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
include hd ho ha in
theorem step_map (s : State B W) (x : B) :
    (step d o a s x).map f fw = step d' o' a' (s.map f fw) (f x) := by
  have hm := headerStep_map ha s.header x (get a (TlsWebSocketFrame.utfStep a s.utf x) 0)
  have hv := congrArg Header.valid hm
  have hc := congrArg Header.colon hm
  change f (headerStep a s.header x (get a (TlsWebSocketFrame.utfStep a s.utf x) 0)).valid = _ at hv
  change f (headerStep a s.header x (get a (TlsWebSocketFrame.utfStep a s.utf x) 0)).colon = _ at hc
  simp only [TlsWebSocketUpgrade.get_map ha,TlsWebSocketFrame.utfStep_map ha] at hv hc
  simp only [step,Event.map,State.map,ha.and,ha.not,ha.maskBit,ha.const,hd.orWord,
    ho.const,ho.band,ho.shift,ho.ule,ho.select,ho.sub,ho.add,
    TlsWebSocketUpgrade.get_map ha,TlsWebSocketUpgrade.any_map ha,List.map_take,
    contribution_map hd ha,weq_map ho ha,wmember_map ho ha,TlsWebSocketUpgrade.either_map ha,
    TlsInner.select_map ha,Word64.eq_map ho ha,lookup_map ho ha,TlsWebSocketFrame.utfStep_map ha,
    headerStep_map ha,TlsWebSocketUpgrade.eq_map ha,List.map_cons,List.map_nil,
    TlsWebSocketUpgrade.choose_map ha,TlsWebSocketUpgrade.initial_map ha,writeStack_map ho ha,
    headerSelect_map ha,headerInitial_map ha,hv,hc]
include ho ha in
theorem finish_map (s : State B W) : (finish o a s).map f fw = finish o' a' (s.map f fw) := by
  simp only [finish,State.map,ha.and,ha.not,ha.const,TlsWebSocketUpgrade.get_map ha,weq_map ho ha,
    Word64.eq_map ho ha,ho.ule,ho.const]
include ho in
theorem stackBytes_map (stack : List W) :
    (stack.flatMap (Word64.bytes o)).map f = (stack.map fw).flatMap (Word64.bytes o') := by
  induction stack with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.map_cons,Word64.bytes_map ho,ih]
include ho ha in
theorem stateBytes_map (s : State B W) :
    (stateBytes o s).map f = stateBytes o' (s.map f fw) := by
  simp only [stateBytes,State.map,List.map_append,List.map_cons,List.map_nil,Word64.bytes_map ho,
    stackBytes_map ho,headerBytes_map ha]
include ho ha in
theorem readState_map (raw : List B) :
    (readState o a raw).map f fw = readState o' a' (raw.map f) := by
  simp only [readState,State.map,TlsWebSocketUpgrade.get_map ha,List.map_take,List.map_drop,
    ho.pack,List.map_map,Function.comp_def,readHeader_map ha]
theorem flagsUpdate_map (s : State B W) (valid seen : B) :
    ({s with valid := valid,seen := seen}).map f fw = {s.map f fw with valid := f valid,seen := f seen} := rfl
theorem validUpdate_map (s : State B W) (valid : B) :
    ({s with valid := valid}).map f fw = {s.map f fw with valid := f valid} := rfl
include hd ho ha in
theorem process_map (capacity : Nat) (s : State B W) (active beginning ending x : B) :
    (process d o a capacity s active beginning ending x).map f fw =
      process d' o' a' capacity (s.map f fw) (f active) (f beginning) (f ending) (f x) := by
  let fresh := {initial o a capacity s.expected with valid := a.and s.valid (a.not s.seen),seen := a.const 255}
  let started := stateSelect o a (eq a beginning 255) fresh s
  let event := step d o a started x
  let base := stateSelect o a (eq a active 255) event.state started
  let canonical := (active::beginning::ending::[]).foldl (fun valid mask =>
    a.and valid (either a (eq a mask 0) (eq a mask 255))) (a.const 255)
  let selected := {base with valid := a.and base.valid canonical}
  let ended := stateSelect o a (eq a ending 255) (finish o a selected) selected
  have fr : fresh.map f fw = {initial o' a' capacity (fw s.expected) with
      valid := a'.and (f s.valid) (a'.not (f s.seen)),seen := a'.const 255} := by
    dsimp only [fresh]
    rw [flagsUpdate_map,initial_map ho ha]
    simp only [ha.and,ha.not,ha.const]
  have st := stateSelect_map ho ha (eq a beginning 255) fresh s
  rw [TlsWebSocketUpgrade.eq_map ha,fr] at st
  have ev := step_map hd ho ha started x
  rw [show started.map f fw = _ from st] at ev
  have es := congrArg Event.state ev
  have eb := congrArg Event.bodyData ev
  have er := congrArg Event.bodyReset ev
  have eh := congrArg Event.headerData ev
  change event.state.map f fw = _ at es
  change f event.bodyData = _ at eb
  change f event.bodyReset = _ at er
  change f event.headerData = _ at eh
  have ba := stateSelect_map ho ha (eq a active 255) event.state started
  rw [TlsWebSocketUpgrade.eq_map ha,es,show started.map f fw = _ from st] at ba
  have bv := congrArg State.valid ba
  change f base.valid = _ at bv
  have ca : f canonical = (f active::f beginning::f ending::[]).foldl (fun valid mask =>
      a'.and valid (either a' (eq a' mask 0) (eq a' mask 255))) (a'.const 255) := by
    dsimp only [canonical]
    simp only [List.foldl_cons,List.foldl_nil,ha.and,ha.const,TlsWebSocketUpgrade.either_map ha,TlsWebSocketUpgrade.eq_map ha]
  have se := validUpdate_map (f:=f) (fw:=fw) base (a.and base.valid canonical)
  change selected.map f fw = _ at se
  rw [ha.and,bv,ca,show base.map f fw = _ from ba] at se
  have en := stateSelect_map ho ha (eq a ending 255) (finish o a selected) selected
  rw [TlsWebSocketUpgrade.eq_map ha,finish_map ho ha,show selected.map f fw = _ from se] at en
  have env := congrArg State.valid en
  change f ended.valid = _ at env
  change (⟨ended.map f fw,f (a.and (a.and ended.valid (eq a active 255)) event.bodyData),
    f (a.and (a.and ended.valid (eq a active 255)) event.bodyReset),
    f (a.and (a.and ended.valid (eq a active 255)) event.headerData)⟩ : Event C V) = _
  rw [show ended.map f fw = _ from en,ha.and,ha.and,env,TlsWebSocketUpgrade.eq_map ha,eb,
    ha.and,ha.and,env,TlsWebSocketUpgrade.eq_map ha,er,ha.and,ha.and,env,TlsWebSocketUpgrade.eq_map ha,eh]
  rfl
include hd ho ha in
theorem runByte_map (capacity : Nat) (raw : List B) :
    (runByte d o a capacity raw).map f = runByte d' o' a' capacity (raw.map f) := by
  have ev := process_map hd ho ha capacity (readState o a (raw.take stateSize))
    (get a raw stateSize) (get a raw (stateSize+1)) (get a raw (stateSize+2)) (get a raw (stateSize+3))
  simp only [readState_map ho ha,List.map_take,TlsWebSocketUpgrade.get_map ha] at ev
  have es := congrArg Event.state ev
  have valid := congrArg (fun e => e.state.valid) ev
  have finished := congrArg (fun e => e.state.finished) ev
  have success := congrArg (fun e => e.state.successful) ev
  have body := congrArg Event.bodyData ev
  have reset := congrArg Event.bodyReset ev
  have header := congrArg Event.headerData ev
  change (process d o a capacity (readState o a (raw.take stateSize))
    (get a raw stateSize) (get a raw (stateSize+1)) (get a raw (stateSize+2)) (get a raw (stateSize+3))).state.map f fw = _ at es
  simp only [Event.map,State.map] at valid finished success body reset header
  unfold runByte
  simp only [List.map_append,List.map_cons,List.map_nil,stateBytes_map ho ha]
  rw [valid,finished,success,body,reset,header,es]
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

end TlsMpc.TlsChatResponse
