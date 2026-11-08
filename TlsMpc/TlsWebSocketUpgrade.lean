import TlsMpc.TlsPrivateSeal

/-! Bounded, oblivious HTTP/1.1 WebSocket response validator. Header names and
tokens are ASCII case-insensitive, critical fields are unique, and additional
syntactically valid headers are permitted. No extension/subprotocol is offered.
The public expected accept value derives only from the fresh public client key.
All state, completion and consumed-length fields stay shared. -/
namespace TlsMpc.TlsWebSocketUpgrade
open Std.Tactic.BVDecide

def get (a : ByteAuth.Ops B) (xs : List B) (i : Nat) : B := xs[i]?.getD (a.const 0)
def eq (a : ByteAuth.Ops B) (x : B) (n : Nat) : B := ByteAuth.eqMask a x (a.const n)
def either (a : ByteAuth.Ops B) (x y : B) : B := a.not (a.and (a.not x) (a.not y))
def any (a : ByteAuth.Ops B) (xs : List B) : B := xs.foldl (either a) (a.const 0)
def member (a : ByteAuth.Ops B) (x : B) (ns : List Nat) : B := any a (ns.map (eq a x))
def ows (a : ByteAuth.Ops B) (x : B) : B := member a x [9,32]
def token (a : ByteAuth.Ops B) (x : B) : B := member a x
  ((List.range 10).map (·+48) ++ (List.range 26).map (·+65) ++
   (List.range 26).map (·+97) ++ [33,35,36,37,38,39,42,43,45,46,94,95,96,124,126])
def lower (a : ByteAuth.Ops B) (x : B) : B :=
  a.xor x (a.and (member a x ((List.range 26).map (·+65))) (a.const 32))
def field (a : ByteAuth.Ops B) (x : B) : B :=
  either a (a.maskBit x 7) (member a x (9::(List.range 95).map (·+32)))
def bytes (s : String) : List Nat := s.toUTF8.toList.map UInt8.toNat
def initial (a : ByteAuth.Ops B) (n : Nat) : List B := a.const 255 :: List.replicate n (a.const 0)
def advance (a : ByteAuth.Ops B) (pattern state : List B) (x : B) : List B :=
  a.const 0 :: (List.zipWith (fun old wanted => a.and old (ByteAuth.eqMask a x wanted)) state pattern)
def literal (a : ByteAuth.Ops B) (s : String) : List B := (bytes s).map a.const
theorem literal_length (a : ByteAuth.Ops B) (s : String) : (literal a s).length = (bytes s).length := by simp [literal]
def choose (a : ByteAuth.Ops B) (mask : B) (yes no : List B) : List B :=
  List.zipWith (TlsInner.select a mask) yes no
def getName (xs : List (List B)) (i : Nat) : List B := xs[i]?.getD []
def namePatterns : List String := ["upgrade","connection","sec-websocket-accept","sec-websocket-extensions","sec-websocket-protocol"]

structure TokenState (B : Type) where
  progress : List B
  nonempty : B
  trailing : B
  found : B
  valid : B

def tokenInitial (a : ByteAuth.Ops B) (n : Nat) : TokenState B :=
  ⟨initial a n,a.const 0,a.const 0,a.const 0,a.const 255⟩
def tokenStep (a : ByteAuth.Ops B) (pattern : List B) (s : TokenState B) (x : B) : TokenState B :=
  let ws := ows a x
  let comma := eq a x 44
  let char := token a x
  let completed := get a s.progress pattern.length
  let ending := either a ws comma
  let found := either a s.found (a.and ending completed)
  let valid := a.and s.valid (either a (a.and char (a.not s.trailing))
    (either a ws (a.and comma s.nonempty)))
  ⟨choose a comma (initial a pattern.length)
      (choose a ws s.progress (advance a pattern s.progress (lower a x))),
   TlsInner.select a comma (a.const 0) (either a s.nonempty char),
   TlsInner.select a comma (a.const 0) (either a s.trailing (a.and ws s.nonempty)),found,valid⟩
def tokenFinish (a : ByteAuth.Ops B) (n : Nat) (s : TokenState B) : B :=
  a.and s.valid (a.and s.nonempty (either a s.found (get a s.progress n)))

def tokenSelect (a : ByteAuth.Ops B) (mask : B) (yes no : TokenState B) : TokenState B :=
  ⟨choose a mask yes.progress no.progress,TlsInner.select a mask yes.nonempty no.nonempty,
   TlsInner.select a mask yes.trailing no.trailing,TlsInner.select a mask yes.found no.found,
   TlsInner.select a mask yes.valid no.valid⟩

structure State (B : Type) where
  -- phases: status prefix/reason, status LF, header name, value, line LF,
  -- final LF, completed. Exactly one phase is active on reachable states.
  phases : List B
  valid : B
  status : List B
  reason : B
  name : List (List B)
  nameNonempty : B
  kinds : List B
  seen : List B
  upgrade : TokenState B
  connection : TokenState B
  accept : List B
  acceptLeading : B
  acceptTrailing : B
  consumedHi : B
  consumedLo : B

def start (a : ByteAuth.Ops B) : State B :=
  ⟨initial a 6,a.const 255,initial a 12,a.const 0,
   namePatterns.map (fun s => initial a (bytes s).length),a.const 0,
   List.replicate 5 (a.const 0),List.replicate 5 (a.const 0),
   tokenInitial a 9,tokenInitial a 7,initial a 28,a.const 255,a.const 0,a.const 0,a.const 0⟩

def step (a : ByteAuth.Ops B) (expected : List B) (offset : Nat) (s : State B) (x : B) : State B :=
  let p := fun i => get a s.phases i
  let cr := eq a x 13
  let lf := eq a x 10
  let colon := eq a x 58
  let ws := ows a x
  let completeStatus := get a s.status 12
  let statusReason := either a s.reason (a.and completeStatus (eq a x 32))
  let nameEnd := a.and (p 2) (a.and colon s.nameNonempty)
  let nameHits := (List.range 5).map (fun i => get a (getName s.name i) (bytes (namePatterns[i]?.getD "")).length)
  let duplicated := any a ((List.range 5).map (fun i => a.and (get a s.seen i) (get a nameHits i)))
  let forbidden := either a (get a nameHits 3) (get a nameHits 4)
  let emptyEnd := a.and (p 2) (a.and cr (a.not s.nameNonempty))
  let valueEnd := a.and (p 3) cr
  let acceptComplete := get a s.accept 28
  let acceptNext := choose a (a.and ws (either a s.acceptLeading acceptComplete)) s.accept
    (advance a expected s.accept x)
  let acceptValid := get a acceptNext 28
  let valueValid := a.and (a.not (a.and (get a s.kinds 0)
      (a.not (tokenFinish a 9 s.upgrade))))
    (a.and (a.not (a.and (get a s.kinds 1) (a.not (tokenFinish a 7 s.connection))))
      (a.not (a.and (get a s.kinds 2) (a.not acceptComplete))))
  let allSeen := a.and (get a s.seen 0) (a.and (get a s.seen 1) (get a s.seen 2))
  let statusValid := either a
    (a.and cr s.reason)
    (either a (a.and statusReason (field a x))
      (any a (advance a (literal a "HTTP/1.1 101") s.status x)))
  let valid := a.and s.valid (a.and
    (a.not (a.and (p 0) (a.not statusValid)))
    (a.and (a.not (a.and (either a (p 1) (either a (p 4) (p 5))) (a.not lf)))
    (a.and (a.not (a.and (p 2) (a.not (either a (token a x) (either a nameEnd emptyEnd)))))
    (a.and (a.not (a.and nameEnd (either a duplicated forbidden)))
    (a.and (a.not (a.and (p 3) (a.not (either a cr (field a x)))))
    (a.and (a.not (a.and valueEnd (a.not valueValid)))
      (a.not (a.and (p 5) (a.not allSeen)))))))))
  let resetName := a.and (p 4) lf
  let names := (List.range 5).map (fun i =>
    let pattern := literal a (namePatterns[i]?.getD "")
    let old := getName s.name i
    choose a resetName (initial a pattern.length)
      (choose a (p 2) (advance a pattern old (lower a x)) old))
  let nextSeen := (List.range 5).map (fun i => either a (get a s.seen i) (a.and nameEnd (get a nameHits i)))
  let phases := [a.and (p 0) (a.not cr),a.and (p 0) cr,
    either a (a.and (p 1) lf) (either a resetName (a.and (p 2) (a.not (either a nameEnd emptyEnd)))),
    either a nameEnd (a.and (p 3) (a.not cr)),valueEnd,emptyEnd,
    either a (p 6) (a.and (p 5) lf)]
  let final := a.and (p 5) lf
  {s with
    phases := phases,valid := valid,status := choose a (p 0) (advance a (literal a "HTTP/1.1 101") s.status x) s.status,
    reason := TlsInner.select a (p 0) statusReason s.reason,
    name := names,nameNonempty := TlsInner.select a resetName (a.const 0)
      (either a s.nameNonempty (a.and (p 2) (token a x))),
    kinds := choose a nameEnd nameHits s.kinds,seen := nextSeen,
    upgrade := tokenSelect a nameEnd (tokenInitial a 9)
      (tokenSelect a (p 3) (tokenStep a (literal a "websocket") s.upgrade x) s.upgrade),
    connection := tokenSelect a nameEnd (tokenInitial a 7)
      (tokenSelect a (p 3) (tokenStep a (literal a "upgrade") s.connection x) s.connection),
    accept := choose a nameEnd (initial a 28) (choose a (p 3) acceptNext s.accept),
    acceptLeading := TlsInner.select a nameEnd (a.const 255)
      (TlsInner.select a (p 3) (a.and s.acceptLeading ws) s.acceptLeading),
    acceptTrailing := TlsInner.select a nameEnd (a.const 0)
      (TlsInner.select a (p 3) (either a s.acceptTrailing (a.and acceptValid ws)) s.acceptTrailing),
    consumedHi := TlsInner.select a final (a.const ((offset+1)/256)) s.consumedHi,
    consumedLo := TlsInner.select a final (a.const (offset+1)) s.consumedLo}

def stateSelect (a : ByteAuth.Ops B) (mask : B) (yes no : State B) : State B :=
  ⟨choose a mask yes.phases no.phases,TlsInner.select a mask yes.valid no.valid,
   choose a mask yes.status no.status,TlsInner.select a mask yes.reason no.reason,
   List.zipWith (choose a mask) yes.name no.name,TlsInner.select a mask yes.nameNonempty no.nameNonempty,
   choose a mask yes.kinds no.kinds,choose a mask yes.seen no.seen,
   tokenSelect a mask yes.upgrade no.upgrade,tokenSelect a mask yes.connection no.connection,
   choose a mask yes.accept no.accept,TlsInner.select a mask yes.acceptLeading no.acceptLeading,
   TlsInner.select a mask yes.acceptTrailing no.acceptTrailing,
   TlsInner.select a mask yes.consumedHi no.consumedHi,TlsInner.select a mask yes.consumedLo no.consumedLo⟩

/-- The mask at index i is255 precisely for i < private length; equality at
capacity contributes bounds acceptance but no active data byte. -/
def activity (a : ByteAuth.Ops B) (hi lo : B) : Nat → Nat → B × List B
  | offset,0 => (TlsPrivateSeal.eqLength a hi lo offset,[])
  | offset,n+1 =>
    let rest := activity a hi lo (offset+1) n
    (either a (TlsPrivateSeal.eqLength a hi lo offset) rest.1,rest.1::rest.2)

def feedLoop (a : ByteAuth.Ops B) (expected : List B) :
    Nat → State B → List B → List B → State B × List B
  | _,s,[],_ => (s,[])
  | _,s,_,[] => (s,[])
  | offset,s,x::xs,active::masks =>
    let ws := a.and active (get a s.phases 6)
    let next := stateSelect a active (step a expected offset s x) s
    let rest := feedLoop a expected (offset+1) next xs masks
    (rest.1,ws::rest.2)

/-- Feed an opaque chunk, retaining every coalesced WebSocket byte through its
same-position activity mask. A following frame parser consumes these masks;
the header boundary and exact chunk length never leave the circuit. -/
def feed (a : ByteAuth.Ops B) (expected : List B) (s : State B) (valid hi lo : B)
    (data : List B) : State B × List B :=
  let masks := activity a hi lo 0 data.length
  let result := feedLoop a expected 0 s data masks.2
  let accepted := a.and result.1.valid (a.and masks.1 (eq a valid 255))
  ({result.1 with valid := accepted},ByteAuth.release a accepted result.2)

def TokenState.map (f : B → C) (s : TokenState B) : TokenState C :=
  ⟨s.progress.map f,f s.nonempty,f s.trailing,f s.found,f s.valid⟩
def State.map (f : B → C) (s : State B) : State C :=
  ⟨s.phases.map f,f s.valid,s.status.map f,f s.reason,s.name.map (List.map f),f s.nameNonempty,
   s.kinds.map f,s.seen.map f,s.upgrade.map f,s.connection.map f,s.accept.map f,
   f s.acceptLeading,f s.acceptTrailing,f s.consumedHi,f s.consumedLo⟩

def tokenBytes (s : TokenState B) : List B := s.progress ++ [s.nonempty,s.trailing,s.found,s.valid]
def stateBytes (s : State B) : List B :=
  s.phases ++ [s.valid] ++ s.status ++ [s.reason] ++ s.name.flatten ++ [s.nameNonempty] ++
  s.kinds ++ s.seen ++ tokenBytes s.upgrade ++ tokenBytes s.connection ++ s.accept ++
  [s.acceptLeading,s.acceptTrailing,s.consumedHi,s.consumedLo]
def nameSize : Nat := (namePatterns.map (fun s => (bytes s).length+1)).sum
def stateSize : Nat := 7+1+13+1+nameSize+1+5+5+14+12+29+4
def readToken (a : ByteAuth.Ops B) (n offset : Nat) (raw : List B) : TokenState B :=
  ⟨(raw.drop offset).take (n+1),get a raw (offset+n+1),get a raw (offset+n+2),
   get a raw (offset+n+3),get a raw (offset+n+4)⟩
def readNames (raw : List B) : Nat → List String → List (List B)
  | _,[] => []
  | offset,pattern::rest =>
    let size := (bytes pattern).length+1
    (raw.drop offset).take size :: readNames raw (offset+size) rest
def readState (a : ByteAuth.Ops B) (raw : List B) : State B :=
  let k := 22+nameSize
  ⟨raw.take 7,get a raw 7,(raw.drop 8).take 13,get a raw 21,readNames raw 22 namePatterns,get a raw k,
   (raw.drop (k+1)).take 5,(raw.drop (k+6)).take 5,readToken a 9 (k+11) raw,
   readToken a 7 (k+25) raw,(raw.drop (k+37)).take 29,get a raw (k+66),get a raw (k+67),
   get a raw (k+68),get a raw (k+69)⟩

/-- Internal pinned evaluator format. Exposes only protocol validity/completion;
the caller must authenticate these fields before interpreting its shared state.
All coalesced bytes remain in the original private chunk, selected by output
activity masks for the subsequent WebSocket frame machine. -/
@[irreducible] def run (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : List B :=
  let s := readState a (raw.take stateSize)
  let expected := (raw.drop stateSize).take 28
  let offset := stateSize+28
  let result := feed a expected s (get a raw offset) (get a raw (offset+1))
    (get a raw (offset+2)) ((raw.drop (offset+3)).take capacity)
  result.1.valid :: get a result.1.phases 6 :: (stateBytes result.1 ++ result.2)

/-- Fixed-cost per-byte interface for a public-capacity host loop. An active
mask comes from the authenticated chunk's private length comparison, never a
host reconstruction. Using a separately pinned byte function avoids repeatedly
expanding a large symbolic state machine into an unbounded expression tree. -/
@[irreducible] def runByte (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let s := readState a (raw.take stateSize)
  let expected := (raw.drop stateSize).take 28
  let active := get a raw (stateSize+28)
  let x := get a raw (stateSize+29)
  let next := stateSelect a (eq a active 255) (step a expected 0 s x) s
  let valid := a.and next.valid (either a (eq a active 0) (eq a active 255))
  let result := {next with valid := valid}
  result.valid :: get a result.phases 6 ::
    a.and valid (a.and active (get a s.phases 6)) :: stateBytes result

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (h : ByteAuth.Hom a b f)
include h
theorem get_map (xs : List B) (i : Nat) : f (get a xs i) = get b (xs.map f) i := by
  simp only [get,List.getElem?_map]
  cases xs[i]? <;> simp [h.const]
theorem getName_map (xs : List (List B)) (i : Nat) :
    (getName xs i).map f = getName (xs.map (List.map f)) i := by
  simp only [getName,List.getElem?_map]
  cases xs[i]? <;> rfl
theorem tokenBytes_map (s : TokenState B) : (tokenBytes s).map f = tokenBytes (s.map f) := by
  simp only [tokenBytes,TokenState.map,List.map_append,List.map_cons,List.map_nil]
theorem stateBytes_map (s : State B) : (stateBytes s).map f = stateBytes (s.map f) := by
  simp only [stateBytes,State.map,List.map_append,List.map_cons,List.map_nil,List.map_flatten,
    tokenBytes_map h]
theorem readToken_map (n offset : Nat) (raw : List B) :
    (readToken a n offset raw).map f = readToken b n offset (raw.map f) := by
  simp only [readToken,TokenState.map,List.map_take,List.map_drop,get_map h]
theorem readNames_map (raw : List B) (offset : Nat) (patterns : List String) :
    (readNames raw offset patterns).map (List.map f) = readNames (raw.map f) offset patterns := by
  induction patterns generalizing offset with
  | nil => rfl
  | cons pat pats ih => simp only [readNames,List.map_cons,List.map_take,List.map_drop,ih]
theorem readState_map (raw : List B) : (readState a raw).map f = readState b (raw.map f) := by
  simp only [readState,State.map,List.map_take,List.map_drop,get_map h,readToken_map h,readNames_map h]
theorem eq_map (x : B) (n : Nat) : f (eq a x n) = eq b (f x) n := by
  simp only [eq,ByteAuth.eqMask_map h,h.const]
theorem either_map (x y : B) : f (either a x y) = either b (f x) (f y) := by
  simp only [either,h.not,h.and]
theorem any_fold_map (xs : List B) (acc : B) :
    f (xs.foldl (either a) acc) = (xs.map f).foldl (either b) (f acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,List.map_cons,ih,either_map h]
theorem any_map (xs : List B) : f (any a xs) = any b (xs.map f) := by
  simp only [any,any_fold_map h,h.const]
theorem member_map (x : B) (ns : List Nat) : f (member a x ns) = member b (f x) ns := by
  simp only [member,any_map h,List.map_map,Function.comp_def,eq_map h]
theorem ows_map (x : B) : f (ows a x) = ows b (f x) := member_map h x _
theorem token_map (x : B) : f (token a x) = token b (f x) := member_map h x _
theorem lower_map (x : B) : f (lower a x) = lower b (f x) := by
  simp only [lower,h.xor,h.and,member_map h,h.const]
theorem field_map (x : B) : f (field a x) = field b (f x) := by
  simp only [field,either_map h,h.maskBit,member_map h]
theorem initial_map (n : Nat) : (initial a n).map f = initial b n := by
  simp only [initial,List.map_cons,List.map_replicate,h.const]
theorem literal_map (s : String) : (literal a s).map f = literal b s := by
  simp only [literal,List.map_map,Function.comp_def,h.const]
theorem advance_map (pattern state : List B) (x : B) :
    (advance a pattern state x).map f = advance b (pattern.map f) (state.map f) (f x) := by
  simp only [advance,List.map_cons,h.const,List.map_zipWith]
  congr 1
  simp only [List.zipWith_map,Function.comp_def,h.and,ByteAuth.eqMask_map h]
theorem choose_map (mask : B) (yes no : List B) :
    (choose a mask yes no).map f = choose b (f mask) (yes.map f) (no.map f) := by
  simp only [choose,List.map_zipWith,List.zipWith_map,Function.comp_def,TlsInner.select_map h]
theorem tokenInitial_map (n : Nat) : (tokenInitial a n).map f = tokenInitial b n := by
  simp only [tokenInitial,TokenState.map,initial_map h,h.const]
theorem tokenStep_map (pattern : List B) (s : TokenState B) (x : B) :
    (tokenStep a pattern s x).map f = tokenStep b (pattern.map f) (s.map f) (f x) := by
  simp only [tokenStep,TokenState.map,ows_map h,eq_map h,token_map h,get_map h,either_map h,
    h.and,h.not,choose_map h,initial_map h,List.length_map,advance_map h,lower_map h,TlsInner.select_map h,h.const]
theorem tokenFinish_map (n : Nat) (s : TokenState B) :
    f (tokenFinish a n s) = tokenFinish b n (s.map f) := by
  simp only [tokenFinish,TokenState.map,h.and,either_map h,get_map h]
theorem tokenSelect_map (mask : B) (yes no : TokenState B) :
    (tokenSelect a mask yes no).map f = tokenSelect b (f mask) (yes.map f) (no.map f) := by
  simp only [tokenSelect,TokenState.map,choose_map h,TlsInner.select_map h]
theorem start_map : (start a).map f = start b := by
  simp only [start,State.map,initial_map h,h.const,List.map_map,Function.comp_def,
    List.map_replicate,tokenInitial_map h]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem step_map (expected : List B) (offset : Nat) (s : State B) (x : B) :
    (step a expected offset s x).map f = step b (expected.map f) offset (s.map f) (f x) := by
  simp only [step,State.map,List.map_cons,List.map_nil,List.map_zipWith,List.zipWith_map,
    List.map_map,Function.comp_def,get_map h,getName_map h,either_map h,eq_map h,h.and,h.not,h.const,
    token_map h,field_map h,ows_map h,lower_map h,any_map h,choose_map h,
    advance_map h,literal_map h,initial_map h,literal_length,List.length_map,TlsInner.select_map h,
    tokenFinish_map h,tokenSelect_map h,tokenInitial_map h,tokenStep_map h]
theorem stateSelect_map (mask : B) (yes no : State B) :
    (stateSelect a mask yes no).map f = stateSelect b (f mask) (yes.map f) (no.map f) := by
  simp only [stateSelect,State.map,choose_map h,TlsInner.select_map h,tokenSelect_map h,
    List.map_zipWith,List.zipWith_map]
theorem activity_map (hi lo : B) (offset n : Nat) :
    (f (activity a hi lo offset n).1,(activity a hi lo offset n).2.map f) =
      activity b (f hi) (f lo) offset n := by
  induction n generalizing offset with
  | zero => simp only [activity,TlsPrivateSeal.eqLength_map h,List.map_nil]
  | succ n ih =>
    have inductionResult := ih (offset+1)
    have first := congrArg Prod.fst inductionResult
    have rest := congrArg Prod.snd inductionResult
    simp only [Prod.fst,Prod.snd] at first rest
    simp only [activity,List.map_cons,either_map h,TlsPrivateSeal.eqLength_map h,first,rest]
theorem feedLoop_map (expected : List B) (offset : Nat) (s : State B) (data masks : List B) :
    ((feedLoop a expected offset s data masks).1.map f,(feedLoop a expected offset s data masks).2.map f) =
      feedLoop b (expected.map f) offset (s.map f) (data.map f) (masks.map f) := by
  induction data generalizing offset s masks with
  | nil => rfl
  | cons x xs ih =>
    cases masks with
    | nil => rfl
    | cons active masks =>
      have inductionResult := ih (offset+1) (stateSelect a active (step a expected offset s x) s) masks
      simp only [stateSelect_map h,step_map h] at inductionResult
      have first := congrArg Prod.fst inductionResult
      have rest := congrArg Prod.snd inductionResult
      simp only [Prod.fst,Prod.snd] at first rest
      simp only [feedLoop,List.map_cons,stateSelect_map h,step_map h,first,rest,h.and,get_map h]
      rfl
theorem validUpdate_map (s : State B) (value : B) :
    ({s with valid := value}).map f = {s.map f with valid := f value} := rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem feed_map (expected : List B) (s : State B) (valid hi lo : B) (data : List B) :
    ((feed a expected s valid hi lo data).1.map f,(feed a expected s valid hi lo data).2.map f) =
      feed b (expected.map f) (s.map f) (f valid) (f hi) (f lo) (data.map f) := by
  have masks := activity_map h hi lo 0 data.length
  have mf := congrArg Prod.fst masks
  have ms := congrArg Prod.snd masks
  simp only [Prod.fst,Prod.snd] at mf ms
  have result := feedLoop_map h expected 0 s data (activity a hi lo 0 data.length).2
  rw [ms] at result
  have rf := congrArg Prod.fst result
  have rs := congrArg Prod.snd result
  simp only [Prod.fst,Prod.snd] at rf rs
  have rv := congrArg State.valid rf
  simp only [State.map] at rv
  unfold feed
  simp only [List.length_map]
  rw [validUpdate_map h]
  simp only [h.and,eq_map h,ByteAuth.release_map h]
  rw [rv,mf,rs,rf]
  rfl
theorem run_map (capacity : Nat) (raw : List B) :
    (run a capacity raw).map f = run b capacity (raw.map f) := by
  have result := feed_map h ((raw.drop stateSize).take 28) (readState a (raw.take stateSize))
    (get a raw (stateSize+28)) (get a raw (stateSize+28+1)) (get a raw (stateSize+28+2))
    ((raw.drop (stateSize+28+3)).take capacity)
  simp only [readState_map h,List.map_take,List.map_drop,get_map h] at result
  have rf := congrArg Prod.fst result
  have rs := congrArg Prod.snd result
  simp only [Prod.fst,Prod.snd] at rf rs
  have rv := congrArg State.valid rf
  have rp := congrArg State.phases rf
  simp only [State.map] at rv rp
  simp only [run,List.map_cons,List.map_append,get_map h,stateBytes_map h,List.map_take,List.map_drop]
  rw [rv,rp,rf,rs]

theorem runByte_map (raw : List B) : (runByte a raw).map f = runByte b (raw.map f) := by
  let s := readState a (raw.take stateSize)
  let expected := (raw.drop stateSize).take 28
  let active := get a raw (stateSize+28)
  let x := get a raw (stateSize+29)
  have next := stateSelect_map h (eq a active 255) (step a expected 0 s x) s
  simp only [eq_map h,step_map h] at next
  have nv := congrArg State.valid next
  have np := congrArg State.phases next
  change f (stateSelect a (eq a active 255) (step a expected 0 s x) s).valid = _ at nv
  change (stateSelect a (eq a active 255) (step a expected 0 s x) s).phases.map f = _ at np
  have sp := congrArg State.phases (readState_map h (raw.take stateSize))
  change (readState a (raw.take stateSize)).phases.map f = _ at sp
  unfold runByte
  simp only [List.map_cons,List.map_append,stateBytes_map h,get_map h,h.and,either_map h,eq_map h]
  rw [validUpdate_map h]
  simp only [h.and,either_map h,eq_map h]
  change _ = _
  simp only [s,expected,active,x] at next nv np
  rw [nv,np,next,sp]
  simp only [readState_map h,List.map_take,List.map_drop,get_map h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
omit h in
theorem compiled_run_correct (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index<8*(run ByteAuth.symbolic capacity raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (run ByteAuth.symbolic capacity raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (run ByteAuth.symbolic capacity raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run ByteAuth.concrete capacity (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)]
omit h in
theorem compiled_runByte_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index<8*(runByte ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runByte ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runByte ByteAuth.symbolic raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (runByte ByteAuth.concrete (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runByte_map (ByteAuth.evaluationHom assign)]
end Refinement

end TlsMpc.TlsWebSocketUpgrade
