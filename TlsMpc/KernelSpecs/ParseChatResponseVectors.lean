import TlsMpc.KernelSpecs.ParseChatResponse

/-!
# Vectors: the service-response parser through `runByte`, byte by byte

New file; it changes no definition and no emitter imports it. Generated (states and outputs
computed by evaluating the deployed definitions, then each step checked by the kernel).

Each vector feeds the deployed `TlsChatResponse.runByte` (capacity 16384, expected id 1) exactly as
the controller does for a single-frame binary message: the frame's first header byte with flags
`0 255 0` (message start), the second with `0 0 0`, every payload byte with `255 0 0`, the last with
`255 0 255` (message end). `vX_stepK`: one `runByte` call, kernel-checked, from the serialised state
`vXK` (written as the fields that differ from the parser's initial state). `vX_run`: the controller's
loop (`respRun`) over the whole message: every output, and the final state. `vX_extent`: the
`bodyData` outputs against the reference decoder `wsMessage` (`bodyMask`).

* A: `08 02 1a 0d | 08 01 | 10 c8 01 | 1a 02 "OK" | 22 02 aa bb`: a 200 response, id 1, body
  `aa bb`. Valid throughout; `bodyReset` on the body's length, `bodyData` on `aa bb`; finished and
  successful at the last byte; final state `id` 1, `status` 200.
* B: the same with the body's length `05` (beyond the inner response's 13 bytes): the validity
  byte drops at that byte (fail closed); no byte is reported as body; the reference rejects it too.
* C: A with a header `"a:b"` after the body (`2a 03 61 3a 62`, inner length `12`): `headerData`
  on the header's bytes, body as in A, completed.
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open TlsMpc.KernelSpecs.ParseChatResponse (RState d o respRun wsMessage Decoded)

namespace TlsMpc.KernelSpecs.ParseChatResponseVectors

abbrev Byte := BitVec 8

def initS : RState := TlsChatResponse.initial Word64.fast fast 16384 (BitVec.ofNat 64 1)

theorem respRun_step (cap : Nat) (raw raw' f out : List Byte) (x : Byte) (rest : List (List Byte × Byte))
    (h : TlsChatResponse.runByte d o fast cap (raw ++ f ++ [x]) = out ++ raw') (hl : out.length = 6) :
    respRun cap raw ((f, x) :: rest) = (out :: (respRun cap raw' rest).1, (respRun cap raw' rest).2) := by
  simp only [respRun, h, List.drop_left' hl, List.take_left' hl]

/-- What the controller feeds the response parser for one binary message in one frame (payload
under 126 bytes): the first header byte starts the message, the second is nothing, each payload byte
is data, the last also ends the message. -/
def msgInputs (m : List Byte) : List (List Byte × Byte) :=
  ([0, 255, 0], 0x82) :: ([0, 0, 0], BitVec.ofNat 8 m.length) ::
    (m.dropLast.map (fun x => ([255, 0, 0], x))) ++ [([255, 0, 255], m.getLast!)]

/-- The reference's body extent over the controller's inputs: two frame-header bytes, then the
message; 255 on the body's bytes. -/
def bodyMask (m : List Byte) : List Byte :=
  match wsMessage m with
  | some r => match r.body with
    | some (s, n) => [0, 0] ++ (List.range m.length).map (fun i => if s ≤ i ∧ i < s + n then 255 else 0)
    | none => List.replicate (m.length + 2) 0
  | none => List.replicate (m.length + 2) 0

/-! ### Vector vA: a 200 response with a body -/

def vAmsg : List Byte := [8#8, 2#8, 26#8, 13#8, 8#8, 1#8, 16#8, 200#8, 1#8, 26#8, 2#8, 79#8, 75#8, 34#8, 2#8, 170#8, 187#8]

def vA0 : RState := initS

def vA1 : RState := { initS with
  seen := 255#8 }
theorem vA_step0 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA0 ++ [0#8, 255#8, 0#8] ++ [130#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA1 := by
  decide +kernel

def vA2 : RState := { initS with
  seen := 255#8 }
theorem vA_step1 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA1 ++ [0#8, 0#8, 0#8] ++ [17#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA2 := by
  decide +kernel

def vA3 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 1#64,
  scalarKnown := 255#8,
  budget := 16383#64 }
theorem vA_step2 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA2 ++ [255#8, 0#8, 0#8] ++ [8#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA3 := by
  decide +kernel

def vA4 : RState := { initS with
  seen := 255#8,
  tag := 1#64,
  scalarKnown := 255#8,
  budget := 16382#64,
  typeValue := 2#64 }
theorem vA_step3 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA3 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA4 := by
  decide +kernel

def vA5 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 3#64,
  kinds := [255#8, 0#8, 0#8, 0#8],
  budget := 16381#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vA_step4 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA4 ++ [255#8, 0#8, 0#8] ++ [26#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA5 := by
  decide +kernel

def vA6 : RState := { initS with
  seen := 255#8,
  tag := 3#64,
  kinds := [255#8, 0#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 13#64,
  budget := 16380#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vA_step5 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA5 ++ [255#8, 0#8, 0#8] ++ [13#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA6 := by
  decide +kernel

def vA7 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 1#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 12#64,
  budget := 16379#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vA_step6 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA6 ++ [255#8, 0#8, 0#8] ++ [8#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA7 := by
  decide +kernel

def vA8 : RState := { initS with
  seen := 255#8,
  tag := 1#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 11#64,
  budget := 16378#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vA_step7 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA7 ++ [255#8, 0#8, 0#8] ++ [1#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA8 := by
  decide +kernel

def vA9 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 10#64,
  budget := 16377#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vA_step8 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA8 ++ [255#8, 0#8, 0#8] ++ [16#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA9 := by
  decide +kernel

def vA10 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  positions := [0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8],
  value := 72#64,
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 9#64,
  budget := 16376#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vA_step9 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA9 ++ [255#8, 0#8, 0#8] ++ [200#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA10 := by
  decide +kernel

def vA11 : RState := { initS with
  seen := 255#8,
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 8#64,
  budget := 16375#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64 }
theorem vA_step10 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA10 ++ [255#8, 0#8, 0#8] ++ [1#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA11 := by
  decide +kernel

def vA12 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 7#64,
  budget := 16374#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64 }
theorem vA_step11 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA11 ++ [255#8, 0#8, 0#8] ++ [26#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA12 := by
  decide +kernel

def vA13 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 6#64,
  budget := 16373#64,
  skip := 2#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vA_step12 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA12 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA13 := by
  decide +kernel

def vA14 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 5#64,
  budget := 16372#64,
  skip := 1#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vA_step13 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA13 ++ [255#8, 0#8, 0#8] ++ [79#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA14 := by
  decide +kernel

def vA15 : RState := { initS with
  seen := 255#8,
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 4#64,
  budget := 16371#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vA_step14 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA14 ++ [255#8, 0#8, 0#8] ++ [75#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA15 := by
  decide +kernel

def vA16 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 3#64,
  budget := 16370#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vA_step15 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA15 ++ [255#8, 0#8, 0#8] ++ [34#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA16 := by
  decide +kernel

def vA17 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 2#64,
  budget := 16369#64,
  skip := 2#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vA_step16 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA16 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 255#8, 0#8] ++ TlsChatResponse.stateBytes o vA17 := by
  decide +kernel

def vA18 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 1#64,
  budget := 16368#64,
  skip := 1#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vA_step17 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA17 ++ [255#8, 0#8, 0#8] ++ [170#8]) =
    [255#8, 0#8, 0#8, 255#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA18 := by
  decide +kernel

def vA19 : RState := { initS with
  seen := 255#8,
  finished := 255#8,
  successful := 255#8,
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  budget := 16367#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vA_step18 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vA18 ++ [255#8, 0#8, 255#8] ++ [187#8]) =
    [255#8, 255#8, 255#8, 255#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vA19 := by
  decide +kernel

/-- The controller's inputs for the message: as `msgInputs` builds them. -/
def vAin : List (List Byte × Byte) :=
    [([0#8, 255#8, 0#8], 130#8),
    ([0#8, 0#8, 0#8], 17#8),
    ([255#8, 0#8, 0#8], 8#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 26#8),
    ([255#8, 0#8, 0#8], 13#8),
    ([255#8, 0#8, 0#8], 8#8),
    ([255#8, 0#8, 0#8], 1#8),
    ([255#8, 0#8, 0#8], 16#8),
    ([255#8, 0#8, 0#8], 200#8),
    ([255#8, 0#8, 0#8], 1#8),
    ([255#8, 0#8, 0#8], 26#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 79#8),
    ([255#8, 0#8, 0#8], 75#8),
    ([255#8, 0#8, 0#8], 34#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 170#8),
    ([255#8, 0#8, 255#8], 187#8)]

theorem vA_inputs : vAin = msgInputs vAmsg := by
  decide +kernel

def vAout : List (List Byte) :=
    [[255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 255#8, 0#8],
     [255#8, 0#8, 0#8, 255#8, 0#8, 0#8],
     [255#8, 255#8, 255#8, 255#8, 0#8, 0#8]]

/-- The controller's loop over the whole message (19 bytes: two frame-header bytes, then the payload): every output, and the final state. -/
theorem vA_run : respRun 16384 (TlsChatResponse.stateBytes o vA0) vAin =
    (vAout, TlsChatResponse.stateBytes o vA19) := by
  simp only [vAin, respRun_step _ _ _ _ _ _ _ vA_step0 rfl, respRun_step _ _ _ _ _ _ _ vA_step1 rfl, respRun_step _ _ _ _ _ _ _ vA_step2 rfl, respRun_step _ _ _ _ _ _ _ vA_step3 rfl, respRun_step _ _ _ _ _ _ _ vA_step4 rfl, respRun_step _ _ _ _ _ _ _ vA_step5 rfl, respRun_step _ _ _ _ _ _ _ vA_step6 rfl, respRun_step _ _ _ _ _ _ _ vA_step7 rfl, respRun_step _ _ _ _ _ _ _ vA_step8 rfl, respRun_step _ _ _ _ _ _ _ vA_step9 rfl, respRun_step _ _ _ _ _ _ _ vA_step10 rfl, respRun_step _ _ _ _ _ _ _ vA_step11 rfl, respRun_step _ _ _ _ _ _ _ vA_step12 rfl, respRun_step _ _ _ _ _ _ _ vA_step13 rfl, respRun_step _ _ _ _ _ _ _ vA_step14 rfl, respRun_step _ _ _ _ _ _ _ vA_step15 rfl, respRun_step _ _ _ _ _ _ _ vA_step16 rfl, respRun_step _ _ _ _ _ _ _ vA_step17 rfl, respRun_step _ _ _ _ _ _ _ vA_step18 rfl]
  rfl

/-- `bodyData` (output byte 3) is 255 exactly on the bytes the reference decoder puts in the body. -/
theorem vA_extent :
    (respRun 16384 (TlsChatResponse.stateBytes o vA0) vAin).1.map (fun o => o.getD 3 0) = bodyMask vAmsg := by
  rw [vA_run]
  decide +kernel

/-! ### Vector vB: a body length beyond the inner response -/

def vBmsg : List Byte := [8#8, 2#8, 26#8, 13#8, 8#8, 1#8, 16#8, 200#8, 1#8, 26#8, 2#8, 79#8, 75#8, 34#8, 5#8, 170#8, 187#8]

def vB0 : RState := initS

def vB1 : RState := { initS with
  seen := 255#8 }
theorem vB_step0 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB0 ++ [0#8, 255#8, 0#8] ++ [130#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB1 := by
  decide +kernel

def vB2 : RState := { initS with
  seen := 255#8 }
theorem vB_step1 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB1 ++ [0#8, 0#8, 0#8] ++ [17#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB2 := by
  decide +kernel

def vB3 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 1#64,
  scalarKnown := 255#8,
  budget := 16383#64 }
theorem vB_step2 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB2 ++ [255#8, 0#8, 0#8] ++ [8#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB3 := by
  decide +kernel

def vB4 : RState := { initS with
  seen := 255#8,
  tag := 1#64,
  scalarKnown := 255#8,
  budget := 16382#64,
  typeValue := 2#64 }
theorem vB_step3 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB3 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB4 := by
  decide +kernel

def vB5 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 3#64,
  kinds := [255#8, 0#8, 0#8, 0#8],
  budget := 16381#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vB_step4 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB4 ++ [255#8, 0#8, 0#8] ++ [26#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB5 := by
  decide +kernel

def vB6 : RState := { initS with
  seen := 255#8,
  tag := 3#64,
  kinds := [255#8, 0#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 13#64,
  budget := 16380#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vB_step5 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB5 ++ [255#8, 0#8, 0#8] ++ [13#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB6 := by
  decide +kernel

def vB7 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 1#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 12#64,
  budget := 16379#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vB_step6 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB6 ++ [255#8, 0#8, 0#8] ++ [8#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB7 := by
  decide +kernel

def vB8 : RState := { initS with
  seen := 255#8,
  tag := 1#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 11#64,
  budget := 16378#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vB_step7 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB7 ++ [255#8, 0#8, 0#8] ++ [1#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB8 := by
  decide +kernel

def vB9 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 10#64,
  budget := 16377#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vB_step8 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB8 ++ [255#8, 0#8, 0#8] ++ [16#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB9 := by
  decide +kernel

def vB10 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  positions := [0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8],
  value := 72#64,
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 9#64,
  budget := 16376#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vB_step9 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB9 ++ [255#8, 0#8, 0#8] ++ [200#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB10 := by
  decide +kernel

def vB11 : RState := { initS with
  seen := 255#8,
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 8#64,
  budget := 16375#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64 }
theorem vB_step10 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB10 ++ [255#8, 0#8, 0#8] ++ [1#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB11 := by
  decide +kernel

def vB12 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 7#64,
  budget := 16374#64,
  skip := 13#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64 }
theorem vB_step11 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB11 ++ [255#8, 0#8, 0#8] ++ [26#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB12 := by
  decide +kernel

def vB13 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 6#64,
  budget := 16373#64,
  skip := 2#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vB_step12 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB12 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB13 := by
  decide +kernel

def vB14 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 5#64,
  budget := 16372#64,
  skip := 1#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vB_step13 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB13 ++ [255#8, 0#8, 0#8] ++ [79#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB14 := by
  decide +kernel

def vB15 : RState := { initS with
  seen := 255#8,
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 4#64,
  budget := 16371#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vB_step14 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB14 ++ [255#8, 0#8, 0#8] ++ [75#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB15 := by
  decide +kernel

def vB16 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 3#64,
  budget := 16370#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vB_step15 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB15 ++ [255#8, 0#8, 0#8] ++ [34#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB16 := by
  decide +kernel

def vB17 : RState := { initS with
  valid := 0#8,
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 2#64,
  budget := 16369#64,
  skip := 5#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 5#64,
  messagePresent := 255#8 }
theorem vB_step16 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB16 ++ [255#8, 0#8, 0#8] ++ [5#8]) =
    [0#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB17 := by
  decide +kernel

def vB18 : RState := { initS with
  valid := 0#8,
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 1#64,
  budget := 16368#64,
  skip := 4#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 5#64,
  messagePresent := 255#8 }
theorem vB_step17 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB17 ++ [255#8, 0#8, 0#8] ++ [170#8]) =
    [0#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB18 := by
  decide +kernel

def vB19 : RState := { initS with
  valid := 0#8,
  seen := 255#8,
  finished := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  budget := 16367#64,
  skip := 3#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 5#64,
  messagePresent := 255#8 }
theorem vB_step18 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vB18 ++ [255#8, 0#8, 255#8] ++ [187#8]) =
    [0#8, 255#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vB19 := by
  decide +kernel

/-- The controller's inputs for the message: as `msgInputs` builds them. -/
def vBin : List (List Byte × Byte) :=
    [([0#8, 255#8, 0#8], 130#8),
    ([0#8, 0#8, 0#8], 17#8),
    ([255#8, 0#8, 0#8], 8#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 26#8),
    ([255#8, 0#8, 0#8], 13#8),
    ([255#8, 0#8, 0#8], 8#8),
    ([255#8, 0#8, 0#8], 1#8),
    ([255#8, 0#8, 0#8], 16#8),
    ([255#8, 0#8, 0#8], 200#8),
    ([255#8, 0#8, 0#8], 1#8),
    ([255#8, 0#8, 0#8], 26#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 79#8),
    ([255#8, 0#8, 0#8], 75#8),
    ([255#8, 0#8, 0#8], 34#8),
    ([255#8, 0#8, 0#8], 5#8),
    ([255#8, 0#8, 0#8], 170#8),
    ([255#8, 0#8, 255#8], 187#8)]

theorem vB_inputs : vBin = msgInputs vBmsg := by
  decide +kernel

def vBout : List (List Byte) :=
    [[255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [0#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [0#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [0#8, 255#8, 0#8, 0#8, 0#8, 0#8]]

/-- The controller's loop over the whole message (19 bytes: two frame-header bytes, then the payload): every output, and the final state. -/
theorem vB_run : respRun 16384 (TlsChatResponse.stateBytes o vB0) vBin =
    (vBout, TlsChatResponse.stateBytes o vB19) := by
  simp only [vBin, respRun_step _ _ _ _ _ _ _ vB_step0 rfl, respRun_step _ _ _ _ _ _ _ vB_step1 rfl, respRun_step _ _ _ _ _ _ _ vB_step2 rfl, respRun_step _ _ _ _ _ _ _ vB_step3 rfl, respRun_step _ _ _ _ _ _ _ vB_step4 rfl, respRun_step _ _ _ _ _ _ _ vB_step5 rfl, respRun_step _ _ _ _ _ _ _ vB_step6 rfl, respRun_step _ _ _ _ _ _ _ vB_step7 rfl, respRun_step _ _ _ _ _ _ _ vB_step8 rfl, respRun_step _ _ _ _ _ _ _ vB_step9 rfl, respRun_step _ _ _ _ _ _ _ vB_step10 rfl, respRun_step _ _ _ _ _ _ _ vB_step11 rfl, respRun_step _ _ _ _ _ _ _ vB_step12 rfl, respRun_step _ _ _ _ _ _ _ vB_step13 rfl, respRun_step _ _ _ _ _ _ _ vB_step14 rfl, respRun_step _ _ _ _ _ _ _ vB_step15 rfl, respRun_step _ _ _ _ _ _ _ vB_step16 rfl, respRun_step _ _ _ _ _ _ _ vB_step17 rfl, respRun_step _ _ _ _ _ _ _ vB_step18 rfl]
  rfl

/-- `bodyData` (output byte 3) is 255 exactly on the bytes the reference decoder puts in the body. -/
theorem vB_extent :
    (respRun 16384 (TlsChatResponse.stateBytes o vB0) vBin).1.map (fun o => o.getD 3 0) = bodyMask vBmsg := by
  rw [vB_run]
  decide +kernel

/-! ### Vector vC: a 200 response with a body and a header -/

def vCmsg : List Byte := [8#8, 2#8, 26#8, 18#8, 8#8, 1#8, 16#8, 200#8, 1#8, 26#8, 2#8, 79#8, 75#8, 34#8, 2#8, 170#8, 187#8, 42#8, 3#8, 97#8, 58#8, 98#8]

def vC0 : RState := initS

def vC1 : RState := { initS with
  seen := 255#8 }
theorem vC_step0 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC0 ++ [0#8, 255#8, 0#8] ++ [130#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC1 := by
  decide +kernel

def vC2 : RState := { initS with
  seen := 255#8 }
theorem vC_step1 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC1 ++ [0#8, 0#8, 0#8] ++ [22#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC2 := by
  decide +kernel

def vC3 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 1#64,
  scalarKnown := 255#8,
  budget := 16383#64 }
theorem vC_step2 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC2 ++ [255#8, 0#8, 0#8] ++ [8#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC3 := by
  decide +kernel

def vC4 : RState := { initS with
  seen := 255#8,
  tag := 1#64,
  scalarKnown := 255#8,
  budget := 16382#64,
  typeValue := 2#64 }
theorem vC_step3 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC3 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC4 := by
  decide +kernel

def vC5 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 3#64,
  kinds := [255#8, 0#8, 0#8, 0#8],
  budget := 16381#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vC_step4 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC4 ++ [255#8, 0#8, 0#8] ++ [26#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC5 := by
  decide +kernel

def vC6 : RState := { initS with
  seen := 255#8,
  tag := 3#64,
  kinds := [255#8, 0#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 18#64,
  budget := 16380#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vC_step5 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC5 ++ [255#8, 0#8, 0#8] ++ [18#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC6 := by
  decide +kernel

def vC7 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 1#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 17#64,
  budget := 16379#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8 }
theorem vC_step6 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC6 ++ [255#8, 0#8, 0#8] ++ [8#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC7 := by
  decide +kernel

def vC8 : RState := { initS with
  seen := 255#8,
  tag := 1#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 16#64,
  budget := 16378#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vC_step7 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC7 ++ [255#8, 0#8, 0#8] ++ [1#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC8 := by
  decide +kernel

def vC9 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 15#64,
  budget := 16377#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vC_step8 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC8 ++ [255#8, 0#8, 0#8] ++ [16#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC9 := by
  decide +kernel

def vC10 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 255#8, 0#8, 0#8],
  positions := [0#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8],
  value := 72#64,
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 14#64,
  budget := 16376#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64 }
theorem vC_step9 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC9 ++ [255#8, 0#8, 0#8] ++ [200#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC10 := by
  decide +kernel

def vC11 : RState := { initS with
  seen := 255#8,
  tag := 2#64,
  scalarKnown := 255#8,
  inner := 255#8,
  responseRemaining := 13#64,
  budget := 16375#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64 }
theorem vC_step10 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC10 ++ [255#8, 0#8, 0#8] ++ [1#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC11 := by
  decide +kernel

def vC12 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 12#64,
  budget := 16374#64,
  skip := 18#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64 }
theorem vC_step11 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC11 ++ [255#8, 0#8, 0#8] ++ [26#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC12 := by
  decide +kernel

def vC13 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 11#64,
  budget := 16373#64,
  skip := 2#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vC_step12 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC12 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC13 := by
  decide +kernel

def vC14 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 10#64,
  budget := 16372#64,
  skip := 1#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vC_step13 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC13 ++ [255#8, 0#8, 0#8] ++ [79#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC14 := by
  decide +kernel

def vC15 : RState := { initS with
  seen := 255#8,
  tag := 3#64,
  kinds := [0#8, 0#8, 255#8, 0#8],
  inner := 255#8,
  responseRemaining := 9#64,
  budget := 16371#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vC_step14 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC14 ++ [255#8, 0#8, 0#8] ++ [75#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC15 := by
  decide +kernel

def vC16 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 8#64,
  budget := 16370#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  messagePresent := 255#8 }
theorem vC_step15 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC15 ++ [255#8, 0#8, 0#8] ++ [34#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC16 := by
  decide +kernel

def vC17 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 7#64,
  budget := 16369#64,
  skip := 2#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vC_step16 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC16 ++ [255#8, 0#8, 0#8] ++ [2#8]) =
    [255#8, 0#8, 0#8, 0#8, 255#8, 0#8] ++ TlsChatResponse.stateBytes o vC17 := by
  decide +kernel

def vC18 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 6#64,
  budget := 16368#64,
  skip := 1#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vC_step17 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC17 ++ [255#8, 0#8, 0#8] ++ [170#8]) =
    [255#8, 0#8, 0#8, 255#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC18 := by
  decide +kernel

def vC19 : RState := { initS with
  seen := 255#8,
  tag := 4#64,
  kinds := [0#8, 255#8, 0#8, 0#8],
  inner := 255#8,
  responseRemaining := 5#64,
  budget := 16367#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vC_step18 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC18 ++ [255#8, 0#8, 0#8] ++ [187#8]) =
    [255#8, 0#8, 0#8, 255#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC19 := by
  decide +kernel

def vC20 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 255#8, 0#8],
  tag := 5#64,
  kinds := [0#8, 0#8, 0#8, 255#8],
  inner := 255#8,
  responseRemaining := 4#64,
  budget := 16366#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vC_step19 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC19 ++ [255#8, 0#8, 0#8] ++ [42#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC20 := by
  decide +kernel

def vC21 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 5#64,
  kinds := [0#8, 0#8, 0#8, 255#8],
  inner := 255#8,
  responseRemaining := 3#64,
  budget := 16365#64,
  skip := 3#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8 }
theorem vC_step20 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC20 ++ [255#8, 0#8, 0#8] ++ [3#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsChatResponse.stateBytes o vC21 := by
  decide +kernel

def vC22 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 5#64,
  kinds := [0#8, 0#8, 0#8, 255#8],
  inner := 255#8,
  responseRemaining := 2#64,
  budget := 16364#64,
  skip := 2#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8,
  header := ⟨255#8, 255#8, 0#8, 0#8, 0#8, 0#8, 0#8⟩ }
theorem vC_step21 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC21 ++ [255#8, 0#8, 0#8] ++ [97#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 255#8] ++ TlsChatResponse.stateBytes o vC22 := by
  decide +kernel

def vC23 : RState := { initS with
  seen := 255#8,
  modes := [0#8, 0#8, 0#8, 255#8],
  tag := 5#64,
  kinds := [0#8, 0#8, 0#8, 255#8],
  inner := 255#8,
  responseRemaining := 1#64,
  budget := 16363#64,
  skip := 1#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8,
  header := ⟨255#8, 255#8, 255#8, 0#8, 0#8, 0#8, 0#8⟩ }
theorem vC_step22 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC22 ++ [255#8, 0#8, 0#8] ++ [58#8]) =
    [255#8, 0#8, 0#8, 0#8, 0#8, 255#8] ++ TlsChatResponse.stateBytes o vC23 := by
  decide +kernel

def vC24 : RState := { initS with
  seen := 255#8,
  finished := 255#8,
  successful := 255#8,
  tag := 5#64,
  kinds := [0#8, 0#8, 0#8, 255#8],
  budget := 16362#64,
  typeValue := 2#64,
  responsePresent := 255#8,
  idPresent := 255#8,
  id := 1#64,
  status := 200#64,
  bodyPresent := 255#8,
  bodyLength := 2#64,
  messagePresent := 255#8,
  header := ⟨255#8, 255#8, 255#8, 255#8, 0#8, 98#8, 0#8⟩ }
theorem vC_step23 : TlsChatResponse.runByte d o fast 16384 (TlsChatResponse.stateBytes o vC23 ++ [255#8, 0#8, 255#8] ++ [98#8]) =
    [255#8, 255#8, 255#8, 0#8, 0#8, 255#8] ++ TlsChatResponse.stateBytes o vC24 := by
  decide +kernel

/-- The controller's inputs for the message: as `msgInputs` builds them. -/
def vCin : List (List Byte × Byte) :=
    [([0#8, 255#8, 0#8], 130#8),
    ([0#8, 0#8, 0#8], 22#8),
    ([255#8, 0#8, 0#8], 8#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 26#8),
    ([255#8, 0#8, 0#8], 18#8),
    ([255#8, 0#8, 0#8], 8#8),
    ([255#8, 0#8, 0#8], 1#8),
    ([255#8, 0#8, 0#8], 16#8),
    ([255#8, 0#8, 0#8], 200#8),
    ([255#8, 0#8, 0#8], 1#8),
    ([255#8, 0#8, 0#8], 26#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 79#8),
    ([255#8, 0#8, 0#8], 75#8),
    ([255#8, 0#8, 0#8], 34#8),
    ([255#8, 0#8, 0#8], 2#8),
    ([255#8, 0#8, 0#8], 170#8),
    ([255#8, 0#8, 0#8], 187#8),
    ([255#8, 0#8, 0#8], 42#8),
    ([255#8, 0#8, 0#8], 3#8),
    ([255#8, 0#8, 0#8], 97#8),
    ([255#8, 0#8, 0#8], 58#8),
    ([255#8, 0#8, 255#8], 98#8)]

theorem vC_inputs : vCin = msgInputs vCmsg := by
  decide +kernel

def vCout : List (List Byte) :=
    [[255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 255#8, 0#8],
     [255#8, 0#8, 0#8, 255#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 255#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 0#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 255#8],
     [255#8, 0#8, 0#8, 0#8, 0#8, 255#8],
     [255#8, 255#8, 255#8, 0#8, 0#8, 255#8]]

/-- The controller's loop over the whole message (24 bytes: two frame-header bytes, then the payload): every output, and the final state. -/
theorem vC_run : respRun 16384 (TlsChatResponse.stateBytes o vC0) vCin =
    (vCout, TlsChatResponse.stateBytes o vC24) := by
  simp only [vCin, respRun_step _ _ _ _ _ _ _ vC_step0 rfl, respRun_step _ _ _ _ _ _ _ vC_step1 rfl, respRun_step _ _ _ _ _ _ _ vC_step2 rfl, respRun_step _ _ _ _ _ _ _ vC_step3 rfl, respRun_step _ _ _ _ _ _ _ vC_step4 rfl, respRun_step _ _ _ _ _ _ _ vC_step5 rfl, respRun_step _ _ _ _ _ _ _ vC_step6 rfl, respRun_step _ _ _ _ _ _ _ vC_step7 rfl, respRun_step _ _ _ _ _ _ _ vC_step8 rfl, respRun_step _ _ _ _ _ _ _ vC_step9 rfl, respRun_step _ _ _ _ _ _ _ vC_step10 rfl, respRun_step _ _ _ _ _ _ _ vC_step11 rfl, respRun_step _ _ _ _ _ _ _ vC_step12 rfl, respRun_step _ _ _ _ _ _ _ vC_step13 rfl, respRun_step _ _ _ _ _ _ _ vC_step14 rfl, respRun_step _ _ _ _ _ _ _ vC_step15 rfl, respRun_step _ _ _ _ _ _ _ vC_step16 rfl, respRun_step _ _ _ _ _ _ _ vC_step17 rfl, respRun_step _ _ _ _ _ _ _ vC_step18 rfl, respRun_step _ _ _ _ _ _ _ vC_step19 rfl, respRun_step _ _ _ _ _ _ _ vC_step20 rfl, respRun_step _ _ _ _ _ _ _ vC_step21 rfl, respRun_step _ _ _ _ _ _ _ vC_step22 rfl, respRun_step _ _ _ _ _ _ _ vC_step23 rfl]
  rfl

/-- `bodyData` (output byte 3) is 255 exactly on the bytes the reference decoder puts in the body. -/
theorem vC_extent :
    (respRun 16384 (TlsChatResponse.stateBytes o vC0) vCin).1.map (fun o => o.getD 3 0) = bodyMask vCmsg := by
  rw [vC_run]
  decide +kernel

theorem vA_reference : wsMessage vAmsg = some ⟨some 2, false, some 1, some 200, some (11, 2), some (15, 2), []⟩ := by
  decide +kernel

theorem vB_reference : wsMessage vBmsg = none := by
  decide +kernel

theorem vC_reference : wsMessage vCmsg = some ⟨some 2, false, some 1, some 200, some (11, 2), some (15, 2), [(19, 3)]⟩ := by
  decide +kernel

end TlsMpc.KernelSpecs.ParseChatResponseVectors
