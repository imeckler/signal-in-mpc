import Lean.Data.Json
import TlsMpc.Node.Policy.Receive

/-!
# Failures as per-contact outcomes, results and the journal (pure)

Moved unchanged (names kept) from the controller
(`handshake_backend/EmpHybridWork/PublicServiceController.lean`, which imports this module) in
REORGANIZATION_PLAN.md stage S2, with its unit check (`checks`, run by
`public_service_controller recovery-check`) and the walks `parse-bench` measures. No emitter
imports this module.
-/

open Lean (toJson)

/-! ---- Failures as per-contact outcomes (PRODUCT_TODO.md sections 3 and 4).

A send session with the database nodes does not end when one contact fails. Everything decided
here is decided from values both controllers hold: a response's status and headers (revealed
as always; never its body), the engines' opened status bytes, and whether the worker reported a
connection closed. The table:

| Signal                                         | Action                                                  |
|------------------------------------------------|---------------------------------------------------------|
| 2xx to a send                                  | delivered                                               |
| 409 / 410 to a send                            | refresh the contact's sessions and send again; a refusal after that is refreshed again, at most `refreshRetries` more times |
| 429 or 5xx (send or prekey fetch)              | back off (`Retry-After` if the response has it, else `schedule`), the contact goes to the end of the queue; at most `transientRetries` retries |
| the connection was closed                      | that connection is replaced (new handshake, the others kept) and what was in flight is sent again: a possible duplicate, by the owner's decision; at most `reconnects` times per message |
| 401 (send or prekey fetch)                     | stop: the contact needs to sign up again                |
| 404                                            | stop: the account is gone                               |
| the bundle's identity key is a new one         | accepted: sessions replaced, reported                   |
| the bundle does not parse or verify            | stop, nothing stored: fault                             |

With sealed sender the Signal server answers 401, not 404, for an account that no longer
exists (`OptionalAccess.verify`: a 404 "would provide a free exists check"), so a deleted
account is reported as needing to sign up again. Never falls back to an unsealed send. -/
namespace Recovery

/-- The result the application gets for an id of a notify. -/
inductive Result where
  | delivered | deliveredAfterRefresh | deliveredAfterIdentityChange
  | retryLater | needsSignup | gone | fault
  deriving BEq, Repr

def Result.all : List Result :=
  [.delivered, .deliveredAfterRefresh, .deliveredAfterIdentityChange, .retryLater, .needsSignup, .gone, .fault]

def Result.text : Result → String
  | .delivered => "delivered"
  | .deliveredAfterRefresh => "delivered after device refresh"
  | .deliveredAfterIdentityChange => "delivered after identity change"
  | .retryLater => "retry later"
  | .needsSignup => "needs re-signup"
  | .gone => "gone"
  | .fault => "fault"

def Result.ofText? (text : String) : Option Result := Result.all.find? (·.text == text)

def Result.isDelivered : Result → Bool
  | .delivered | .deliveredAfterRefresh | .deliveredAfterIdentityChange => true
  | _ => false

/-- Settled for this notify: a later session for the same notify does not send it again. -/
def Result.settled : Result → Bool
  | .retryLater | .fault => false
  | _ => true

/-- No further send to this contact in this session. -/
def Result.stops : Result → Bool
  | .needsSignup | .gone | .fault => true
  | _ => false

inductive Action where
  | done | refresh | backOff | stop (result : Result)
  deriving BEq, Repr

/-- From the status of the response to a send. -/
def onSend (status : Nat) : Action :=
  if 200 ≤ status && status < 300 then .done
  else if status == 409 || status == 410 then .refresh
  else if status == 429 || (500 ≤ status && status < 600) then .backOff
  else if status == 401 then .stop .needsSignup
  else if status == 404 then .stop .gone
  else .stop .fault

/-- From the status of the response to a prekey fetch. -/
def onFetch (status : Nat) : Action :=
  if status == 200 then .done
  else if status == 429 || (500 ≤ status && status < 600) then .backOff
  else if status == 401 then .stop .needsSignup
  else if status == 404 then .stop .gone
  else .stop .fault

/-- Refreshes after the first, for one message. -/
def refreshRetries : Nat := 2
def transientRetries : Nat := 3
def reconnects : Nat := 2
/-- Waits (milliseconds) before retry 1, 2, 3 when the response names none. -/
def schedule : List Nat := [1000, 3000, 9000]
/-- The longest wait a session accepts; a longer `Retry-After` is left to the application. -/
def longestWait : Nat := 60000

/-- The wait before retry number `attempt` (from 0), or `none`: give the contact up as
"retry later". -/
def delay (attempt : Nat) (retryAfter : Option Nat) : Option Nat :=
  if attempt ≥ transientRetries then none else
  match retryAfter with
  | some seconds => if seconds * 1000 ≤ longestWait then some (max 200 (seconds * 1000)) else none
  | none => schedule[attempt]?

/-- How a refresh of a contact's sessions ended. `ok`: the new device list is stored and is the
contact's state (`changed`: under a new identity key). In every other case nothing was stored
and the contact is as before. -/
inductive Refreshed where
  | ok (changed : Bool)
  | lost                                             -- the connection was closed meanwhile
  | stop (result : Result) (reason : String)
  | transient (status : Nat) (retryAfter : Option Nat)

/-- One result line: (message number within the notify, contact id, result, reason). -/
abbrev Entry := Nat × Nat × Result × String

/-- The results as the bytes whose digest the two controllers compare before reporting. -/
def canonical (entries : List Entry) : String :=
  String.join (entries.map fun (message, contact, result, reason) => s!"{message}\t{contact}\t{result.text}\t{reason}\n")

/-- A journal line: a settled result of notify `notify` (PRODUCT_TODO.md section 4, "what was
confirmed"). Each computation node appends these to its own journal; a later session for the
same notify skips an entry only when BOTH nodes' journals have it. -/
def journalLine (notify : String) (entry : Entry) : String :=
  (Lean.Json.mkObj [("notify", toJson notify), ("message", toJson entry.1), ("id", toJson (toString entry.2.1)),
    ("result", toJson entry.2.2.1.text)]).compress

def journalEntries (notify text : String) : List (Nat × Nat × Result) :=
  (text.splitOn "\n").filterMap fun line =>
    match Lean.Json.parse line with
    | .error _ => none
    | .ok json =>
      match json.getObjValAs? String "notify", json.getObjValAs? Nat "message", json.getObjValAs? String "id",
          json.getObjValAs? String "result" with
      | .ok named, .ok message, .ok id, .ok result =>
        if named != notify then none else
        match id.toNat?, Result.ofText? result with
        | some contact, some result => if result.settled then some (message, contact, result) else none
        | _, _ => none
      | _, _, _, _ => none

/-! Unit check (`public_service_controller recovery-check`): the table above, and the response
parser on server responses built here — a 429 with `Retry-After`, a 503 without, a 409 with a
body — fed as the session feeds them: a body byte is never given to `step`. -/

private def bytesOf (s : String) : List (BitVec 8) := s.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- An unmasked server frame carrying a response. -/
def responseFrame (id status : Nat) (message : String) (body : List (BitVec 8)) (headers : List String) : List (BitVec 8) :=
  let inner := [0x08] ++ PublicReceive.varint id ++ [0x10] ++ PublicReceive.varint status ++
    [0x1a] ++ PublicReceive.varint message.utf8ByteSize ++ bytesOf message ++
    (if body.isEmpty then [] else [0x22] ++ PublicReceive.varint body.length ++ body) ++
    headers.flatMap (fun header => [0x2a] ++ PublicReceive.varint header.utf8ByteSize ++ bytesOf header)
  let payload := [0x08, 0x02, 0x1a] ++ PublicReceive.varint inner.length ++ inner
  (if payload.length < 126 then [0x82, BitVec.ofNat 8 payload.length]
    else [0x82, 126, BitVec.ofNat 8 (payload.length / 256), BitVec.ofNat 8 payload.length]) ++ payload

/-- Feed a frame to a connection awaiting response `id`. Returns the final state, whether the
response completed, and how many bytes were passed over unrevealed. -/
def feed (lenient : Bool) (id : Nat) (frame : List (BitVec 8)) : Except String (PublicReceive.State × Bool × Nat) := do
  let mut s := PublicReceive.expect { PublicReceive.start [] with upgraded := true, lenient } id
  let mut complete := false
  let mut passed := 0
  for byte in frame do
    if s.skip > 0 then
      let (next, done) ← PublicReceive.stepPassed s
      s := next
      complete := complete || done
      passed := passed + 1
    else
      unless PublicReceive.mayReveal s do throw "may not reveal"
      let (next, done) ← PublicReceive.step s byte
      s := next
      complete := complete || done
  return (s, complete, passed)

/-- `feed`'s walk from any state, without its reveal check, with the record loop's pass-over when
`bulk` (a run of body bytes passed over with `passBulk` as far as `passRoom` allows, the rest one
at a time) or one byte at a time otherwise. Measurement and cross-check only (`parse-bench`). -/
def walk (bulk : Bool) (start : PublicReceive.State) (frame : List (BitVec 8)) :
    Except String (PublicReceive.State × Bool × Nat) := do
  let mut s := start
  let mut complete := false
  let mut passed := 0
  let mut rest := frame
  for _ in [0:frame.length] do
    match rest with
    | [] => break
    | byte :: tail =>
      if s.skip > 0 then
        let count := if bulk then min rest.length (PublicReceive.passRoom s) else 0
        if count > 0 then
          s := PublicReceive.passBulk count s
          passed := passed + count
          rest := rest.drop count
        else
          let (next, done) ← PublicReceive.passOne s
          s := next
          complete := complete || done
          passed := passed + 1
          rest := tail
      else
        let (next, done) ← PublicReceive.step s byte
        s := next
        complete := complete || done
        rest := tail
  return (s, complete, passed)

/-- What `parse-bench` compares of two walks' results. -/
def digest : Except String (PublicReceive.State × Bool × Nat) →
    Option ((List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) ×
      (Nat × List (BitVec 8) × List (List (BitVec 8)) × Bool × Nat × Bool × Nat))
  | .ok (s, complete, passed) =>
    some ((s.frame, s.control, s.response, s.upgrade),
      (s.skip, s.message, s.requests, s.pending, s.status, complete, passed))
  | .error _ => none

set_option compiler.extract_closed false in   -- a function, so that nothing is evaluated at program start
def checks (_ : Unit) : List (String × Bool) :=
  let parsed (lenient : Bool) (frame : List (BitVec 8)) (want : PublicReceive.State → Bool) (passed : Nat) : Bool :=
    match feed lenient 77 frame with
    | .ok (s, complete, count) => complete && want s && count == passed
    | .error _ => false
  [ ("send 200 is delivered", onSend 200 == .done),
    ("send 204 is delivered", onSend 204 == .done),
    ("send 409 refreshes", onSend 409 == .refresh),
    ("send 410 refreshes", onSend 410 == .refresh),
    ("send 429 backs off", onSend 429 == .backOff),
    ("send 500 backs off", onSend 500 == .backOff),
    ("send 503 backs off", onSend 503 == .backOff),
    ("send 401 needs re-signup", onSend 401 == .stop .needsSignup),
    ("send 404 is gone", onSend 404 == .stop .gone),
    ("send 413 is a fault", onSend 413 == .stop .fault),
    ("send 428 is a fault", onSend 428 == .stop .fault),
    ("fetch 200 continues", onFetch 200 == .done),
    ("fetch 401 needs re-signup", onFetch 401 == .stop .needsSignup),
    ("fetch 404 is gone", onFetch 404 == .stop .gone),
    ("fetch 429 backs off", onFetch 429 == .backOff),
    ("fetch 503 backs off", onFetch 503 == .backOff),
    ("fetch 409 is a fault", onFetch 409 == .stop .fault),
    ("fixed schedule", [delay 0 none, delay 1 none, delay 2 none, delay 3 none] == [some 1000, some 3000, some 9000, none]),
    ("Retry-After is honoured", delay 0 (some 7) == some 7000 && delay 2 (some 1) == some 1000),
    ("a long Retry-After gives up", delay 0 (some 3600) == none),
    ("retries are bounded with Retry-After too", delay 3 (some 1) == none),
    ("429 with Retry-After parses", parsed true (responseFrame 77 429 "Too Many Requests" [] ["Retry-After:7"])
      (fun s => s.status == 429 && s.retryAfter == some 7) 0),
    ("header name case and spaces", parsed true (responseFrame 77 429 "x" [] ["Content-Length:0", "retry-after: 12"])
      (fun s => s.status == 429 && s.retryAfter == some 12) 0),
    ("503 without the header", parsed true (responseFrame 77 503 "Service Unavailable" [] [])
      (fun s => s.status == 503 && s.retryAfter == none) 0),
    ("409: its body is passed over, not revealed", parsed true
      (responseFrame 77 409 "Conflict" (bytesOf "{\"missingDevices\":[2],\"extraDevices\":[]}") ["Content-Type:application/json"])
      (fun s => s.status == 409 && s.bundle == none) 40),
    ("a failure is refused without leniency", (feed false 77 (responseFrame 77 429 "x" [] [])).toOption.isNone),
    ("another request's response is refused", (feed true 77 (responseFrame 78 200 "OK" [] [])).toOption.isNone),
    ("results text", canonical [(0, 5, .delivered, ""), (1, 5, .needsSignup, "status 401")] ==
      "0\t5\tdelivered\t\n1\t5\tneeds re-signup\tstatus 401\n"),
    ("journal round trip", journalEntries "n1" (journalLine "n1" (1, 5, .deliveredAfterRefresh, "") ++ "\n" ++
      journalLine "n2" (0, 6, .delivered, "") ++ "\n" ++ journalLine "n1" (0, 7, .retryLater, "") ++ "\nnot json\n") ==
      [(1, 5, .deliveredAfterRefresh)]) ]

end Recovery
