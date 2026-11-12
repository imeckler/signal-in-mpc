import TlsMpc.Node.Policy.ReceiveProofs

/-!
# T1's property test: the deployed reveal policy against the reference, on generated streams

REORGANIZATION_PLAN.md proof track P1 ("extend `Recovery.checks` into a property test"). New file;
pure (no I/O). `checks ()` returns named results like `Recovery.checks`; every entry is `true` when
the policy behaves as T1 says. No emitter or executable imports this module; to run it, evaluate
`ReceiveTest.failures ()` (the names of the failing checks, expected `[]`) from any Lean file that
imports it.

Streams are generated from a seed (a linear congruential generator): server requests (delivered
envelopes with every wire type, `queue/empty`, other paths, with and without bodies), responses
(with and without bodies, success and failure), pings, messages fragmented over several frames with
pings in between, all cut into records at random places. For each stream:

* **safety** (`safe`): every position the record loop reveals (`ReceiveProofs.streamRun`, the
  controller's loop modelled, including runs whose check fails) is allowed by the reference
  (`ReceiveSpec.classifyFrames`), or is the one byte right after the first malformed byte;
* **liveness** (`live`, on the well-formed streams): the loop does not fail, and it reveals exactly
  the positions the reference allows. The generator never cuts a message into frames inside a body
  or an envelope field's payload (`cutAllowed`): the controller requires each of those to lie in
  one frame and refuses the stream otherwise (`splitBody`: safe, not live).

Malformed streams are the well-formed ones with one byte changed, one byte inserted or one byte
removed; only safety is checked on them. `counterexamples` are hand-made streams on which the
policy reveals secret bytes (see the section at the end).
-/

namespace ReceiveTest

open PublicReceive ReceiveProofs
open ReceiveSpec (classifyFrames allowedIn firstError)

/-! ### Encoding -/

def bytesOf (s : String) : List Byte := s.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- A length-delimited field: key, length, content. -/
def delimited (key : List Byte) (content : List Byte) : List Byte := key ++ varint content.length ++ content
def number (key : List Byte) (value : Nat) : List Byte := key ++ varint value

/-- Unmasked server frames: `opcode` (2 binary, 0 continuation, 9 ping), FIN. -/
def frame (fin : Bool) (opcode : Nat) (payload : List Byte) : List Byte :=
  let b0 : Byte := BitVec.ofNat 8 ((if fin then 128 else 0) + opcode)
  (if payload.length < 126 then [b0, BitVec.ofNat 8 payload.length]
   else [b0, 126, BitVec.ofNat 8 (payload.length / 256), BitVec.ofNat 8 payload.length]) ++ payload

def requestMessage (fields : List Byte) : List Byte := [8, 1, 0x12] ++ varint fields.length ++ fields
def responseMessage (fields : List Byte) : List Byte := [8, 2, 0x1a] ++ varint fields.length ++ fields

/-! ### A pseudo-random source -/

structure Gen where
  seed : Nat

def Gen.next (g : Gen) : Nat × Gen :=
  let s := (g.seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  (s / 2 ^ 33, ⟨s⟩)

/-- A number below `n` (`n > 0`). -/
def Gen.below (g : Gen) (n : Nat) : Nat × Gen := let (x, g) := g.next; (x % n, g)

def Gen.bytes (g : Gen) : Nat → List Byte × Gen
  | 0 => ([], g)
  | n + 1 => let (x, g) := g.below 256; let (rest, g) := g.bytes n; (BitVec.ofNat 8 x :: rest, g)

/-- Printable bytes (header values, paths). -/
def Gen.text (g : Gen) : Nat → List Byte × Gen
  | 0 => ([], g)
  | n + 1 => let (x, g) := g.below 94; let (rest, g) := g.text n; (BitVec.ofNat 8 (x + 32) :: rest, g)

def Gen.pick {α : Type} (g : Gen) (xs : List α) (default : α) : α × Gen :=
  let (i, g) := g.below (max xs.length 1); (xs.getD i default, g)

/-! ### Messages -/

/-- A delivered envelope: type, timestamps, flags, a fixed64 and a fixed32 field, a server guid,
the sealed content, a two-byte key (field 16), an empty field, in an order that varies. (Never two
content fields: the controller refuses an envelope with a second one, which is safe.) -/
def Gen.envelope (g : Gen) : List Byte × Gen := Id.run do
  let mut g := g
  let (kind, g1) := g.pick [6, 6, 1, 3] 6; g := g1
  let (contentLength, g2) := g.below 300; g := g2
  let (content, g3) := g.bytes contentLength; g := g3
  let (guid, g4) := g.text 36; g := g4
  let (time, g5) := g.next; g := g5
  let (fixed, g6) := g.bytes 8; g := g6
  let (fixed4, g7) := g.bytes 4; g := g7
  let fields : List (List Byte) :=
    [number [0x08] kind, number [0x28] time, delimited [0x42] content, delimited [0x4a] guid,
     number [0x50] (time + 7), [0x61] ++ fixed, [0x6d] ++ fixed4, number [0x80, 0x01] 1, delimited [0x3a] []]
  let (rotate, g8) := g.below fields.length; g := g8
  return (((fields.drop rotate) ++ (fields.take rotate)).flatten, g)

/-- A server request: a delivered message (envelope body), `queue/empty`, or another path with an
opaque body; fields in the server's order (verb, path, body, id, headers), sometimes without
body or headers. -/
def Gen.request (g : Gen) : List Byte × Gen := Id.run do
  let mut g := g
  let (which, g1) := g.below 4; g := g1
  let (id, g2) := g.next; g := g2
  let (header, g3) := g.text 20; g := g3
  let (path, body, g4) :=
    if which < 2 then let (e, g) := g.envelope; ("/api/v1/message", e, g)
    else if which = 2 then ("/api/v1/queue/empty", [], g)
    else let (n, g) := g.below 200; let (b, g) := g.bytes n; ("/v1/other", b, g)
  g := g4
  let fields := delimited [0x0a] (bytesOf "PUT") ++ delimited [0x12] (bytesOf path) ++
    (if body.isEmpty then [] else delimited [0x1a] body) ++ number [0x20] id ++
    (if which = 1 then [] else delimited [0x2a] header)
  return (requestMessage fields, g)

/-- A response: id, status, message, a body or none, headers. -/
def Gen.response (g : Gen) : List Byte × Gen := Id.run do
  let mut g := g
  let (id, g1) := g.next; g := g1
  let (status, g2) := g.pick [200, 200, 204, 409, 410, 429, 503] 200; g := g2
  let (bodyLength, g3) := g.below 400; g := g3
  let (body, g4) := g.bytes bodyLength; g := g4
  let (withBody, g5) := g.below 3; g := g5
  let (header, g6) := g.text 15; g := g6
  let fields := number [0x08] id ++ number [0x10] status ++ delimited [0x1a] (bytesOf "OK") ++
    (if withBody = 0 then [] else delimited [0x22] body) ++ delimited [0x2a] (bytesOf "Retry-After:" ++ header)
  return (responseMessage fields, g)

/-- Whether a message may be cut into two frames before its byte `p`: never inside a body or an
envelope's field payload (the controller requires each of those to lie in one frame, and refuses
the stream otherwise, which is safe but not live). -/
def cutAllowed (payload : List Byte) (p : Nat) : Bool :=
  match (ReceiveSpec.message false payload)[p]? with
  | some c => !c.secret
  | none => true

/-- A message as frames: one frame, or cut into up to three fragments (never inside a body),
sometimes with a ping between two of them. -/
def Gen.frames (g : Gen) (payload : List Byte) : List Byte × Gen := Id.run do
  let mut g := g
  let (cuts, g1) := g.below 3; g := g1
  if cuts = 0 || payload.length < 4 then return (frame true 2 payload, g)
  let (a, g2) := g.below payload.length; g := g2
  let (b, g3) := g.below payload.length; g := g3
  let a := if cutAllowed payload a then a else 0
  let b := if cutAllowed payload b then b else payload.length
  let (lo, hi) := (min a b, max a b)
  let (ping, g4) := g.below 2; g := g4
  let (pingPayload, g5) := g.bytes 3; g := g5
  return (frame false 2 (payload.take lo) ++ (if ping = 0 then frame true 9 pingPayload else []) ++
    frame false 0 ((payload.drop lo).take (hi - lo)) ++ frame true 0 (payload.drop hi), g)

/-- A stream of a few messages and pings. -/
def Gen.stream (g : Gen) : List Byte × Gen := Id.run do
  let mut g := g
  let (count, g1) := g.below 4; g := g1
  let mut out : List Byte := []
  for _ in [0:count + 1] do
    let (which, g2) := g.below 5; g := g2
    if which = 4 then
      let (p, g3) := g.bytes 4; g := g3
      out := out ++ frame true 9 p
    else
      let (m, g3) := if which < 2 then g.request else g.response; g := g3
      let (f, g4) := g.frames m; g := g4
      out := out ++ f
  return (out, g)

/-- Cut a stream into records of random sizes (1 to 600 bytes). -/
def Gen.records (g : Gen) : (fuel : Nat) → List Byte → List (List Byte) × Gen
  | 0, bytes => ([bytes], g)
  | fuel + 1, bytes =>
    if bytes.isEmpty then ([], g) else
    let (n, g) := g.below 600
    let (rest, g) := g.records fuel (bytes.drop (n + 1))
    (bytes.take (n + 1) :: rest, g)

/-- One byte changed, inserted or removed (at a random place). -/
def Gen.mutate (g : Gen) (bytes : List Byte) : List Byte × Gen := Id.run do
  let mut g := g
  let (how, g1) := g.below 3; g := g1
  let (at_, g2) := g.below (max bytes.length 1); g := g2
  let (x, g3) := g.below 256; g := g3
  let b : Byte := BitVec.ofNat 8 x
  let out := match how with
    | 0 => bytes.take at_ ++ [b] ++ bytes.drop (at_ + 1)
    | 1 => bytes.take at_ ++ [b] ++ bytes.drop at_
    | _ => bytes.take at_ ++ bytes.drop (at_ + 1)
  return (out, g)

/-! ### The comparison -/

/-- The connection after the upgrade, no request pending (as `Recovery.feed`, without `expect`). -/
def upgraded (openBody : Bool) : State := { start [] with upgraded := true, lenient := true, openBody }

/-- Every revealed position is allowed, or is the byte right after the first malformed one. -/
def safe (openBody : Bool) (records : List (List Byte)) : Bool :=
  let classes := classifyFrames openBody records.flatten
  (streamRun (upgraded openBody) records).1.all fun q => allowedIn classes q || firstError classes == some q

/-- The loop does not fail and reveals exactly the allowed positions. -/
def live (openBody : Bool) (records : List (List Byte)) : Bool :=
  let stream := records.flatten
  let classes := classifyFrames openBody stream
  let (revealed, result) := streamRun (upgraded openBody) records
  result.toOption.isSome && revealed == (List.range stream.length).filter (allowedIn classes)

/-- `count` generated streams from `seed`: (well-formed safe, well-formed live, mutated safe), as
the seeds that fail. -/
def run (openBody : Bool) (seed count : Nat) : List Nat × List Nat × List Nat := Id.run do
  let mut g : Gen := ⟨seed⟩
  let mut bad : List Nat × List Nat × List Nat := ([], [], [])
  for i in [0:count] do
    let (stream, g1) := g.stream; g := g1
    let (records, g2) := g.records (stream.length + 1) stream; g := g2
    let (mutated, g3) := g.mutate stream; g := g3
    let (mrecords, g4) := g.records (mutated.length + 1) mutated; g := g4
    if !safe openBody records then bad := (bad.1 ++ [i], bad.2)
    if !live openBody records then bad := (bad.1, bad.2.1 ++ [i], bad.2.2)
    if !safe openBody mrecords then bad := (bad.1, bad.2.1, bad.2.2 ++ [i])
  return bad

/-! ### Counterexamples: secret bytes the policy reveals

**A varint of more than 10 bytes.** `varintAt` reads at most 10 bytes and returns `none` both when
the bytes end inside a varint and when the varint is longer; the scanners (`scan`, `replyScan`,
`envelopeScan`, `fieldMissing`, `replyBudget`) take `none` as "not complete yet" and ask for the
next byte. So once the server sends an 11-byte varint where a request's (or response's) wrapper
length, a field length or the id is expected, the scanners never see another field: the body's key
is not recognised, `skip` is never set, and every remaining payload byte of the message is revealed
one at a time. The message then completes normally. On the stream below (a delivered message whose
wrapper length is written in 11 bytes), every byte is revealed, the envelope's sealed content
included. -/

/-- A delivered message with a sealed content `AA BB CC DD`, whose request length is an 11-byte
varint. -/
def overlongRequest : List Byte :=
  let envelope := number [0x08] 6 ++ delimited [0x42] [0xAA, 0xBB, 0xCC, 0xDD]
  let fields := delimited [0x0a] (bytesOf "PUT") ++ delimited [0x12] (bytesOf "/api/v1/message") ++
    delimited [0x1a] envelope ++ number [0x20] 5
  frame true 2 ([8, 1, 0x12] ++ List.replicate 10 0x80 ++ [0x00] ++ fields)

/-- A 200 response with a body, whose id is an 11-byte varint. -/
def overlongResponse : List Byte :=
  let fields := [0x08] ++ List.replicate 10 0xFF ++ [0x01] ++ number [0x10] 200 ++
    delimited [0x22] [0xAA, 0xBB, 0xCC, 0xDD]
  frame true 2 (responseMessage fields)

/-- The policy reveals a position the reference does not allow, beyond the one-byte grace. -/
def leaks (records : List (List Byte)) : Bool := !safe false records

/-- A response whose body is cut across two frames: the controller refuses it (fail closed: a
body must lie in one frame), and reveals none of the body. Safe, not live. -/
def splitBody : List Byte :=
  let payload := responseMessage (number [0x08] 1 ++ number [0x10] 200 ++ delimited [0x22] (List.replicate 40 0xAB))
  frame false 2 (payload.take 20) ++ frame true 0 (payload.drop 20)

def refusedSafely (records : List (List Byte)) : Bool :=
  safe false records && (streamRun (upgraded false) records).2.toOption.isNone

/-! ### The checks -/

set_option compiler.extract_closed false in
def checks (_ : Unit) : List (String × Bool) :=
  let (s1, l1, m1) := run false 1 100
  let (s2, l2, m2) := run true 2 40
  [ ("well-formed streams: safe", s1.isEmpty),
    ("well-formed streams: live", l1.isEmpty),
    ("mutated streams: safe", m1.isEmpty),
    ("openBody, well-formed: safe", s2.isEmpty),
    ("openBody, well-formed: live", l2.isEmpty),
    ("openBody, mutated: safe", m2.isEmpty),
    ("a body cut across frames is refused, unrevealed", refusedSafely [splitBody]),
    ("the same, cut into records", refusedSafely [splitBody.take 7, splitBody.drop 7]),
    ("counterexample reproduced: 11-byte request length reveals the sealed content", leaks [overlongRequest]),
    ("counterexample reproduced: 11-byte response id reveals the body", leaks [overlongResponse]) ]

def failures (_ : Unit) : List String := (checks ()).filterMap fun (name, ok) => if ok then none else some name

end ReceiveTest
