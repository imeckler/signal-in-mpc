import TlsMpc.RecordClassKernels

/-!
Opening a received TLS application-phase record in two steps, so that the
framing scan for post-handshake HANDSHAKE messages (KeyUpdate, NewSessionTicket)
runs only on handshake records. `tls-open-application-class CAP` runs that scan
over every record (about 640 of its 935 AND gates per byte), although almost
every record is application data.

* `tls-open-typed CAP` decrypts and parses the record exactly as
  `tls-open-application-class CAP` does (`RecordClass.openParsed`: CTR
  decryption, header check, inner type and padding, all released under the
  private tag-check mask `accepted` from `gcm-check`) and opens ONE BIT first,
  `handshake`: 255 when the parse's type byte is 22, else 0. Beside it, it
  computes what the post-handshake parser gives when its scan does not run
  (`TypedOpen.direct`): `event`, `parser`, `length`, `content`, as the class
  kernel names them. It also returns the private parse (`parsed`).
* `tls-frame CAP`, run only when the bit is 255: the post-handshake parser
  (`TlsPostHandshake.Fast.core`, scan included) on the previous parser state and
  that private parse. Its outputs replace the first kernel's.

The worker opens `handshake`; when it is 0 it opens the first kernel's `event`
and keeps its `parser`, `length`, `content`; when it is 255 it runs `tls-frame`
and opens and keeps that kernel's instead. The record is decrypted once.

WHAT THE NODES LEARN THAT THEY DID NOT BEFORE. One bit per received record:
"this record authenticated, its header and inner plaintext are well formed, and
its inner content type is handshake".

* For a record that fails authentication (`accepted` = 0), whatever its bytes:
  nothing. The parse is all zero, the bit is 0 and the event is `[0, 0]`, as the
  class kernel's event is (`TypedOpenProofs`: `rejected_parse`, `gating`,
  `tlsOpenTyped_gated`). The bit is a function of the parse alone, and every
  byte of the parse is ANDed with `accepted`; AES-GCM without its tag is
  malleable, so nothing derived from a decryption may be opened otherwise.
* For an authenticated record: whether it is a handshake record. With the
  class kernel's event alone a handshake record that is skipped (a session
  ticket, a fragment) and an ignored `user_canceled` alert both show as event 2,
  and every record the parser rejects after authentication (a malformed
  handshake message, an alert of another kind, a record after an earlier
  error) shows as event 0; the bit now separates the handshake records among
  them. Application data (event 1), KeyUpdate (event 3) and `close_notify`
  (event 4) already determined the type. Nothing about contents or lengths.

REFINEMENT (`TypedOpenProofs`: `direct_eq`, `frame_eq`, `typed_pair_refines`).
The bit is 0 or 255. When it is 0, the first kernel's four fields are the class
kernel's on the same inputs. When it is 255, `tls-frame` on the same parser
state and the first kernel's parse gives the class kernel's four fields. When
the bit is 255 the first kernel's own `event` is forced to `[0, 0]` (it is never
opened then).
-/
namespace TlsMpc.TypedOpen
open Std.Tactic.BVDecide
open TlsPostHandshake Signal.Word64

/-- The opened bit: the parse's type byte is 22 (handshake). `parsed` is
`TlsReceive.releaseOpened`'s layout: acceptance, type, length (2), content;
every byte of it is zero unless the record authenticated. -/
def handshakeBit (a : ByteAuth.Ops B) (parsed : List B) : B :=
  ByteAuth.eqMask a (get a parsed 1) (a.const 22)

/-- The post-handshake parser without its scan: `TlsPostHandshake.finish` on the
unchanged state. For a parse whose type is not handshake this is the whole
parser (`TypedOpenProofs.direct_eq`). The two event bytes are released only
when the bit is 0. Layout as `TlsPostHandshake.core`: event (2), state (11),
length (2), content. -/
def direct (o : Ops B W) (a : ByteAuth.Ops B) (state parsed : List B) : List B :=
  let s := decodeState o a state
  let out := finish o a s parsed ⟨s, a.const 0, a.const 0⟩
  ByteAuth.release a (a.not (handshakeBit a parsed)) (out.take 2) ++ out.drop 2

end TlsMpc.TypedOpen

namespace TlsMpc.TypedOpenKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup pub priv sl blockKey blockIv gcmExpanded)

/-- The inputs of `tls-open-typed`: those of `tls-open-application-class`. -/
def typedInputs (capacity : Nat) : List (String × Shape) :=
  [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
    ("record", .bytes capacity), ("size", .bytes 2), ("accepted", .bytes 1)]

/-- The parse of the record, the expression `tls-open-application-class` hands
to the post-handshake parser. -/
def typedParsed (capacity : Nat) : List (BVExpr 8) :=
  let get := lookup (typedInputs capacity)
  let block := get "serverApplication"
  RecordClass.openParsed Gcm.symbolic ByteAuth.symbolic (gcmExpanded block)
    (TlsRecord.nonce Gcm.symbolic (blockIv block) (get "sequence"))
    (get "record") (HybridService.at' (get "size") 0) (HybridService.at' (get "size") 1)
    (HybridService.at' (get "accepted") 0)

/-- Decrypt and parse one record; open whether it is an authenticated
handshake record, and give the parser's result for one that is not. -/
def tlsOpenTyped (capacity : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let parsed := typedParsed capacity
  let out := TypedOpen.direct Word64.symbolicMux a (lookup (typedInputs capacity) "parser") parsed
  { name := "tls-open-typed", inputs := typedInputs capacity, outputs := [
      pub "handshake" [TypedOpen.handshakeBit a parsed],
      pub "event" (sl out 0 2), priv "parser" (sl out 2 11), priv "length" (sl out 13 2), priv "content" (out.drop 15),
      priv "parsed" parsed] }

/-- The inputs of `tls-frame`: the parser state and the private parse of
`tls-open-typed` for the same capacity (`capacity - 17` bytes). -/
def frameInputs (capacity : Nat) : List (String × Shape) :=
  [("parser", Shape.bytes 11), ("parsed", .bytes (capacity - 17))]

/-- The post-handshake parser, scan included, on a private parse. -/
def tlsFrame (capacity : Nat) : Kernel :=
  let get := lookup (frameInputs capacity)
  let out := TlsPostHandshake.Fast.core Word64.symbolicMux ByteAuth.symbolic (get "parser") (get "parsed")
  { name := "tls-frame", inputs := frameInputs capacity, outputs := [
      pub "event" (sl out 0 2), priv "parser" (sl out 2 11), priv "length" (sl out 13 2), priv "content" (out.drop 15)] }

/-- Kernel named on the command line: `tls-open-typed CAP` and `tls-frame CAP`,
for the capacities `tls-open-application-class` accepts. -/
def find : List String → Option Kernel
  | [name, a] =>
      match name, a.toNat? with
      | "tls-open-typed", some n =>
          if RecordClass.capacity n == n && n ≤ RecordClass.capacity 16406 then some (tlsOpenTyped n) else none
      | "tls-frame", some n =>
          if RecordClass.capacity n == n && n ≤ RecordClass.capacity 16406 then some (tlsFrame n) else none
      | _, _ => none
  | _ => none

end TlsMpc.TypedOpenKernel
