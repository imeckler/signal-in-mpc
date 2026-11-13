import TlsMpc.Node.Flows.Ghash
import TlsMpc.TypedOpenProofs
import TlsMpc.KernelSpecs.TlsHandshakeKernels
import TlsMpc.KernelSpecs.RevealMasked

/-!
# `Tls.*`: the TLS 1.3 client's engine part as scripts (handshake, record seal and open, key
# update, server-byte reveal, buffers)

REORGANIZATION_PLAN.md stage S12. Replaces `handshake_backend/EmpHybridWork/tls_kernels.h`
(`derive`, `open_handshake`, `verify_finished`, `finish`, `retire`, `open_application`,
`seal_application`, `tagged`, `seal_control`, `reveal_range`, `public_buffer`, `rotate`, lines
112-298) and the TLS dispatch of `tls_worker_v3.cpp` (ops 2-7, 12-16, 30, 43; the 64-record window
and the drop-after-seal rule of lines 318-338). Advance work in a new file; the C++ stays in use
until the controller switches (the backends of `Flows/TlsBackend.lean` are selectable, not
selected). The X25519 agreement is NOT here: it is S11's (`Flows/Curve.lean`), a parameter of the
backend (`TlsBackend.KeyAgreement`, S12_NOTES.md).

THE SCRIPTS (Boolean handles; `n` the session's next free handle id; bits of bytes least
significant first; every kernel by its cache name; every opening labelled by its reveal kind):

  Seal (`tagged` + `seal_control` / `seal_application`, ops 13, 14), three phases:
    `sealCtrScript n traffic content seq kind size padding`: public seq; concat traffic ‖ seq ‖
    content; run `tls-seal-ctr kind size padding` (header 5, ciphertext L = size+1+padding: public;
    pad 16: private); slice the pad (kept), slice header ‖ ciphertext and OPEN it (sealedRecord).
    `sealClassScript …` the same with `tls-seal-class CAP` (content padded with zeros to the class
    capacity, the header's length field public; opens accepted ‖ header ‖ ciphertext in one
    opening; aborts unless accepted = 255; keeps the first size+1 ciphertext bytes).
    Then, OUTSIDE the script (`TlsBackend`): enough key-power shares (Flows/Ghash), and this party's
    half over the opened header and ciphertext (`Local.Ghash.half`) into a store slot.
    `tagScript n pad halfSlot`: both halves in (boolInputBoth, once), concat pad ‖ A's ‖ B's, run
    `gcm-tag`, free the pad, OPEN the tag (sealedRecord). Record = header ‖ ciphertext ‖ tag.
  Open (`open_application`, op 12): the halves first (local, over the public received header and
    ciphertext), then
    `openScript n parser traffic seq tag recordPadded size cap halfSlot`: public seq; halves in;
    public tag; run `gcm-check` (accepted: private); public record ‖ size; run `tls-open-typed CAP`
    on parser ‖ traffic ‖ seq ‖ record ‖ size ‖ accepted; OPEN the handshake bit (recordKindBit);
    bit 0: OPEN the typed kernel's event (recordEvent), keep its parser, length, content; bit 255:
    run `tls-frame CAP` on the old parser and the private parse, OPEN its event, keep its parser,
    length, content; any other bit: abort. Returns the event bytes and the three new handles.
  `parserScript n`: `tls-parser-initial` (a private zero state).
  Key update (`rotate`, ops 15, 16): `updateScript n traffic`: run `tls-update`, free the old
    block. The direction's GHASH shares are dropped by the backend (they belong to the old key).
  Server-byte reveal (`reveal_range`, op 43): `revealScript n length content cap`: run
    `tls-reveal-masked CAP` on length ‖ content, OPEN the length (serverBytes), keep the masked
    bytes (public marks: zero at and past the length). `rangeScript n bytes lo hi`: OPEN the slice
    [lo, hi) of those bytes (serverBytes). The CALLER keeps to T1's budget (see `revealRange` in
    TlsBackend.lean).
  `publicScript n bytes` (`public_buffer`, op 30): public bits as a buffer; nothing opened.
  Handshake (ops 2-7): `deriveScript n agreement helloHash` (`tls-derive` on the agreement word ‖
    the public hash; keeps the client and server handshake blocks and the main secret; frees the
    agreement), `openHandshakeScript n serverHs seq record` (`tls-open-handshake |record|`, OPEN its
    gated result: handshakeRecord), `verifyScript n serverHs hash message` (`tls-verify-finished`,
    OPEN the acceptance byte: finishedAccepted), `finishScript n main serverHash clientHs
    clientHash certificate` (`tls-finish |certificate|`; keeps the application blocks, OPENS the
    client Finished record: clientFinished), `agreeScript n digest valid` (the certificate check's
    request digest and decision as public bits: agreed through the batch skeleton, op 4's
    "identical request incl. each party's own decision", nothing released).
  `dropScript hs`: free handles (retire, abort, the window, drop-after-seal).

THE STATE (to live in `Session/Pool`, replacing the C++ `Parked`; S12_NOTES.md): `Conn` (one TLS
connection's handles and its two directions' GHASH `Secret` shares) and `Buffers` (the session's
private buffers by public id, with the 64-record window `Window` and the drop-after-seal rule).

PROVED (ideal model; the kernels' circuits compute their Lean definitions; S12_NOTES.md lists
what is open). Here: the kinds, `seal_is_record`, the window and `Buffers.remove_gone`; the open,
reveal, handshake and WF statements below are in `Flows/TlsProofs.lean`:
  T3: `*_reveals` for every script (the kinds of `tlsKinds`; registered in Flows/Registry.lean).
  T4-TLS, seal: `seal_is_record`: header ‖ ciphertext of `tls-seal-ctr` followed by `gcm-tag` on
    its pad and the two parties' halves `Local.Ghash.half` of shares that share H¹ … Hⁿ (P-GHASH
    (a)) is `TlsRecord.sealCore`: `sealCtr_with_tag_is_seal` with its `halves` hypothesis
    DISCHARGED by P-GHASH (c) (`Local.Ghash.halves_xor`).
  T4-TLS, open: `check_accepts` (the private acceptance byte is 255 exactly when the received tag
    is GCM's tag of the header and ciphertext under the server key, for honest shares),
    `open_event_refines` (`typed_pair_refines`, `class_fields`: what the script opens and keeps is
    the single class kernel's event and fields), `open_rejected` (`tlsOpenTyped_gated`: a
    rejected record opens bit 0 and event [0, 0]).
  Reveal: `reveal_value` (`tlsRevealMasked_value`).
  Handshake: `openHandshake_value` (`tlsOpenHandshake_spec`), `verify_value`
    (`tlsVerifyFinished_spec`: 255 iff the message is the server Finished), `finish_value`
    (`tlsFinish_spec`: the record is the client Finished sealed under the client handshake key).
  Window: `Window.push_bound` (at most 64 kept), `Window.push_newest` (the newest is kept),
    `Window.push_partition` (kept and dropped are exactly the old ones and the new one).
  WF: `sealCtrScript_wf`, `tagScript_wf`, `updateScript_wf`, `publicScript_wf`, `rangeScript_wf`,
    `dropScript_wf`.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open Std.Tactic.BVDecide

abbrev W := BitVec 128

/-! ## Names and labels -/

def sealCtrName (kind size padding : Nat) : Bytes := name3 "tls-seal-ctr" kind size padding
def sealClassName (cap : Nat) : Bytes := name1 "tls-seal-class" cap
def tagName : Bytes := name0 "gcm-tag"
def checkName : Bytes := name0 "gcm-check"
def typedName (cap : Nat) : Bytes := name1 "tls-open-typed" cap
def frameName (cap : Nat) : Bytes := name1 "tls-frame" cap
def parserName : Bytes := name0 "tls-parser-initial"
def revealName (cap : Nat) : Bytes := name1 "tls-reveal-masked" cap
def updateName : Bytes := name0 "tls-update"
def deriveName : Bytes := name0 "tls-derive"
def openHsName (size : Nat) : Bytes := name1 "tls-open-handshake" size
def verifyName : Bytes := name0 "tls-verify-finished"
def finishName (cert : Nat) : Bytes := name1 "tls-finish" cert

/-- The record size classes (`RecordClass.capacity`, `tls_kernels.h` `record_capacity`). -/
def capacity (n : Nat) : Nat := RecordClass.capacity n

/-! ## The scripts: seal -/

/-- The TLSInnerPlaintext length of a record: content, type byte, padding. -/
def innerLength (size padding : Nat) : Nat := size + 1 + padding

/-- **Seal, first phase** (`tls-seal-ctr`): returns the opened header ‖ ciphertext and the pad's
handle `n + 3` (private, for `tagScript`). `content` holds `8 · size` bits. Uses ids `n … n+4`. -/
def sealCtrScript (n : Nat) (traffic content : BoolH) (seq : B8) (kind size padding : Nat) : Script (B8 × BoolH) :=
  seqs [.boolPublic ⟨n⟩ (bitsOf seq),
        .concat ⟨n + 1⟩ [traffic, ⟨n⟩, content],
        .run ⟨n + 2⟩ (sealCtrName kind size padding) 1 ⟨n + 1⟩,
        .slice ⟨n + 3⟩ ⟨n + 2⟩ (8 * (5 + innerLength size padding)) (8 * (5 + innerLength size padding + 16)),
        .slice ⟨n + 4⟩ ⟨n + 2⟩ 0 (8 * (5 + innerLength size padding)),
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩]
    (openThen ⟨n + 4⟩ Label.sealedRecord fun out =>
      seqs [.freeBool ⟨n + 4⟩] (.done (bytesOf out, ⟨n + 3⟩)))

/-- **Seal in a size class, first phase** (`tls-seal-class CAP`, `padding = 0`): the content
followed by zeros up to the capacity, the header's length field `size + 17` public. Opens
accepted ‖ header ‖ ciphertext; aborts unless accepted is 255; returns header ‖ the first
`size + 1` ciphertext bytes (the rest are zeros) and the pad's handle. Uses ids `n … n+5`. -/
def sealClassScript (n : Nat) (traffic content : BoolH) (seq : B8) (size : Nat) : Script (B8 × BoolH) :=
  let cap := capacity size
  seqs [.boolPublic ⟨n⟩ (bitsOf seq),
        .boolPublic ⟨n + 1⟩ (List.replicate (8 * (cap - size)) false ++
          bitsOf [BitVec.ofNat 8 ((size + 17) / 256), BitVec.ofNat 8 (size + 17)]),
        .concat ⟨n + 2⟩ [traffic, ⟨n⟩, content, ⟨n + 1⟩],
        .run ⟨n + 3⟩ (sealClassName cap) 1 ⟨n + 2⟩,
        .slice ⟨n + 4⟩ ⟨n + 3⟩ (8 * (1 + 5 + cap + 1)) (8 * (1 + 5 + cap + 1 + 16)),
        .slice ⟨n + 5⟩ ⟨n + 3⟩ 0 (8 * (1 + 5 + cap + 1)),
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩, .freeBool ⟨n + 3⟩]
    (openThen ⟨n + 5⟩ Label.sealedRecord fun out =>
      seqs [.freeBool ⟨n + 5⟩]
        (if (bytesOf out).take 1 = [255] then .done (((bytesOf out).drop 1).take (5 + size + 1), ⟨n + 4⟩)
         else .abort "sealed record size"))

/-- **Seal, last phase** (`gcm-tag`): both parties' halves (this party's 128 bits in `halfSlot`),
the pad; frees the pad; opens the tag. Uses ids `n … n+3`. -/
def tagScript (n : Nat) (pad : BoolH) (halfSlot : Nat) : Script B8 :=
  seqs [.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 128 true false halfSlot,
        .concat ⟨n + 2⟩ [pad, ⟨n⟩, ⟨n + 1⟩],
        .run ⟨n + 3⟩ tagName 1 ⟨n + 2⟩,
        .freeBool pad]
    (openThen ⟨n + 3⟩ Label.sealedRecord fun tag => seqs [.freeBool ⟨n + 3⟩] (.done (bytesOf tag)))

/-! ## The scripts: open -/

/-- What a record's opening leaves: the opened event bytes, and the new parser state, the
payload's length and content handles. -/
structure Opened where
  event : B8
  parser : BoolH
  length : BoolH
  content : BoolH

def checkBlock (n : Nat) (traffic : BoolH) (seq tag : B8) (halfSlot : Nat) : List Instr :=
  [.boolPublic ⟨n⟩ (bitsOf seq),
   .boolInputBoth ⟨n + 1⟩ ⟨n + 2⟩ 128 true false halfSlot,
   .boolPublic ⟨n + 3⟩ (bitsOf tag),
   .concat ⟨n + 4⟩ [traffic, ⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩],
   .run ⟨n + 5⟩ checkName 1 ⟨n + 4⟩]

def typedBlock (n : Nat) (parser traffic : BoolH) (recordPadded size : B8) (cap : Nat) : List Instr :=
  [.boolPublic ⟨n + 6⟩ (bitsOf recordPadded ++ bitsOf size),
   .concat ⟨n + 7⟩ [parser, traffic, ⟨n⟩, ⟨n + 6⟩, ⟨n + 5⟩],
   .run ⟨n + 8⟩ (typedName cap) 1 ⟨n + 7⟩,
   .slice ⟨n + 9⟩ ⟨n + 8⟩ 0 8,
   .freeBool ⟨n⟩, .freeBool ⟨n + 3⟩, .freeBool ⟨n + 5⟩, .freeBool ⟨n + 6⟩, .freeBool ⟨n + 7⟩]

/-- Bit 0: the typed kernel's own event and fields (output layout: handshake 1, event 2, parser 11,
length 2, content `cap − 21`, parsed `cap − 17` bytes). -/
def directRest (n cap : Nat) : Script Opened :=
  seqs [.slice ⟨n + 10⟩ ⟨n + 8⟩ 8 24, .slice ⟨n + 11⟩ ⟨n + 8⟩ 24 112, .slice ⟨n + 12⟩ ⟨n + 8⟩ 112 128,
        .slice ⟨n + 13⟩ ⟨n + 8⟩ 128 (128 + 8 * (cap - 21)), .freeBool ⟨n + 8⟩, .freeBool ⟨n + 9⟩]
    (openThen ⟨n + 10⟩ Label.recordEvent fun ev =>
      seqs [.freeBool ⟨n + 10⟩] (.done ⟨bytesOf ev, ⟨n + 11⟩, ⟨n + 12⟩, ⟨n + 13⟩⟩))

/-- Bit 255: `tls-frame CAP` on the old parser and the private parse (output layout: event 2,
parser 11, length 2, content `cap − 21`). -/
def frameRest (n : Nat) (parser : BoolH) (cap : Nat) : Script Opened :=
  seqs [.slice ⟨n + 10⟩ ⟨n + 8⟩ (128 + 8 * (cap - 21)) (128 + 8 * (cap - 21) + 8 * (cap - 17)),
        .concat ⟨n + 11⟩ [parser, ⟨n + 10⟩],
        .run ⟨n + 12⟩ (frameName cap) 1 ⟨n + 11⟩,
        .slice ⟨n + 13⟩ ⟨n + 12⟩ 0 16, .slice ⟨n + 14⟩ ⟨n + 12⟩ 16 104, .slice ⟨n + 15⟩ ⟨n + 12⟩ 104 120,
        .slice ⟨n + 16⟩ ⟨n + 12⟩ 120 (120 + 8 * (cap - 21)),
        .freeBool ⟨n + 8⟩, .freeBool ⟨n + 9⟩, .freeBool ⟨n + 10⟩, .freeBool ⟨n + 11⟩, .freeBool ⟨n + 12⟩]
    (openThen ⟨n + 13⟩ Label.recordEvent fun ev =>
      seqs [.freeBool ⟨n + 13⟩] (.done ⟨bytesOf ev, ⟨n + 14⟩, ⟨n + 15⟩, ⟨n + 16⟩⟩))

/-- After the handshake bit. -/
def afterBit (n : Nat) (parser : BoolH) (cap : Nat) (bit : Bits) : Script Opened :=
  if bit = bitsOf [0] then directRest n cap
  else if bit = bitsOf [255] then frameRest n parser cap
  else .abort "record type bit"

/-- **Open one received application record** (`open_application`, typed). `recordPadded`: the
record followed by zeros to its class capacity `cap`; `size`: its header's length field; `tag`:
its last 16 bytes; `halfSlot`: this party's half over its header and ciphertext. The old parser
handle is not freed here (the backend frees it after). Uses ids `n … n+16`. -/
def openScript (n : Nat) (parser traffic : BoolH) (seq tag recordPadded size : B8) (cap halfSlot : Nat) :
    Script Opened :=
  seqs (checkBlock n traffic seq tag halfSlot ++ typedBlock n parser traffic recordPadded size cap)
    (openThen ⟨n + 9⟩ Label.recordKindBit (afterBit n parser cap))

/-- The initial private parser state (`tls-parser-initial`). Uses ids `n, n+1`. -/
def parserScript (n : Nat) : Script BoolH :=
  seqs [.boolPublic ⟨n⟩ (bitsOf [0]), .run ⟨n + 1⟩ parserName 1 ⟨n⟩, .freeBool ⟨n⟩] (.done ⟨n + 1⟩)

/-! ## The scripts: key update, reveal, public buffers, drop -/

/-- **KeyUpdate of one direction** (`rotate`): the next traffic block; the old one is freed. -/
def updateScript (n : Nat) (traffic : BoolH) : Script BoolH :=
  seqs [.run ⟨n⟩ updateName 1 traffic, .freeBool traffic] (.done ⟨n⟩)

/-- The big-endian length of two opened bytes (`TlsPrivateSeal.lengthValue`). -/
def lengthOf (b : B8) : Nat := 256 * (b.getD 0 0).toNat + (b.getD 1 0).toNat

/-- **The masked content of a received buffer, and its length** (`reveal_range`'s first call):
OPENS the length (serverBytes); keeps the masked bytes `n + 3` (public marks: the bytes below the
length, zeros above). Uses ids `n … n+3`. -/
def revealScript (n : Nat) (length content : BoolH) (cap : Nat) : Script (Nat × BoolH) :=
  seqs [.concat ⟨n⟩ [length, content], .run ⟨n + 1⟩ (revealName cap) 1 ⟨n⟩,
        .slice ⟨n + 2⟩ ⟨n + 1⟩ 0 16, .slice ⟨n + 3⟩ ⟨n + 1⟩ 16 (16 + 8 * cap),
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]
    (openThen ⟨n + 2⟩ Label.serverBytes fun len => seqs [.freeBool ⟨n + 2⟩] (.done (lengthOf (bytesOf len), ⟨n + 3⟩)))

/-- **Bytes `[lo, hi)` of a revealed buffer** (serverBytes). Uses id `n`. -/
def rangeScript (n : Nat) (bytes : BoolH) (lo hi : Nat) : Script B8 :=
  seqs [.slice ⟨n⟩ bytes (8 * lo) (8 * hi)]
    (openThen ⟨n⟩ Label.serverBytes fun b => seqs [.freeBool ⟨n⟩] (.done (bytesOf b)))

/-- **Public bytes as a buffer** (`public_buffer`, op 30). Uses id `n`. -/
def publicScript (n : Nat) (bytes : B8) : Script BoolH :=
  seqs [.boolPublic ⟨n⟩ (bitsOf bytes)] (.done ⟨n⟩)

/-- **Free handles** (retire, abort, the window, drop-after-seal). -/
def dropScript (hs : List BoolH) : Script Unit := seqs (frees hs) (.done ())

/-! ## The scripts: handshake -/

/-- What `tls-derive` leaves: the client and server handshake traffic blocks and the main secret. -/
structure HandshakeHandles where
  client : BoolH
  server : BoolH
  main : BoolH

/-- **Derive the handshake keys** (`derive`, op 2): `agreement` is the X25519 result as a 255-bit
word (S11's `Curve.agree`, all-zero already rejected there); frees it. Uses ids `n … n+5`. -/
def deriveScript (n : Nat) (agreement : BoolH) (helloHash : B8) : Script HandshakeHandles :=
  seqs [.boolPublic ⟨n⟩ (bitsOf helloHash),
        .concat ⟨n + 1⟩ [agreement, ⟨n⟩],
        .run ⟨n + 2⟩ deriveName 1 ⟨n + 1⟩,
        .slice ⟨n + 3⟩ ⟨n + 2⟩ 0 480, .slice ⟨n + 4⟩ ⟨n + 2⟩ 480 960, .slice ⟨n + 5⟩ ⟨n + 2⟩ 960 1216,
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩, .freeBool agreement]
    (.done ⟨⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩⟩)

/-- **Open a protected handshake record** (`open_handshake`, op 3): opens `tls-open-handshake`'s
gated result (handshakeRecord). Uses ids `n … n+2`. -/
def openHandshakeScript (n : Nat) (serverHs : BoolH) (seq record : B8) : Script B8 :=
  seqs [.boolPublic ⟨n⟩ (bitsOf seq ++ bitsOf record),
        .concat ⟨n + 1⟩ [serverHs, ⟨n⟩],
        .run ⟨n + 2⟩ (openHsName record.length) 1 ⟨n + 1⟩,
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]
    (openThen ⟨n + 2⟩ Label.handshakeRecord fun out => seqs [.freeBool ⟨n + 2⟩] (.done (bytesOf out)))

/-- **Verify the server Finished** (`verify_finished`, op 5): opens the acceptance byte
(finishedAccepted); `true` iff it is 255. Uses ids `n … n+2`. -/
def verifyScript (n : Nat) (serverHs : BoolH) (hash message : B8) : Script Bool :=
  seqs [.boolPublic ⟨n⟩ (bitsOf hash ++ bitsOf message),
        .concat ⟨n + 1⟩ [serverHs, ⟨n⟩],
        .run ⟨n + 2⟩ verifyName 1 ⟨n + 1⟩,
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]
    (openThen ⟨n + 2⟩ Label.finishedAccepted fun out =>
      seqs [.freeBool ⟨n + 2⟩] (.done (bytesOf out = [255])))

/-- The client Finished record's length: header 5, certificate, Finished message 36, type 1, tag 16. -/
def finishedLength (cert : Nat) : Nat := cert + 58

/-- **Finish** (`finish`, op 6): the application traffic blocks (kept) and the client Finished
record (opened: clientFinished). Uses ids `n … n+7`. -/
def finishScript (n : Nat) (main clientHs : BoolH) (serverHash clientHash certificate : B8) :
    Script (B8 × BoolH × BoolH) :=
  seqs [.boolPublic ⟨n⟩ (bitsOf serverHash),
        .boolPublic ⟨n + 1⟩ (bitsOf clientHash ++ bitsOf certificate),
        .concat ⟨n + 2⟩ [main, ⟨n⟩, clientHs, ⟨n + 1⟩],
        .run ⟨n + 3⟩ (finishName certificate.length) 1 ⟨n + 2⟩,
        .slice ⟨n + 4⟩ ⟨n + 3⟩ 0 480, .slice ⟨n + 5⟩ ⟨n + 3⟩ 480 960,
        .slice ⟨n + 6⟩ ⟨n + 3⟩ 960 (960 + 8 * finishedLength certificate.length),
        .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩, .freeBool ⟨n + 3⟩]
    (openThen ⟨n + 6⟩ Label.clientFinished fun out =>
      seqs [.freeBool ⟨n + 6⟩] (.done (bytesOf out, ⟨n + 4⟩, ⟨n + 5⟩)))

/-- **Agree a public decision** (op 4's role: the certificate check's request digest and this
party's decision): public bits, in the batch skeleton both parties agree before anything runs;
aborts locally on a negative decision. Nothing released. Uses id `n`. -/
def agreeScript (n : Nat) (digest : B8) (valid : Bool) : Script Unit :=
  seqs [.boolPublic ⟨n⟩ (bitsOf digest ++ [valid]), .freeBool ⟨n⟩]
    (if valid then .done () else .abort "authentication rejected")

/-! ## The per-connection state and the buffers (to live in `Session/Pool`) -/

/-- One direction's record protection: its traffic block's handle and this party's `Secret`
shares of the GHASH key powers H¹ … Hⁿ under it (`gcm_shares.h` `GcmShares::power`). -/
structure Direction where
  traffic : BoolH
  shares : Secret (List W) := Secret.hide []
  /-- How many powers the shares cover (public: a function of the record sizes seen). -/
  powers : Nat := 0

/-- **One TLS connection's secret state** (the C++ `TlsKernels::Parked`: the named TLS secrets,
the key-agreement scalar between begin and derive, the GHASH shares of both directions). Handles
name engine values; the shares are this party's `Secret`s. `Sc` is S11's scalar state. -/
structure Conn (Sc : Type) where
  scalar : Option Sc := none
  handshake : Option HandshakeHandles := none
  send : Option Direction := none
  receive : Option Direction := none
  parser : Option BoolH := none

/-- Every handle a connection holds (what `abort` and `retire` free). -/
def Conn.handles {Sc : Type} (c : Conn Sc) : List BoolH :=
  (c.handshake.map fun h => [h.client, h.server, h.main]).getD [] ++
    (c.send.map (·.traffic)).toList ++ (c.receive.map (·.traffic)).toList ++ c.parser.toList

/-- A private buffer by public id (`TlsKernels::PrivateBuffer`): a received payload (length and
content; after the first reveal, its masked bytes and revealed length) or public bytes. -/
inductive Buffer where
  | received (length content : BoolH) (cap : Nat) (revealed : Option (BoolH × Nat))
  | publicBytes (content : BoolH) (size : Nat)

def Buffer.handles : Buffer → List BoolH
  | .received l c _ none => [l, c]
  | .received l c _ (some (b, _)) => [l, c, b]
  | .publicBytes c _ => [c]

/-- **The received-record window** (`tls_worker_v3.cpp:321-329`): the ids of received buffers
still held, oldest first. -/
abbrev Window := List Nat

/-- How many received records stay held (`kept_records`). -/
def keptRecords : Nat := 64

/-- Push a newly received buffer id: returns the window and the ids to drop (the oldest, beyond
64). -/
def Window.push (w : Window) (id : Nat) : Window × List Nat :=
  let all := w ++ [id]
  (all.drop (all.length - keptRecords), all.take (all.length - keptRecords))

theorem Window.push_bound (w : Window) (id : Nat) : (w.push id).1.length ≤ keptRecords := by
  simp [Window.push]
  omega

theorem Window.push_newest (w : Window) (id : Nat) : (w.push id).1.getLast? = some id := by
  simp only [Window.push, keptRecords]
  rw [List.getLast?_drop]
  simp
  try omega

/-- Kept and dropped are exactly the old window and the new id, in order. -/
theorem Window.push_partition (w : Window) (id : Nat) : (w.push id).2 ++ (w.push id).1 = w ++ [id] := by
  simp [Window.push, List.take_append_drop]

/-- The session's buffers (`TlsKernels::buffers`, `next_buffer`, and the window). -/
structure Buffers where
  table : List (Nat × Buffer) := []
  next : Nat := 1
  window : Window := []

namespace Buffers

def find? (b : Buffers) (id : Nat) : Option Buffer := b.table.lookup id

/-- Add a buffer; its id. -/
def add (b : Buffers) (buf : Buffer) : Nat × Buffers := (b.next, { b with table := (b.next, buf) :: b.table, next := b.next + 1 })

/-- Remove a buffer: its handles (to free) and the table without it. -/
def remove (b : Buffers) (id : Nat) : List BoolH × Buffers :=
  match b.find? id with
  | some buf => (buf.handles, { b with table := b.table.filter (fun e => e.1 != id), window := b.window.filter (· != id) })
  | none => ([], b)

/-- Remove several. -/
def removeAll (b : Buffers) : List Nat → List BoolH × Buffers
  | [] => ([], b)
  | id :: ids =>
    let (h1, b1) := b.remove id
    let (h2, b2) := b1.removeAll ids
    (h1 ++ h2, b2)

/-- **A received application payload joins the window**; the oldest beyond 64 are removed (their
handles to free). -/
def receive (b : Buffers) (buf : Buffer) : Nat × List BoolH × Buffers :=
  let (id, b1) := b.add buf
  let (kept, dropped) := b1.window.push id
  let (hs, b2) := { b1 with window := kept }.removeAll dropped
  (id, hs, b2)

/-- **Drop after seal** (`tls_worker_v3.cpp:336-338`): a buffer is sealed into exactly one record
and never used again. -/
def sealed (b : Buffers) (id : Nat) : List BoolH × Buffers := b.remove id

theorem remove_gone (b : Buffers) (id : Nat) : (b.remove id).2.find? id = none := by
  unfold remove
  cases h : b.find? id with
  | none => exact h
  | some buf =>
    simp only [find?]
    exact (Ctx.lookup_filter_ne b.table id id).trans (by simp)

end Buffers

/-! ## The reveal list -/

/-- The kinds the TLS scripts release under. -/
def sealKinds : List TlsMpc.Node.RevealKind := [.sealedRecord]
def openKinds : List TlsMpc.Node.RevealKind := [.recordKindBit, .recordEvent]
def revealKinds : List TlsMpc.Node.RevealKind := [.serverBytes]
def handshakeKinds : List TlsMpc.Node.RevealKind := [.handshakeRecord, .finishedAccepted, .clientFinished]
def tlsKinds : List TlsMpc.Node.RevealKind :=
  [.sealedRecord, .recordKindBit, .recordEvent, .serverBytes, .handshakeRecord, .finishedAccepted,
   .clientFinished, .ghashMaskedPower]

theorem none_of_frees (hs : List BoolH) : ∀ i ∈ frees hs, i.label? = none := by
  intro i hi
  simp only [frees, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem every_free_done {α : Type} {ks : List TlsMpc.Node.RevealKind} (hs : List BoolH) (a : α) :
    Reveals ks (seqs (frees hs) (.done a)) :=
  every_seqs (Every.done _) _ (labelIn_of_none (none_of_frees hs))

theorem sealCtr_reveals (n : Nat) (traffic content : BoolH) (seq : B8) (kind size padding : Nat) :
    Reveals sealKinds (sealCtrScript n traffic content seq kind size padding) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .sealedRecord) (by simp [sealKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem sealClass_reveals (n : Nat) (traffic content : BoolH) (seq : B8) (size : Nat) :
    Reveals sealKinds (sealClassScript n traffic content seq size) := by
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .sealedRecord) (by simp [sealKinds]) rfl)
    (fun _ => every_seqs ?_ _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))
  split
  · exact Every.done _
  · exact Every.abort _

theorem tag_reveals (n : Nat) (pad : BoolH) (halfSlot : Nat) : Reveals sealKinds (tagScript n pad halfSlot) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .sealedRecord) (by simp [sealKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem open_reveals (n : Nat) (parser traffic : BoolH) (seq tag recordPadded size : B8) (cap halfSlot : Nat) :
    Reveals openKinds (openScript n parser traffic seq tag recordPadded size cap halfSlot) := by
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .recordKindBit) (by simp [openKinds]) rfl)
    (fun bit => ?_)) _ (labelIn_of_none (by simp [checkBlock, typedBlock, InstrP.label?]))
  unfold afterBit
  split
  · exact every_seqs (every_openThen (LabelIn.of_mem (k := .recordEvent) (by simp [openKinds]) rfl)
      (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
      (labelIn_of_none (by simp [InstrP.label?]))
  · split
    · exact every_seqs (every_openThen (LabelIn.of_mem (k := .recordEvent) (by simp [openKinds]) rfl)
        (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
        (labelIn_of_none (by simp [InstrP.label?]))
    · exact Every.abort _

theorem parser_reveals (n : Nat) : Reveals [] (parserScript n) :=
  every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))

theorem update_reveals (n : Nat) (traffic : BoolH) : Reveals [] (updateScript n traffic) :=
  every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))

theorem reveal_reveals (n : Nat) (length content : BoolH) (cap : Nat) :
    Reveals revealKinds (revealScript n length content cap) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .serverBytes) (by simp [revealKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem range_reveals (n : Nat) (bytes : BoolH) (lo hi : Nat) : Reveals revealKinds (rangeScript n bytes lo hi) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .serverBytes) (by simp [revealKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem public_reveals (n : Nat) (bytes : B8) : Reveals [] (publicScript n bytes) :=
  every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))

theorem drop_reveals (hs : List BoolH) : Reveals [] (dropScript hs) := every_free_done hs ()

theorem derive_reveals (n : Nat) (agreement : BoolH) (helloHash : B8) :
    Reveals [] (deriveScript n agreement helloHash) :=
  every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))

theorem openHandshake_reveals (n : Nat) (serverHs : BoolH) (seq record : B8) :
    Reveals handshakeKinds (openHandshakeScript n serverHs seq record) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .handshakeRecord) (by simp [handshakeKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem verify_reveals (n : Nat) (serverHs : BoolH) (hash message : B8) :
    Reveals handshakeKinds (verifyScript n serverHs hash message) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .finishedAccepted) (by simp [handshakeKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem finish_reveals (n : Nat) (main clientHs : BoolH) (serverHash clientHash certificate : B8) :
    Reveals handshakeKinds (finishScript n main clientHs serverHash clientHash certificate) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .clientFinished) (by simp [handshakeKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem agree_reveals (n : Nat) (digest : B8) (valid : Bool) : Reveals [] (agreeScript n digest valid) := by
  refine every_seqs ?_ _ (labelIn_of_none (by simp [InstrP.label?]))
  split
  · exact Every.done _
  · exact Every.abort _

/-! ## T4-TLS, seal: `sealCtr_with_tag_is_seal` with its halves hypothesis discharged -/

theorem header_length (k : Nat) : (TlsRecord.header Gcm.concrete k).length = 5 := by
  simp [TlsRecord.header, Gcm.encodeNat]

theorem inner_length (C : B8) (kind padding : Nat) :
    (TlsRecord.inner Gcm.concrete C kind padding).length = innerLength C.length padding := by
  simp [TlsRecord.inner, Gcm.zeros, innerLength]
  omega

theorem padOf_length (K seqB : B8) (hK : K.length = 60) : (HybridKernel.padOf K seqB).length = 16 :=
  Aes.encryptExpanded_length _ 10 _ _ (HybridKernel.expandedOf_length K hK)

theorem sealCtr_outputs (kind size padding : Nat) :
    ∃ o1 o2 o3, (HybridKernel.tlsSealCtr kind size padding).outputs = [o1, o2, o3] := ⟨_, _, _, rfl⟩

theorem tag_outputs : ∃ o, HybridKernel.gcmTag.outputs = [o] := ⟨_, rfl⟩

theorem blocks_needed (aad ct : B8) : (Local.Ghash.blocks aad ct).length =
    Local.Ghash.needed aad.length ct.length := by
  rw [Local.Ghash.blocks_length]
  simp only [Local.Ghash.needed]
  omega

/-- The sealing kernel's outputs as the script cuts them: header ‖ ciphertext (opened) and pad. -/
theorem sealCtr_kernelOut (kind size padding : Nat) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) :
    kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C)) =
      TlsRecord.header Gcm.concrete (innerLength size padding + 16) ++
        HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding) ++ HybridKernel.padOf K seqB ∧
    (HybridKernel.tlsSealCtr kind size padding).outputs.map
        (fun field => field.value.map (BVExpr.eval (assignOf (K ++ (seqB ++ C))))) =
      [TlsRecord.header Gcm.concrete (innerLength size padding + 16),
        HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding), HybridKernel.padOf K seqB] := by
  have e1 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ C))) 0 60 = K := by
    rw [inputValue_assignOf _ 0 60 (by simp; omega), List.drop_zero, List.take_left' hK]
  have e2 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ C))) 60 8 = seqB := by
    rw [inputValue_assignOf _ 60 8 (by simp; omega), List.drop_left' hK, List.take_left' hs]
  have e3 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ C))) 68 size = C := by
    rw [inputValue_assignOf _ 68 size (by simp; omega), ← List.append_assoc,
      List.drop_left' (by simp; omega), List.take_of_length_le (by omega)]
  have hspec := HybridKernel.tlsSealCtr_spec kind size padding (assignOf (K ++ (seqB ++ C)))
  rw [e1, e2, e3, inner_length, hC] at hspec
  refine ⟨?_, hspec⟩
  simp only [kernelOut, hspec, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- **T4-TLS for the seal** (`sealCtrScript` then `tagScript`, P-GHASH (c)). For a traffic block
`K` (60 bytes), sequence `seqB` (8 bytes) and content `C`: cut the `tls-seal-ctr` output as the
script does (header ‖ ciphertext opened, pad kept), let each party compute its half
(`Local.Ghash.half`) over that header and ciphertext from shares `a` (A) and `b` (B) that share
H¹ … Hⁿ for `H = hashKeyOf K` with `n` covering the record's blocks (what Flows/Ghash builds,
P-GHASH (a)); the `gcm-tag` output on pad ‖ halfA ‖ halfB appended gives EXACTLY
`TlsRecord.sealCore` of the key and IV of `K`, the sequence, content, kind and padding: the
AES-GCM TLS record. This is `sealCtr_with_tag_is_seal` with its `halves` hypothesis discharged
by `Local.Ghash.halves_xor` (closes P-GHASH (c) for the Lean code; plan 7.1). -/
theorem seal_is_record (kind size padding : Nat) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (a b : List W) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (innerLength size padding) ≤ nPow) :
    let out := kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))
    let hc := out.take (5 + innerLength size padding)
    let pad := (out.drop (5 + innerLength size padding)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C kind padding := by
  intro out hc pad hA hB
  obtain ⟨hout, hmap⟩ := sealCtr_kernelOut kind size padding K seqB C hK hs hC
  have hH := header_length (innerLength size padding + 16)
  have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding)).length =
      innerLength size padding := by
    rw [HybridKernel.ctrOf_length _ _ _ hK, inner_length, hC]
  have hP := padOf_length K seqB hK
  have ehc : hc = TlsRecord.header Gcm.concrete (innerLength size padding + 16) ++
      HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding) := by
    show out.take _ = _
    rw [show out = _ from hout, List.take_left' (by simp [hH, hCT])]
  have epad : pad = HybridKernel.padOf K seqB := by
    show (out.drop _).take 16 = _
    rw [show out = _ from hout, List.drop_left' (by simp [hH, hCT]), List.take_of_length_le (by omega)]
  have e5 : hc.take 5 = TlsRecord.header Gcm.concrete (innerLength size padding + 16) := by
    rw [ehc, List.take_left' hH]
  have e5' : hc.drop 5 = HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding) := by
    rw [ehc, List.drop_left' hH]
  have hAl : hA.length = 16 := Local.Ghash.toBytes_length _
  have hBl : hB.length = 16 := Local.Ghash.toBytes_length _
  -- the tagging assignment
  have t1 : HybridKernel.inputValue (assignOf (pad ++ (hA ++ hB))) 0 16 = pad := by
    rw [inputValue_assignOf _ 0 16 (by simp [epad, hP, hAl, hBl]), List.drop_zero,
      List.take_left' (by rw [epad, hP])]
  have t2 : HybridKernel.inputValue (assignOf (pad ++ (hA ++ hB))) 16 16 = hA := by
    rw [inputValue_assignOf _ 16 16 (by simp [epad, hP, hAl, hBl]), List.drop_left' (by rw [epad, hP]),
      List.take_left' hAl]
  have t3 : HybridKernel.inputValue (assignOf (pad ++ (hA ++ hB))) 32 16 = hB := by
    rw [inputValue_assignOf _ 32 16 (by simp [epad, hP, hAl, hBl]), ← List.append_assoc,
      List.drop_left' (by simp [epad, hP, hAl]), List.take_of_length_le (by omega)]
  obtain ⟨o, ho⟩ := tag_outputs
  have htag := TlsMpc.Node.Flows.Ghash.outputs_one _ o ho (pad ++ (hA ++ hB))
  have hhalves : Aes.addRoundKey Gcm.concrete.aes hA hB =
      HybridKernel.ghashOf K (hc.take 5) (hc.drop 5) := by
    refine Local.Ghash.halves_xor K _ _ a b nPow hsh ?_
    rw [blocks_needed, e5, e5', hH, hCT]
    exact hn
  have s1 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ C))) 0 60 = K := by
    rw [inputValue_assignOf _ 0 60 (by simp; omega), List.drop_zero, List.take_left' hK]
  have s2 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ C))) 60 8 = seqB := by
    rw [inputValue_assignOf _ 60 8 (by simp; omega), List.drop_left' hK, List.take_left' hs]
  have s3 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ C))) 68 size = C := by
    rw [inputValue_assignOf _ 68 size (by simp; omega), ← List.append_assoc,
      List.drop_left' (by simp; omega), List.take_of_length_le (by omega)]
  have hrec := HybridKernel.sealCtr_with_tag_is_seal kind size padding (assignOf (K ++ (seqB ++ C)))
    (assignOf (pad ++ (hA ++ hB))) (hc.take 5) (hc.drop 5) pad (kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)))
    (by rw [hmap, e5, e5', epad]) t1 htag (by rw [t2, t3, hhalves, s1])
  rw [s1, s2, s3, List.take_append_drop] at hrec
  exact hrec

end TlsMpc.Node.Flows.Tls
