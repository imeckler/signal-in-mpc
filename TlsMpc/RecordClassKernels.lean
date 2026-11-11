import TlsMpc.HybridKernels

/-!
TLS application records in SIZE CLASSES, so that the set of record circuits a
deployment needs is fixed before it starts (`handshake_backend/EmpHybridWork/CIRCUIT_SHAPES.md`).

A record's size is public (it is on the wire), but it is only known when the
record arrives or is built, and `tls-open-application-ctr N` / `tls-seal-ctr 23 N 0`
are a different circuit for every `N`. The kernels here take a public CAPACITY
from a small ladder (`capacity`) as their only shape parameter and the record's
true length as a public VALUE (`size`, the two bytes of the record header's
length field):

* `tls-open-application-class CAP`: the record followed by zero bytes up to
  `CAP`. Computes what `tls-open-application-ctr N` computes for the record
  itself, with `CAP - N` more zero bytes at the end of the content buffer
  (`TlsMpc/RecordClassProofs.lean`). The private content is `CAP - 21` bytes,
  so the buffer's later kernels (`tls-reveal-masked`) come in the same classes.
* `tls-seal-class CAP`: the content followed by anything up to `CAP` bytes.
  Opens the header and the ciphertext of exactly the content and its type byte,
  as `tls-seal-ctr 23 N 0` does, followed by zero bytes; no TLS padding is added,
  so the record on the wire is byte for byte the exact-size one.

The length is enforced inside the circuits: bytes at or beyond it are masked
before they are parsed (open) or encrypted and released (seal), and a length
that does not fit the capacity rejects. Nothing new is revealed: the class is a
function of the record size, which both parties already see.
-/
namespace TlsMpc.RecordClass
open Std.Tactic.BVDecide

/-- The capacity ladder: sizes up to 32 share one class; above that a size is
rounded up to a multiple of a quarter of the power of two below it (four
classes per doubling: 40, 48, 56, 64, 80, 96, 112, 128, 160, …). The padding is
under a quarter of the size, an eighth on average. -/
def capacity (n : Nat) : Nat :=
  if n ≤ 32 then 32 else
    let step := 2 ^ (Nat.log2 (n - 1) - 2)
    (n + step - 1) / step * step

/-- Bytewise AND with a mask per byte. -/
def maskBytes (a : ByteAuth.Ops B) : List B → List B → List B
  | mask :: masks, byte :: bytes => a.and mask byte :: maskBytes a masks bytes
  | _, _ => []

/-- The length masks for a field that starts `offset` bytes into what `high`,
`low` count: whether the length fits (`offset ≤ length ≤ offset + count`), and
for each `j < count` whether `offset + j < length`. -/
def within (a : ByteAuth.Ops B) (high low : B) (offset count : Nat) : B × List B :=
  TlsWebSocketUpgrade.activity a high low offset count

/-- CTR decryption of a record that is followed by padding up to a capacity.
`high`, `low` are the record header's length field (ciphertext and tag). The
result is whether the length fits, and the plaintext with every byte at or
beyond the true ciphertext length zero. -/
def openPlaintext (g : Gcm.Ops B W) (a : ByteAuth.Ops B) (expanded nonce wire : List B) (high low : B) :
    B × List B :=
  let ciphertext := TlsReceive.ciphertext wire
  let masks := within a high low 16 ciphertext.length
  (masks.1, maskBytes a masks.2 (Gcm.ctr g expanded nonce ciphertext))

/-- The inner parse of that record (`TlsReceive.releaseOpened`: acceptance,
type, length, content), with the header required to be the TLS 1.3 encoding of
the stated length. `accepted` is the tag check's private mask. -/
def openParsed (g : Gcm.Ops B W) (a : ByteAuth.Ops B) (expanded nonce wire : List B) (high low accepted : B) :
    List B :=
  let opened := openPlaintext g a expanded nonce wire high low
  let headerValid := a.and opened.1
    (ByteAuth.equalMask a (wire.take 5) [g.aes.const 23, g.aes.const 3, g.aes.const 3, high, low])
  TlsReceive.releaseOpened a headerValid ⟨accepted, opened.2⟩

/-- The TLSInnerPlaintext of a content held in a capacity: content bytes below
the length, the type byte 23 at the length, zero after it. `below` are the
masks `j < length`, `upTo` the masks `j ≤ length` (one more of them). -/
def place (a : ByteAuth.Ops B) : List B → List B → List B → List B
  | byte :: bytes, low :: below, high :: upTo =>
      a.xor (a.and low byte) (a.and (a.xor high low) (a.const 23)) :: place a bytes below upTo
  | [], _, high :: _ => [a.and high (a.const 23)]
  | _, _, _ => []

/-- CTR encryption of a content held in a capacity. `high`, `low` are the
record header's length field (content, type byte and tag: length + 17). The
result is whether the length fits, and the ciphertext of the content and its
type byte followed by zero bytes. -/
def sealCiphertext (g : Gcm.Ops B W) (a : ByteAuth.Ops B) (expanded nonce content : List B) (high low : B) :
    B × List B :=
  let below := within a high low 17 content.length
  let upTo := (within a high low 16 (content.length + 1)).2
  (below.1, maskBytes a upTo (Gcm.ctr g expanded nonce (place a content below.2 upTo)))

end TlsMpc.RecordClass

namespace TlsMpc.RecordClassKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup pub priv sl blockKey blockIv gcmExpanded gcmPad)

/-- `tlsOpenApplicationCtr` for a record of any size up to `capacity`: `record`
is the wire record followed by zero bytes, `size` its header's length field. -/
def tlsOpenApplicationClass (capacity : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := [("parser", Shape.bytes 11), ("serverApplication", .bytes 60), ("sequence", .bytes 8),
    ("record", .bytes capacity), ("size", .bytes 2), ("accepted", .bytes 1)]
  let get := lookup inputs
  let block := get "serverApplication"
  let parsed := RecordClass.openParsed g a (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "sequence"))
    (get "record") (HybridService.at' (get "size") 0) (HybridService.at' (get "size") 1)
    (HybridService.at' (get "accepted") 0)
  let out := TlsPostHandshake.Fast.core Word64.symbolicMux a (get "parser") parsed
  { name := "tls-open-application-class", inputs, outputs := [
      pub "event" (sl out 0 2), priv "parser" (sl out 2 11), priv "length" (sl out 13 2), priv "content" (out.drop 15)] }

/-- `tlsSealCtr 23 _ 0` for a content of any size up to `capacity`: `content`
is the content followed by anything, `size` the record header's length field
(content length + 17). `accepted` is 255 exactly when that length fits; the
ciphertext is zero otherwise, and zero beyond the content and its type byte. -/
def tlsSealClass (capacity : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes capacity),
    ("size", .bytes 2)]
  let get := lookup inputs
  let block := get "clientApplication"
  let sealed := RecordClass.sealCiphertext g a (gcmExpanded block) (TlsRecord.nonce g (blockIv block) (get "sequence"))
    (get "content") (HybridService.at' (get "size") 0) (HybridService.at' (get "size") 1)
  { name := "tls-seal-class", inputs, outputs := [
      pub "accepted" [sealed.1], pub "header" ([23, 3, 3].map HybridKernel.const ++ get "size"),
      pub "ciphertext" (ByteAuth.release a sealed.1 sealed.2), priv "pad" (gcmPad block (get "sequence"))] }

/-- Kernel named on the command line: `tls-open-application-class CAP` (a
capacity of the ladder, at most that of the largest TLS record) and
`tls-seal-class CAP` (likewise, for the content). -/
def find : List String → Option Kernel
  | [name, a] =>
      match name, a.toNat? with
      | "tls-open-application-class", some n =>
          if RecordClass.capacity n == n && n ≤ RecordClass.capacity 16406 then some (tlsOpenApplicationClass n) else none
      | "tls-seal-class", some n =>
          if RecordClass.capacity n == n && n ≤ 16384 then some (tlsSealClass n) else none
      | _, _ => none
  | _ => none

end TlsMpc.RecordClassKernel
