import TlsMpc.BundleKernels

/-!
`bundle-device SIZE START D R S P K` (`TlsMpc/BundleKernels.lean`) is a
different circuit for every size of the response body and every offset of the
item in it, although it reads only the header, the item, the bytes on either
side of it and the body's last two bytes. `bundle-item` takes exactly those
bytes as separate inputs, so its shape depends on the item alone: whether it is
the first and the last item of the response, and the digit counts of its five
numbers (`handshake_backend/EmpHybridWork/CIRCUIT_SHAPES.md`).

It is `BundleResponse.device` itself, applied to the response made of the
header, this item with its neighbouring bytes, and the closing `]}` — the same
bytes at the positions `device` reads in the whole body:

* `head`: the body's first `BundleResponse.firstItem` bytes (the identity key
  and the opening of the device list);
* `before` (unless first): the byte before the item, which must be `,`;
* `item`: the item, `BundleResponse.size (BundleResponse.item w)` bytes;
* `after` (unless last): the byte after the item, which must be `,`;
* `end`: the body's last two bytes, which must be `]}`.

The runtime binds those ranges of the private body using the item's offset
from `BundleResponse.layout?` and the widths this kernel declares for its
inputs; it has no other knowledge of the layout. The outputs are those of
`bundle-device`, under the same names.

The response body is opened in classes as well, with no new kernel:
`bundle-shape CAP` is run on the body followed by zero bytes up to a capacity
of `RecordClass.capacity`; a zero byte is not punctuation, so the flags are the
body's flags followed by zeros (`BundleItemKernel.shape_padded`).
-/
namespace TlsMpc.BundleItemKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup pub priv)
open BundleResponse (Widths)

def itemInputs (first last : Bool) (w : Widths) : List (String × Shape) :=
  [("head", Shape.bytes BundleResponse.firstItem)] ++ (if first then [] else [("before", Shape.bytes 1)]) ++
    [("item", Shape.bytes (BundleResponse.size (BundleResponse.item w)))] ++
    (if last then [] else [("after", Shape.bytes 1)]) ++ [("end", Shape.bytes 2)]

/-- One device's bundle fields from the item and the bytes around it. An input
that is absent (`before` of the first item, `after` of the last) is empty. -/
def bundleItem (first last : Bool) (w : Widths) : Kernel :=
  let inputs := itemInputs first last w
  let get := lookup inputs
  let body := get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end"
  let start := BundleResponse.firstItem + (if first then 0 else 1)
  let out := BundleResponse.device ByteAuth.symbolic body.length start w body
  { name := "bundle-item", inputs, outputs := [
      priv "valid" (out.getD 0 []), priv "identityKey" (out.getD 1 []), priv "deviceId" (out.getD 2 []),
      priv "registrationId" (out.getD 3 []), priv "signedPrekeyId" (out.getD 4 []), priv "signedPrekey" (out.getD 5 []),
      priv "signedPrekeySignature" (out.getD 6 []), priv "kyberPrekeyId" (out.getD 7 []),
      priv "kyberPrekey" (out.getD 8 []), priv "kyberPrekeySignature" (out.getD 9 [])] ++
      (if w.oneTime = 0 then [] else [priv "oneTimePrekeyId" (out.getD 10 []), priv "oneTimePrekey" (out.getD 11 [])]) }

/-- The parameter list of `bundle-item` for the item at `index` of `count`. -/
def arguments (index count : Nat) (w : Widths) : List String :=
  ["bundle-item", if index == 0 then "1" else "0", if index + 1 == count then "1" else "0", toString w.device,
    toString w.registration, toString w.signed, toString w.oneTime, toString w.kyber]

/-- Kernel named on the command line: `bundle-item FIRST LAST D R S P K` (0 or
1 for whether the item is the first and the last of the response, then the
digit counts of its device id, registration id, signed prekey id, one-time
prekey id — 0 when it has none — and Kyber prekey id). -/
def find (arguments : List String) : Option Kernel :=
  match arguments with
  | "bundle-item" :: rest =>
      match rest.mapM (·.toNat?) with
      | some [first, last, d, r, s, p, k] =>
          let w : Widths := ⟨d, r, s, p, k⟩
          if first ≤ 1 && last ≤ 1 && w.ok then some (bundleItem (first == 1) (last == 1) w) else none
      | _ => none
  | _ => none

/-- Zero bytes after a body add only zero flags to its shape. -/
theorem shape_padded (body : List (BitVec 8)) (k : Nat) :
    BundleResponse.shape ByteAuth.concrete (body ++ List.replicate k 0) =
      [(BundleResponse.shape ByteAuth.concrete body).getD 0 [] ++ List.replicate k 0] := by
  have h : BundleResponse.structural ByteAuth.concrete (0 : BitVec 8) = 0 := by decide
  simp only [BundleResponse.shape, List.map_append, List.map_replicate, List.getD_cons_zero]
  rw [h]

#print axioms shape_padded

end TlsMpc.BundleItemKernel
