import TlsMpc.BundleItemKernels
import TlsMpc.Signal.BundleSlots

/-!
`bundle-slot FIRST LAST ONETIME`: one device of a prekey response, whatever the digit counts of
its numbers (`TlsMpc/Signal/BundleSlots.lean`). It replaces `bundle-item FIRST LAST D R S P K`,
one circuit per digit-count combination, by eight circuits.

Inputs, as for `bundle-item`: `head` (the body's first `firstItem` bytes), `before` (unless
first: the byte before the item), `item`, `after` (unless last: the byte after it), `end` (the
body's last two bytes); but `item` is the item SPLICED into the slot layout (`BundleSlots.splice`:
public `0` characters inserted before each number by the runtime), `size (item (slots ONETIME))`
bytes; and `widths`: the five digit counts, one byte each (public; the runtime passes the values
`layout?` read off the opened flags). The outputs are those of `bundle-item`, under the same names.

It is `BundleSlots.deviceSlots` applied to the response made of those inputs, as `bundle-item` is
`BundleResponse.device` (`TlsMpc/BundleSlotProofs.lean`). Produced by its own executable,
`bundle_slot_emitter` (`circuit_cache.py` sends names starting with `bundle-slot` there), so that
`flat_kernel_emitter` and the cache of every other circuit are unchanged.
-/
namespace TlsMpc.BundleSlotKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup pub priv)
open BundleResponse (Widths)

def slotInputs (first last oneTime : Bool) : List (String × Shape) :=
  [("head", Shape.bytes BundleResponse.firstItem)] ++ (if first then [] else [("before", Shape.bytes 1)]) ++
    [("item", Shape.bytes (BundleResponse.size (BundleResponse.item (BundleSlots.slots oneTime))))] ++
    (if last then [] else [("after", Shape.bytes 1)]) ++ [("end", Shape.bytes 2), ("widths", Shape.bytes 5)]

def bundleSlot (first last oneTime : Bool) : Kernel :=
  let inputs := slotInputs first last oneTime
  let get := lookup inputs
  let body := get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end"
  let start := BundleResponse.firstItem + (if first then 0 else 1)
  let out := BundleSlots.deviceSlots ByteAuth.symbolic body.length start oneTime (get "widths") body
  { name := "bundle-slot", inputs, outputs := [
      priv "valid" (out.getD 0 []), priv "identityKey" (out.getD 1 []), priv "deviceId" (out.getD 2 []),
      priv "registrationId" (out.getD 3 []), priv "signedPrekeyId" (out.getD 4 []), priv "signedPrekey" (out.getD 5 []),
      priv "signedPrekeySignature" (out.getD 6 []), priv "kyberPrekeyId" (out.getD 7 []),
      priv "kyberPrekey" (out.getD 8 []), priv "kyberPrekeySignature" (out.getD 9 [])] ++
      (if oneTime then [priv "oneTimePrekeyId" (out.getD 10 []), priv "oneTimePrekey" (out.getD 11 [])] else []) }

/-- The parameter list of `bundle-slot` for the item at `index` of `count`. -/
def arguments (index count : Nat) (w : Widths) : List String :=
  ["bundle-slot", if index == 0 then "1" else "0", if index + 1 == count then "1" else "0",
    if w.oneTime == 0 then "0" else "1"]

/-- Kernel named on the command line: `bundle-slot FIRST LAST ONETIME` (each 0 or 1: whether the
item is the first and the last of the response, and whether it has a one-time prekey). -/
def find (arguments : List String) : Option Kernel :=
  match arguments with
  | "bundle-slot" :: rest =>
      match rest.mapM (·.toNat?) with
      | some [first, last, oneTime] =>
          if first ≤ 1 && last ≤ 1 && oneTime ≤ 1 then some (bundleSlot (first == 1) (last == 1) (oneTime == 1)) else none
      | _ => none
  | _ => none

end TlsMpc.BundleSlotKernel
