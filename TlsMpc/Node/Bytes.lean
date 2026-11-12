import TlsMpc.ByteAuth
import TlsMpc.TlsWire

/-!
# The controller's byte operations (pure)

`PublicReceive.fast`: the byte operations the controller's parsers and request builders run on, for
values in the clear. Equal to `ByteAuth.concrete` (`fast_eq`); the differences are in how three
operations are computed at run time. `ByteAuth.concrete` builds the mask of one bit with
`BitVec.replicate`, and its constants and complements go through `2 ^ 8` as an arbitrary-precision
power each time; together that made every parsed byte cost milliseconds.

Moved here unchanged (names kept) from the controller
(`handshake_backend/EmpHybridWork/PublicServiceController.lean`), by way of
`TlsMpc/Node/PassOver.lean`, so that both the receive policy (`Policy/Receive.lean`, with the
pass-over theorems) and the request builders (`Policy/Request.lean`) can use it without importing
each other (REORGANIZATION_PLAN.md stage S2). No emitter imports this module.
-/

open TlsMpc

namespace PublicReceive

def fastConst (n : Nat) : BitVec 8 := BitVec.ofFin ⟨n % 256, Nat.mod_lt n (by decide)⟩
theorem fastConst_eq (n : Nat) : fastConst n = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp [fastConst]

def fastNot (x : BitVec 8) : BitVec 8 := x ^^^ 255#8
theorem fastNot_eq : ∀ x : BitVec 8, fastNot x = ~~~x := by decide

def fastMask (x : BitVec 8) (i : Nat) : BitVec 8 := if x.getLsbD i then 255#8 else 0#8

theorem fastMask_eq (x : BitVec 8) (i : Nat) : fastMask x i = BitVec.replicate 8 (x.extractLsb' i 1) := by
  have h : x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hz : j = 0 := by omega
    subst hz
    simp
  rw [h]
  unfold fastMask
  cases x.getLsbD i <;> decide

def fast : ByteAuth.Ops (BitVec 8) where
  const := fastConst
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := fastNot
  maskBit := fastMask

theorem fast_eq : fast = ByteAuth.concrete := by
  have hc : fastConst = BitVec.ofNat 8 := funext fastConst_eq
  have hn : fastNot = (fun x : BitVec 8 => ~~~x) := funext fastNot_eq
  have hm : fastMask = (fun (x : BitVec 8) (i : Nat) => BitVec.replicate 8 (x.extractLsb' i 1)) :=
    funext fun x => funext fun i => fastMask_eq x i
  unfold fast ByteAuth.concrete
  rw [hc, hn, hm]

end PublicReceive

/-! ### Conversions between the controller's byte representations

Moved unchanged from the controller in stage S2 (they were `private` there; the controller opens
this namespace and uses the same names). `natural` and `sessionBytes` parse command-line fixture
arguments (they only throw; no I/O). -/

namespace TlsMpc.Node.Bytes
open TlsMpc.TlsWire

def natural (s : String) : IO Nat :=
  match s.toNat? with | some n => pure n | none => throw (IO.userError "invalid fixture integer")
def sessionBytes (text : String) : IO Bytes := do
  unless text.length == 64 do throw (IO.userError "invalid fixture session ID")
  let chars := text.toList.toArray
  (List.range 32).mapM fun i => do
    let digit (c : Char) : IO Nat :=
      if '0' ≤ c && c ≤ '9' then pure (c.toNat-'0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat-'a'.toNat+10)
      else throw (IO.userError "invalid fixture hex")
    return UInt8.ofNat (16*(← digit chars[2*i]!) + (← digit chars[2*i+1]!))

def toBits (bytes : Bytes) : List (BitVec 8) := bytes.map (fun b => BitVec.ofNat 8 b.toNat)
def toBytes (bits : List (BitVec 8)) : Bytes := bits.map (fun b => UInt8.ofNat b.toNat)

def fromHex (text : String) : Except String Bytes := do
  let chars := text.toList
  unless chars.length % 2 == 0 do throw "odd-length hex string"
  let digit (c : Char) : Except String Nat :=
    if c.isDigit then pure (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
    else throw "invalid hex digit"
  (List.range (chars.length / 2)).mapM (fun i => do
    pure (UInt8.ofNat (16 * (← digit (chars.getD (2 * i) '0')) + (← digit (chars.getD (2 * i + 1) '0')))))

end TlsMpc.Node.Bytes
