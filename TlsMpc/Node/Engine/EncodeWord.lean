import TlsMpc.Node.Engine

/-!
# `encodeBatch` into a byte array, eight-byte numbers from a machine word

`EncA` (Engine.lean) writes `encodeBatch` into a `ByteArray`; its `u64` cuts each number into eight
bytes with eight divisions by 256 on `Nat`. The mask pool's batches carry about 520,000 `pick`
positions (4 MB) per generation and every instruction its handle ids, so that was a third of the
pool's controller time (PERFORMANCE.md, "third round"). `EncW` is `EncA` with `u64W`: for a number
below 2^64 (every handle, position, length and label in practice) the bytes are shifts of one
`UInt64`; any other number takes `EncA.u64`. **`encodeBatchWord_eq`: the array holds exactly
`encodeBatch`** (each `EncW.*` appends what the `Enc.*` of the same name returns: `EncW.*_spec`), so
the runner sends the same bytes as before. IO glue only: no script and no instruction changes.
-/

namespace TlsMpc.Node.Engine.EncW

open TlsMpc.Node.Engine
open TlsMpc.Node.Engine.EncA (bl bl_push)
open TlsMpc.FieldDag (F)

/-- `Enc.u64 n` (eight little-endian bytes), from a machine word when `n < 2^64` (`u64W_spec`). -/
def u64W (n : Nat) (acc : ByteArray) : ByteArray :=
  if n < 18446744073709551616 then
    let v := n.toUInt64
    (((((((acc.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8).push
      (v >>> 32).toUInt8).push (v >>> 40).toUInt8).push (v >>> 48).toUInt8).push (v >>> 56).toUInt8
  else EncA.u64 n acc

theorem byte_eq (n k : Nat) (hn : n < 18446744073709551616) (hk : k < 64) :
    (n.toUInt64 >>> k.toUInt64).toUInt8 = UInt8.ofNat (n / 2 ^ k) := by
  apply UInt8.toNat_inj.mp
  have h1 : (UInt64.ofNat n).toNat = n := by simp; omega
  have h2 : (UInt64.ofNat k).toNat = k := by simp; omega
  have h3 : (UInt8.ofNat (n / 2 ^ k)).toNat = n / 2 ^ k % 256 := by simp
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.toUInt64, Nat.shiftRight_eq_div_pow, h1, h2, h3]
  rw [Nat.mod_eq_of_lt hk]

theorem ofNat_mod256 (m : Nat) : UInt8.ofNat (m % 256) = UInt8.ofNat m := by
  apply UInt8.toNat_inj.mp
  simp

theorem u64W_spec (n : Nat) (acc : ByteArray) : bl (u64W n acc) = bl acc ++ Enc.u64 n := by
  unfold u64W
  split
  · next hn =>
    simp only [bl_push, Enc.u64, Engine.le, List.append_assoc, List.cons_append, List.nil_append]
    have e : ∀ k, k < 64 → (n.toUInt64 >>> k.toUInt64).toUInt8 = UInt8.ofNat (n / 2 ^ k) :=
      fun k hk => byte_eq n k hn hk
    have e0 : n.toUInt64.toUInt8 = UInt8.ofNat n := by
      have := e 0 (by decide); simpa using this
    rw [e0, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, e 8 (by decide),
      show (16 : UInt64) = (16 : Nat).toUInt64 from rfl, e 16 (by decide),
      show (24 : UInt64) = (24 : Nat).toUInt64 from rfl, e 24 (by decide),
      show (32 : UInt64) = (32 : Nat).toUInt64 from rfl, e 32 (by decide),
      show (40 : UInt64) = (40 : Nat).toUInt64 from rfl, e 40 (by decide),
      show (48 : UInt64) = (48 : Nat).toUInt64 from rfl, e 48 (by decide),
      show (56 : UInt64) = (56 : Nat).toUInt64 from rfl, e 56 (by decide)]
    simp only [ofNat_mod256, Nat.div_div_eq_div_mul, Nat.reduceMul, Nat.reducePow]
  · exact EncA.u64_spec n acc

/-- A list: its length, then each element (as `EncA.list`, the length by `u64W`). -/
def list {α : Type} (e : α → ByteArray → ByteArray) (l : List α) (acc : ByteArray) : ByteArray :=
  l.foldl (fun a x => e x a) (u64W l.length acc)
def bytes (b : Bytes) (acc : ByteArray) : ByteArray := list (fun x a => a.push x) b acc
def bits (b : Bits) (acc : ByteArray) : ByteArray := list EncA.flag b acc
def felts (v : List F) (acc : ByteArray) : ByteArray := list EncA.felt v acc
def boolH (h : BoolH) (acc : ByteArray) : ByteArray := u64W h.id acc
def fieldH (h : FieldH) (acc : ByteArray) : ByteArray := u64W h.id acc
def label (l : Label) (acc : ByteArray) : ByteArray := u64W l.code acc
def pair (p : FieldH × FieldH) (acc : ByteArray) : ByteArray := fieldH p.2 (fieldH p.1 acc)

theorem list_spec {α : Type} (e : α → ByteArray → ByteArray) (f : α → Bytes)
    (he : ∀ x a, bl (e x a) = bl a ++ f x) (l : List α) (acc : ByteArray) :
    bl (list e l acc) = bl acc ++ Enc.list f l := by
  simp only [list, Enc.list, EncA.foldl_spec e f he, u64W_spec, List.append_assoc]

theorem bytes_spec (b : Bytes) (acc : ByteArray) : bl (bytes b acc) = bl acc ++ Enc.bytes b :=
  list_spec _ (fun x => [x]) (fun x a => bl_push a x) b acc
theorem bits_spec (b : Bits) (acc : ByteArray) : bl (bits b acc) = bl acc ++ Enc.bits b :=
  list_spec _ _ EncA.flag_spec b acc
theorem felts_spec (v : List F) (acc : ByteArray) : bl (felts v acc) = bl acc ++ Enc.felts v :=
  list_spec _ _ EncA.felt_spec v acc
theorem boolH_spec (h : BoolH) (acc : ByteArray) : bl (boolH h acc) = bl acc ++ Enc.boolH h := u64W_spec _ _
theorem fieldH_spec (h : FieldH) (acc : ByteArray) : bl (fieldH h acc) = bl acc ++ Enc.fieldH h := u64W_spec _ _
theorem label_spec (l : Label) (acc : ByteArray) : bl (label l acc) = bl acc ++ Enc.label l := u64W_spec _ _
theorem pair_spec (p : FieldH × FieldH) (acc : ByteArray) : bl (pair p acc) = bl acc ++ Enc.pair p := by
  simp only [pair, Enc.pair, fieldH_spec, List.append_assoc]

/-- `encWire`, appended (`EncA.wire` with `u64W`). -/
def wire (w : Wire) (acc : ByteArray) : ByteArray :=
  match w with
  | .boolInput out owner w once rev v =>
    bits v (EncA.flag rev (EncA.flag once (u64W w (EncA.party owner (boolH out (acc.push 1))))))
  | .boolInputBoth oa ob w once rev v =>
    bits v (EncA.flag rev (EncA.flag once (u64W w (boolH ob (boolH oa (acc.push 2))))))
  | .boolPublic out v => bits v (boolH out (acc.push 3))
  | .run out name n input => boolH input (u64W n (bytes name (boolH out (acc.push 4))))
  | .concat out ps => list boolH ps (boolH out (acc.push 5))
  | .slice out h lo hi => u64W hi (u64W lo (boolH h (boolH out (acc.push 6))))
  | .pick out h is => list u64W is (boolH h (boolH out (acc.push 7)))
  | .openBool h l => label l (boolH h (acc.push 8))
  | .openBoolTo h r l _ => label l (EncA.party r (boolH h (acc.push 9)))
  | .freeBool h => boolH h (acc.push 10)
  | .fieldInput oa ob k rev v =>
    felts v (EncA.flag rev (EncA.kind k (list fieldH ob (list fieldH oa (acc.push 11)))))
  | .fieldPublic out v => EncA.felt v (fieldH out (acc.push 12))
  | .fieldAdd out a b => fieldH b (fieldH a (fieldH out (acc.push 13)))
  | .fieldSub out a b => fieldH b (fieldH a (fieldH out (acc.push 14)))
  | .fieldScale out a k => u64W k (fieldH a (fieldH out (acc.push 15)))
  | .fieldDivide out a k => EncA.felt k (fieldH a (fieldH out (acc.push 16)))
  | .fieldMul outs ps => list pair ps (list fieldH outs (acc.push 17))
  | .fieldCheck => acc.push 18
  | .openField hs l => label l (list fieldH hs (acc.push 19))
  | .freeField h => fieldH h (acc.push 20)
  | .exchange len l p => bytes p (label l (u64W len (acc.push 21)))
  | .program name k ins ms outs l =>
    label l (list fieldH outs (list fieldH ms (list fieldH ins (u64W k (bytes name (acc.push 22))))))

theorem wire_spec (w : Wire) (acc : ByteArray) : bl (wire w acc) = bl acc ++ encWire w := by
  cases w <;> simp only [wire, encWire, bl_push, u64W_spec, EncA.flag_spec, EncA.party_spec, EncA.kind_spec,
    EncA.felt_spec, bytes_spec, bits_spec, felts_spec, boolH_spec, fieldH_spec, label_spec,
    list_spec _ _ boolH_spec, list_spec _ _ u64W_spec, list_spec _ _ fieldH_spec, list_spec _ _ pair_spec,
    List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

end TlsMpc.Node.Engine.EncW

namespace TlsMpc.Node.Engine

/-- `encodeBatch` written into a byte array with `EncW` (`encodeBatchWord_eq`): what the runner sends. -/
def encodeBatchWord (b : List Wire) : ByteArray := EncW.list EncW.wire b ByteArray.empty

/-- **The array holds exactly `encodeBatch b`.** -/
theorem encodeBatchWord_eq (b : List Wire) : (encodeBatchWord b).data.toList = encodeBatch b := by
  have h := EncW.list_spec EncW.wire encWire EncW.wire_spec b ByteArray.empty
  simpa [encodeBatchWord, encodeBatch, EncA.bl] using h

end TlsMpc.Node.Engine
