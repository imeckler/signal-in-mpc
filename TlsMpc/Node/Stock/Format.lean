import TlsMpc.Node.Engine

/-!
THE STOCK'S ON-DISK FORMAT: SHAPE ID, HEADER, ITEM RECORDS, THE ITEM'S ASSOCIATED DATA, THE
JOURNAL CHECK, THE KEY CHAIN, AND THE AGREEMENT CLAIM.

X1 (PRODUCT_TODO.md 11a "Stock format"). Pure; no I/O; no emitter imports this module. The Rust
store (`node_stock/src/format.rs`) implements these encodings byte for byte; the vectors
`node_stock/tests/stock_vectors.txt` are printed from these definitions
(`node_stock/tests/lean/StockVectors.lean`).

Numbers are u64 little-endian and byte strings are a u64 length then the bytes (the engine
batch's conventions, Engine.lean design note item 2). Fixed 32-byte fields (hashes, ids) are
written raw.

  shape id   = bytes circuit-name, u64 size-class, bytes client-profile
               (the circuit name as the manifest loads it; a size class such as a message-length
               bucket; the client profile, e.g. official or built)
  header     = "x1-stock" (8 bytes), u64 version (1), shape id, manifest hash (32),
               boot id (32), stock id (32), u64 item length
  item       = u64 index, u64 length, agreed hash (32), sealed bytes (length + 16: the AEAD
               ciphertext and its tag); records are fixed-size (`recordLen`), item i at offset
               i * recordLen of the items file
  item AAD   = "x1-item-v1", boot id, stock id, manifest hash, shape id, u64 index, u64 length,
               agreed hash: the item's encryption is bound to the boot, the stock, the circuits,
               the shape and the index
  journal    = records of 16 bytes: u64 watermark, then the first 8 bytes of
               H("x1-journal-v1" || stock id || u64 watermark) (Journal.lean)
  key chain  = c_0 random (boot memory only); c_{i+1} = H("x1-chain-v1" || c_i);
               the key of item i is H("x1-item-key-v1" || c_i). Taking item i keeps only
               c_{i+1}, so the keys of used items cannot be computed from what is left.
  claim      = 1 byte (0: no usable stock, 1: a usable stock), then u64 next index if 1: what each
               node sends in the per-message agreement before the `stockUse` instruction
               (Use.lean, SPECIFICATION).

The agreed hash is computed by both nodes when the item is made (for a garbled circuit, a hash
of the garbled tables both hold) and is part of the `stockUse` skeleton, so the two nodes confirm
before any engine call that they hold the two halves of the same item.
-/

namespace TlsMpc.Node.Stock

open TlsMpc.Node.Engine

/-- A circuit shape: which lowered circuit, which size class, which client profile. Items of
one shape are interchangeable; each shape has its own stock, key chain and journal. -/
structure ShapeId where
  circuit : Bytes
  sizeClass : Nat
  profile : Bytes
  deriving DecidableEq, Repr

def ShapeId.enc (s : ShapeId) : Bytes := Enc.bytes s.circuit ++ (Enc.u64 s.sizeClass ++ Enc.bytes s.profile)

def ShapeId.Bounded (s : ShapeId) : Prop :=
  s.circuit.length < B64 ∧ s.sizeClass < B64 ∧ s.profile.length < B64

def decShape : Dec ShapeId := do
  let c ← Dec.bytes
  let n ← Dec.u64
  let p ← Dec.bytes
  pure ⟨c, n, p⟩

theorem shape_enc (s : ShapeId) (hs : s.Bounded) (rest : Bytes) :
    decShape (s.enc ++ rest) = some (s, rest) := by
  obtain ⟨h1, h2, h3⟩ := hs
  simp [decShape, ShapeId.enc, h1, h2, h3]

/-- "x1-stock" -/
def magic : Bytes := ascii "x1-stock"

def version : Nat := 1

theorem magic_length : magic.length = 8 := by decide

/-- A stock's header (one file per shape). -/
structure Header where
  shape : ShapeId
  manifest : Bytes
  bootId : Bytes
  stockId : Bytes
  itemLen : Nat
  deriving DecidableEq, Repr

def Header.Bounded (h : Header) : Prop :=
  h.shape.Bounded ∧ h.manifest.length = 32 ∧ h.bootId.length = 32 ∧ h.stockId.length = 32 ∧
    h.itemLen < B64

def encHeader (h : Header) : Bytes :=
  magic ++ (Enc.u64 version ++ (h.shape.enc ++ (h.manifest ++ (h.bootId ++ (h.stockId ++ Enc.u64 h.itemLen)))))

def decHeader : Dec Header := do
  let m ← Dec.take 8
  if m = magic then
    let v ← Dec.u64
    if v = version then
      let sh ← decShape
      let man ← Dec.take 32
      let b ← Dec.take 32
      let s ← Dec.take 32
      let n ← Dec.u64
      pure ⟨sh, man, b, s, n⟩
    else Dec.fail
  else Dec.fail

/-- The header file's content, or `none` (the stock is refused). -/
def parseHeader (s : Bytes) : Option Header :=
  match decHeader s with
  | some (h, []) => some h
  | _ => none

theorem header_enc (h : Header) (hb : h.Bounded) (rest : Bytes) :
    decHeader (encHeader h ++ rest) = some (h, rest) := by
  obtain ⟨hs, hm, hbt, hst, hi⟩ := hb
  have hv : version < B64 := by decide
  simp only [decHeader, encHeader, List.append_assoc, Dec.bind_apply,
    take_enc 8 magic _ magic_length, if_true, u64_enc _ hv, shape_enc _ hs,
    take_enc 32 _ _ hm, take_enc 32 _ _ hbt, take_enc 32 _ _ hst, u64_enc _ hi, Dec.pure_apply]

/-- **Round trip of the header.** -/
theorem parseHeader_encHeader (h : Header) (hb : h.Bounded) : parseHeader (encHeader h) = some h := by
  have := header_enc h hb []
  rw [List.append_nil] at this
  simp [parseHeader, this]

/-- The tag length of the item cipher (ChaCha20-Poly1305, and the HMAC test cipher). -/
def tagLen : Nat := 16

/-- What is stored in the clear in front of an item's sealed bytes. -/
structure ItemHead where
  index : Nat
  length : Nat
  agreed : Bytes
  deriving DecidableEq, Repr

def ItemHead.Bounded (it : ItemHead) : Prop := it.index < B64 ∧ it.length < B64 ∧ it.agreed.length = 32

def encItem (it : ItemHead) (sealed : Bytes) : Bytes :=
  Enc.u64 it.index ++ (Enc.u64 it.length ++ (it.agreed ++ sealed))

def decItem : Dec (ItemHead × Bytes) := do
  let i ← Dec.u64
  let l ← Dec.u64
  let a ← Dec.take 32
  let c ← Dec.take (l + tagLen)
  pure (⟨i, l, a⟩, c)

/-- The size of one item record for items of `itemLen` bytes. -/
def recordLen (itemLen : Nat) : Nat := 8 + 8 + 32 + itemLen + tagLen

theorem item_enc (it : ItemHead) (hb : it.Bounded) (sealed : Bytes) (hs : sealed.length = it.length + tagLen)
    (rest : Bytes) : decItem (encItem it sealed ++ rest) = some ((it, sealed), rest) := by
  obtain ⟨hi, hl, ha⟩ := hb
  simp only [decItem, encItem, List.append_assoc, Dec.bind_apply, u64_enc _ hi, u64_enc _ hl,
    take_enc 32 _ _ ha, take_enc _ _ _ hs, Dec.pure_apply]

theorem encItem_length (it : ItemHead) (hb : it.Bounded) (sealed : Bytes) (hs : sealed.length = it.length + tagLen) :
    (encItem it sealed).length = recordLen it.length := by
  obtain ⟨_, _, ha⟩ := hb
  simp only [encItem, List.length_append, Enc.u64, length_le, ha, hs, recordLen]
  omega

/-- The associated data of item `it` of the stock with header `h`. -/
def itemAad (h : Header) (it : ItemHead) : Bytes :=
  ascii "x1-item-v1" ++ (h.bootId ++ (h.stockId ++ (h.manifest ++ (h.shape.enc ++
    (Enc.u64 it.index ++ (Enc.u64 it.length ++ it.agreed))))))

/-- The associated data determines the boot id, the stock id, the manifest, the shape and the
index: an item sealed for one of them does not open for another (with an authenticated cipher). -/
theorem itemAad_inj (h h' : Header) (it it' : ItemHead) (hb : h.Bounded) (hb' : h'.Bounded)
    (hi : it.Bounded) (hi' : it'.Bounded) (he : itemAad h it = itemAad h' it') :
    h.bootId = h'.bootId ∧ h.stockId = h'.stockId ∧ h.manifest = h'.manifest ∧ h.shape = h'.shape ∧
      it = it' := by
  obtain ⟨hs, hm, hbt, hst, _⟩ := hb
  obtain ⟨hs', hm', hbt', hst', _⟩ := hb'
  obtain ⟨hii, hil, hia⟩ := hi
  obtain ⟨hii', hil', hia'⟩ := hi'
  simp only [itemAad, List.append_cancel_left_eq] at he
  -- read the fields back with the decoders
  have key : ∀ (H : Header) (I : ItemHead), H.bootId.length = 32 → H.stockId.length = 32 →
      H.manifest.length = 32 → H.shape.Bounded → I.Bounded →
      (do let b ← Dec.take 32; let s ← Dec.take 32; let m ← Dec.take 32; let sh ← decShape
          let i ← Dec.u64; let l ← Dec.u64; let a ← Dec.take 32; pure (b, s, m, sh, (⟨i, l, a⟩ : ItemHead)) : Dec _)
        (H.bootId ++ (H.stockId ++ (H.manifest ++ (H.shape.enc ++ (Enc.u64 I.index ++
          (Enc.u64 I.length ++ I.agreed)))))) = some ((H.bootId, H.stockId, H.manifest, H.shape, I), []) := by
    intro H I h1 h2 h3 h4 h5
    obtain ⟨i1, i2, i3⟩ := h5
    have e3 : I.agreed = I.agreed ++ [] := (List.append_nil _).symm
    rw [e3]
    simp only [Dec.bind_apply, take_enc 32 _ _ h1, take_enc 32 _ _ h2, take_enc 32 _ _ h3,
      shape_enc _ h4, u64_enc _ i1, u64_enc _ i2, take_enc 32 _ _ i3, Dec.pure_apply]
  have k1 := key h it hbt hst hm hs ⟨hii, hil, hia⟩
  have k2 := key h' it' hbt' hst' hm' hs' ⟨hii', hil', hia'⟩
  rw [he] at k1
  rw [k1] at k2
  simp only [Option.some.injEq, Prod.mk.injEq] at k2
  obtain ⟨⟨a, b, c, d, e⟩, _⟩ := k2
  exact ⟨a, b, c, d, e⟩

/-- The journal check of watermark `w` in the stock `stockId`, from a hash `H` (SHA-256). -/
def journalTag (H : Bytes → Bytes) (stockId : Bytes) (w : Nat) : Bytes :=
  (H (ascii "x1-journal-v1" ++ (stockId ++ Enc.u64 w))).take 8

theorem journalTag_length (H : Bytes → Bytes) (hH : ∀ m, 8 ≤ (H m).length) (stockId : Bytes) (w : Nat) :
    (journalTag H stockId w).length = 8 := by
  simp [journalTag, List.length_take, Nat.min_eq_left (hH _)]

/-- One step of the key chain. -/
def chainNext (H : Bytes → Bytes) (c : Bytes) : Bytes := H (ascii "x1-chain-v1" ++ c)

/-- The key of the item whose chain value is `c`. -/
def itemKey (H : Bytes → Bytes) (c : Bytes) : Bytes := H (ascii "x1-item-key-v1" ++ c)

/-- The chain value of index `i` from the seed `c₀`. -/
def chainAt (H : Bytes → Bytes) (c₀ : Bytes) : Nat → Bytes
  | 0 => c₀
  | i + 1 => chainNext H (chainAt H c₀ i)

/-- The chain only goes forward: from the value at `i`, the value at any `i + d` is computable,
and nothing else is needed. (That the values below `i` are NOT computable from it is the
one-wayness of `H`, an assumption about SHA-256, not a theorem here.) -/
theorem chainAt_add (H : Bytes → Bytes) (c₀ : Bytes) (i d : Nat) :
    chainAt H c₀ (i + d) = chainAt H (chainAt H c₀ i) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show chainNext H (chainAt H c₀ (i + d)) = chainNext H (chainAt H (chainAt H c₀ i) d)
    rw [ih]

/-- A node's claim in the per-message agreement: its next index, or `none` when it has no usable
stock of the shape (the message is then preprocessed live). -/
def encClaim : Option Nat → Bytes
  | none => [0]
  | some n => 1 :: Enc.u64 n

def decClaim (s : Bytes) : Option (Option Nat) :=
  match s with
  | [0] => some none
  | 1 :: rest => if rest.length = 8 then some (some (fromLE rest)) else none
  | _ => none

theorem decClaim_encClaim (c : Option Nat) (hc : ∀ n, c = some n → n < B64) : decClaim (encClaim c) = some c := by
  cases c with
  | none => rfl
  | some n =>
    have hn := hc n rfl
    simp only [encClaim, decClaim, Enc.u64, length_le, if_true, fromLE_le]
    rw [Nat.mod_eq_of_lt (by simpa [B64] using hn)]

end TlsMpc.Node.Stock
