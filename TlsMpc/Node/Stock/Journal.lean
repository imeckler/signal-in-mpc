import TlsMpc.Node.Engine

/-!
THE CONSUMED JOURNAL OF THE STOCK, WITH CRASH SEMANTICS, AND THE BOOT ID.

X1 (PRODUCT_TODO.md 11a "Use exactly once"; REORGANIZATION_PLAN.md section 9, T14). Pure: no I/O,
no escape hatch; no emitter imports this module. The Rust store (`node_stock/src/journal.rs`)
implements exactly the byte format and the reading rule below; its tests truncate a journal at
every byte offset and compare with `parse_prefix`.

WHAT THE JOURNAL IS. A stock item (preprocessing for one message: a garbled circuit, or
authenticated triples) must reach the engine at most once. Before an item is handed to the
engine, its index is appended to a per-stock append-only file and the file is synced (fsync).
An entry is a WATERMARK `w`: "every index up to and including `w` is consumed". Taking item `j`
appends `j`; skipping forward to `j` (the peer is ahead) appends `j - 1`. The node's next usable
index is one more than the largest entry (`nextOf`), so a journal never needs to be read in
order and an entry can only move the next index forward.

THE CRASH MODEL (byte level, the one the Rust store and its tests use). The file is the
concatenation of fixed-size records (`recLen` = 16 bytes: the watermark as u64 little-endian,
then an 8-byte check `tag w`, Format.journalTag: a hash of the stock id and the watermark).
Appends write whole records at the end; a sync makes everything written so far durable. A crash
leaves, on disk, a PREFIX of the bytes written, at least as long as the synced part:
  - synced bytes are never lost;
  - unsynced bytes may be lost, from the end, at any byte offset (a torn last record);
  - nothing is reordered, and no bytes are invented.
For a process crash within one boot this is conservative (the page cache keeps every write); for
a power loss the stock is unusable anyway (the boot id below), so the model never has to trust
unsynced data after a power loss.

THE READING RULE (`parse`). Complete records are read in order; a final fragment shorter than a
record is a torn tail and is dropped (the store truncates the file to the last complete record
and syncs before appending again); a complete record whose check fails is not something a crash
can produce, so it is corruption: the stock is refused. `parse_prefix`: every crash prefix of a
journal reads as exactly the records it contains in full, `es.take (n / recLen)`.

THE ABSTRACT JOURNAL (`Journal`), used by the use rule (Use.lean): the list of entries appended
and how many of them are known durable. `Journal.crash keep` is the journal after a crash that
kept `keep` of the unsynced bytes, followed by the restart (torn tail dropped, the rest synced).
`Journal.crash_bytes` ties it to the byte level; `crash_durable` (synced entries survive) and
`crash_prefix` (no invented or reordered entries) are the crash model's two clauses.

THE BOOT ID. A random value drawn when the node's boot memory is created and held only in memory
(never written anywhere except into the headers of stocks made during that boot). A stock is
usable only when its header's boot id equals the current boot's (`Hdr.usableIn`). A reboot draws
a new id, so every stock on disk from before is unusable; a disk restored from a snapshot or a
backup carries old headers, so it is unusable too, unless it was taken during the current boot,
which the key chain (Use.lean) covers. The stock's key chain lives in the same boot memory and
is lost with it.
-/

namespace TlsMpc.Node.Stock

open TlsMpc.Node.Engine (Bytes le fromLE B64 length_le fromLE_le)

/-! ## Byte level -/

/-- The size of one journal record: the watermark (8 bytes) and its check (8 bytes). -/
def recLen : Nat := 16

/-- One record: the watermark as u64 little-endian, then its 8-byte check. -/
def encRec (tag : Nat → Bytes) (w : Nat) : Bytes := le 8 w ++ tag w

/-- A journal file holding the given entries, in order. -/
def encAll (tag : Nat → Bytes) : List Nat → Bytes
  | [] => []
  | e :: es => encRec tag e ++ encAll tag es

/-- Read a journal file: the complete records, in order; a final fragment shorter than a record
(a torn tail) is dropped; a complete record with a wrong check is corruption (`none`). -/
def parse (tag : Nat → Bytes) (s : Bytes) : Option (List Nat) :=
  if s.length < recLen then some []
  else
    let w := fromLE (s.take 8)
    if (s.drop 8).take 8 = tag w then (parse tag (s.drop recLen)).map (w :: ·) else none
termination_by s.length
decreasing_by simp only [List.length_drop, recLen] at *; omega

theorem encRec_length (tag : Nat → Bytes) (htag : ∀ w, (tag w).length = 8) (w : Nat) :
    (encRec tag w).length = recLen := by
  simp [encRec, length_le, htag, recLen]

theorem encAll_length (tag : Nat → Bytes) (htag : ∀ w, (tag w).length = 8) (es : List Nat) :
    (encAll tag es).length = recLen * es.length := by
  induction es with
  | nil => simp [encAll]
  | cons e es ih =>
    simp only [encAll, List.length_append, encRec_length tag htag, ih, List.length_cons]
    simp only [recLen]; omega

/-- **Torn tails.** Every prefix of a journal file, cut at any byte offset `n`, reads as exactly
the records it contains in full. In particular a crash never yields a corrupt journal, never a
record that was not written, and never loses a record whose bytes survived. -/
theorem parse_prefix (tag : Nat → Bytes) (htag : ∀ w, (tag w).length = 8) :
    ∀ (es : List Nat), (∀ e ∈ es, e < B64) →
      ∀ n, parse tag ((encAll tag es).take n) = some (es.take (n / recLen))
  | [], _, n => by
    rw [parse]
    simp [encAll, recLen]
  | e :: es, hes, n => by
    have he : e < B64 := hes e (by simp)
    have ih := parse_prefix tag htag es (fun x hx => hes x (by simp [hx]))
    have hrec := encRec_length tag htag e
    by_cases hn : n < recLen
    · have hlen : ((encAll tag (e :: es)).take n).length < recLen := by
        simp only [List.length_take]; omega
      rw [parse, if_pos hlen, Nat.div_eq_of_lt hn]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + recLen := ⟨n - recLen, by omega⟩
      have hsplit : (encAll tag (e :: es)).take (m + recLen) =
          le 8 e ++ (tag e ++ (encAll tag es).take m) := by
        have hle : (encRec tag e).length ≤ m + recLen := by rw [hrec]; omega
        rw [encAll, List.take_append, List.take_of_length_le hle, hrec, Nat.add_sub_cancel, encRec,
          List.append_assoc]
      have hl8 : (le 8 e).length = 8 := length_le 8 e
      have he8 : fromLE (le 8 e) = e := by
        rw [fromLE_le]; exact Nat.mod_eq_of_lt (by simpa [B64] using he)
      have hlen : ¬ (le 8 e ++ (tag e ++ (encAll tag es).take m)).length < recLen := by
        simp only [List.length_append, hl8, htag, recLen]; omega
      have hdrop : (le 8 e ++ (tag e ++ (encAll tag es).take m)).drop recLen = (encAll tag es).take m := by
        rw [show recLen = 8 + 8 from rfl, ← List.drop_drop, List.drop_left' hl8, List.drop_left' (htag e)]
      rw [hsplit, parse, if_neg hlen]
      simp only [List.take_left' hl8, he8, List.drop_left' hl8, List.take_left' (htag e), if_true]
      rw [hdrop, ih m, Nat.add_div_right m (by decide : 0 < recLen)]
      simp

/-- A journal written in full reads back as its entries. -/
theorem parse_encAll (tag : Nat → Bytes) (htag : ∀ w, (tag w).length = 8) (es : List Nat)
    (hes : ∀ e ∈ es, e < B64) : parse tag (encAll tag es) = some es := by
  have h := parse_prefix tag htag es hes (encAll tag es).length
  rw [List.take_of_length_le (Nat.le_refl _), encAll_length tag htag,
    Nat.mul_div_cancel_left _ (by decide : 0 < recLen), List.take_of_length_le (Nat.le_refl _)] at h
  exact h

/-- **Restart truncation.** Truncating a journal file to its first `k` complete records gives the
file of the first `k` entries (what the store does to a torn tail before it appends again). -/
theorem encAll_take (tag : Nat → Bytes) (htag : ∀ w, (tag w).length = 8) :
    ∀ (es : List Nat) (k : Nat), (encAll tag es).take (recLen * k) = encAll tag (es.take k)
  | [], k => by simp [encAll]
  | e :: es, 0 => by simp [encAll]
  | e :: es, k + 1 => by
    have hrec := encRec_length tag htag e
    rw [show recLen * (k + 1) = recLen * k + recLen by rw [Nat.mul_succ]]
    simp only [encAll, List.take_append, hrec, List.take_succ_cons]
    rw [List.take_of_length_le (by omega), show recLen * k + recLen - recLen = recLen * k by omega,
      encAll_take tag htag es k]

/-! ## The abstract journal -/

/-- One more than the largest entry: the next index a node may use (0 for an empty journal). -/
def nextOf (es : List Nat) : Nat := es.foldr (fun e m => max (e + 1) m) 0

theorem lt_nextOf_of_mem {es : List Nat} {e : Nat} (h : e ∈ es) : e < nextOf es := by
  induction es with
  | nil => simp at h
  | cons x es ih =>
    simp only [List.mem_cons] at h
    simp only [nextOf, List.foldr_cons] at *
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem nextOf_le {es : List Nat} {m : Nat} (h : ∀ e ∈ es, e < m) : nextOf es ≤ m := by
  induction es with
  | nil => simp [nextOf]
  | cons x es ih =>
    simp only [nextOf, List.foldr_cons] at *
    have hx := h x (by simp)
    have := ih (fun e he => h e (by simp [he]))
    omega

/-- Entries can only move the next index forward: a journal containing every entry of another
has a next index at least as large. -/
theorem nextOf_mono {es es' : List Nat} (h : ∀ e ∈ es, e ∈ es') : nextOf es ≤ nextOf es' :=
  nextOf_le (fun e he => lt_nextOf_of_mem (h e he))

theorem nextOf_append (es : List Nat) (e : Nat) : nextOf (es ++ [e]) = max (nextOf es) (e + 1) := by
  induction es with
  | nil => simp [nextOf]
  | cons x es ih =>
    simp only [List.cons_append, nextOf, List.foldr_cons] at *
    rw [ih]; omega

theorem nextOf_take_le (es : List Nat) (k : Nat) : nextOf (es.take k) ≤ nextOf es :=
  nextOf_mono (fun _ h => List.mem_of_mem_take h)

/-- The journal of one stock, abstractly: the entries appended, in order, and how many of the
first ones are known durable (synced). -/
structure Journal where
  entries : List Nat := []
  synced : Nat := 0
  deriving DecidableEq, Repr

namespace Journal

/-- The next index this journal allows. -/
def next (j : Journal) : Nat := nextOf j.entries

/-- The entries that are durable: no crash loses them. -/
def durable (j : Journal) : List Nat := j.entries.take j.synced

/-- The next index the durable entries alone allow. -/
def durableNext (j : Journal) : Nat := nextOf j.durable

/-- Append an entry (written, not yet durable). -/
def append (j : Journal) (e : Nat) : Journal := { j with entries := j.entries ++ [e] }

/-- Sync (fsync): everything written is durable. -/
def sync (j : Journal) : Journal := { j with synced := j.entries.length }

/-- A crash that kept `keep` bytes of the unsynced records, then the restart: the torn tail is
dropped and what is left is synced (the store truncates and syncs when it opens a journal). -/
def crash (j : Journal) (keep : Nat) : Journal :=
  let es := j.entries.take (j.synced + keep / recLen)
  { entries := es, synced := es.length }

/-- **Synced entries are never lost.** -/
theorem crash_durable (j : Journal) (keep : Nat) :
    (j.crash keep).entries.take j.synced = j.durable := by
  simp only [crash, durable, List.take_take]
  rw [Nat.min_eq_left (Nat.le_add_right _ _)]

/-- **No torn, reordered or invented entries**: after a crash the entries are a prefix of those
appended. -/
theorem crash_prefix (j : Journal) (keep : Nat) : ∃ k, (j.crash keep).entries = j.entries.take k :=
  ⟨_, rfl⟩

/-- After a restart every entry is durable. -/
theorem crash_synced (j : Journal) (keep : Nat) :
    (j.crash keep).synced = (j.crash keep).entries.length := rfl

/-- **Byte level.** The journal file after a crash that kept `keep` unsynced bytes (the file is
cut at `recLen * synced + keep`, possibly inside a record) reads as the abstract crash. -/
theorem crash_bytes (tag : Nat → Bytes) (htag : ∀ w, (tag w).length = 8) (j : Journal)
    (hes : ∀ e ∈ j.entries, e < B64) (keep : Nat) :
    parse tag ((encAll tag j.entries).take (recLen * j.synced + keep)) = some (j.crash keep).entries := by
  rw [parse_prefix tag htag j.entries hes, Nat.mul_add_div (by decide : recLen > 0)]
  rfl

/-- A crash does not lower the next index below what the durable entries allow ... -/
theorem durableNext_le_crash (j : Journal) (keep : Nat) : j.durableNext ≤ (j.crash keep).next := by
  simp only [durableNext, durable, next, crash]
  apply nextOf_mono
  intro e he
  have hpre : j.entries.take j.synced = (j.entries.take (j.synced + keep / recLen)).take j.synced := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  rw [hpre] at he
  exact List.mem_of_mem_take he

/-- ... and does not raise it: a crash never skips forward by itself. -/
theorem crash_next_le (j : Journal) (keep : Nat) : (j.crash keep).next ≤ j.next :=
  nextOf_take_le _ _

/-- **At most the entry in flight is lost.** If everything before the last append was synced,
a crash keeps either all of the earlier entries or all of them and the new one. -/
theorem crash_append (j : Journal) (hs : j.synced = j.entries.length) (e keep : Nat) :
    ((j.append e).crash keep).entries = j.entries ∨ ((j.append e).crash keep).entries = j.entries ++ [e] := by
  simp only [crash, append, hs]
  by_cases h : keep / recLen = 0
  · left
    rw [h, Nat.add_zero, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  · right
    have hpos : 1 ≤ keep / recLen := Nat.pos_of_ne_zero h
    exact List.take_of_length_le (by simp only [List.length_append, List.length_singleton]; omega)

theorem durable_append (j : Journal) (h : j.synced ≤ j.entries.length) (e : Nat) :
    (j.append e).durable = j.durable := by
  simp [durable, append, List.take_append_of_le_length h]

theorem durableNext_le_next (j : Journal) : j.durableNext ≤ j.next := nextOf_take_le _ _

theorem durable_sync (j : Journal) : j.sync.durable = j.entries := by
  simp [durable, sync]

end Journal

/-! ## The stock header's identity and the boot id -/

/-- What the use rule needs of a stock header (Format.Header has the bytes): the boot id of the
boot it was made in and the stock's id. -/
structure Hdr where
  boot : Nat
  id : Nat
  deriving DecidableEq, Repr

/-- A stock is usable only in the boot it was made in. -/
def Hdr.usableIn (h : Hdr) (boot : Nat) : Bool := h.boot == boot

theorem Hdr.not_usable_of_ne {h : Hdr} {boot : Nat} (hne : h.boot ≠ boot) : h.usableIn boot = false := by
  simp [usableIn, hne]

end TlsMpc.Node.Stock
