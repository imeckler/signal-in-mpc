import TlsMpc.TlsWire

/-!
# Connection rotation over Tor with a pool (pure; X2, T15)

PRODUCT_TODO.md section 8 (connection rotation over Tor), REORGANIZATION_PLAN.md section 9 (X2)
and section 8 (T15). New file; pure; no I/O; no emitter imports it. It replaces
`Circuits.assign` (Policy/Circuits.lean) once the session is switched over (ROTATION.md, the
integration to-do). Nothing imports it yet.

## What it decides

For one *batch* of `n` messages (one broadcast, or every broadcast gathered within the hold
window), from a seed of joint randomness (`Random.joint`, 32 bytes that neither node chose
alone), the rotation configuration and `n` only:

* **the send order**: a permutation `order` of the positions `0 … n-1` (`shuffle`): the i-th
  message sent is input `order[i]`;
* **the pool slot of each send**: uniform over the `poolSize` slots, drawn per send;
* **the rotation points**: each connection, when its slot first needs it, draws a budget `L`
  (the number of messages it carries, `drawLength`); after its L-th message it is closed, and
  the slot's next use opens a fresh connection on a fresh Tor circuit;
* **the generations**: every connection opened gets the next generation number (`base`,
  `base + 1`, …), from which its SOCKS5 credentials are made (`labels`), so Tor isolates it on a
  circuit of its own (`IsolateSOCKSAuth`, Tor's default for a SocksPort).

The output is a list of `Action`s: `open slot gen`, `send position slot`, `close slot`, in the
order the executor performs them (`PlanState`, `next`). At the end of the batch every connection
still open is closed.

## The distribution of a connection's message count (`Length`)

Default `uniform`: `L` uniform on `[1, 2·mean − 1]`. Chosen because
* its mean is exactly `mean` (`uniform_mean`), with one draw per connection;
* it has a hard maximum `2·mean − 1` (19 for mean 10): no connection ever links more recipients;
* the number of OTHER recipients a given recipient shares its connection with (the size-biased
  mean, `E[L²]/E[L] − 1`) is `(4·mean − 1)/3 − 1` = 12 for mean 10 (`uniform_second_moment`);
  for a geometric law with the same mean it is `2·mean − 2` = 18.
`geometric cap` is available as a parameter: after each message the connection ends with
probability `1/mean` (memoryless: how long a connection has run says nothing about when it ends),
capped at `cap` messages; its mean is `mean·(1 − (1 − 1/mean)^cap)` (9.85 for mean 10, cap 40).

## Sampling (exact, deterministic, both nodes compute the same plan)

Words: 64-bit lanes of `H(domain ‖ tag ‖ seed ‖ counter)` (`blockInput`, `lanes`), `H` = SHA-256
(`sha256` = `TlsWire.hash`, the definition the send path already hashes with). Two streams with
distinct tags: `shuffleTag` (the shuffle) and `poolTag` (slots and lengths), on disjoint inputs
(`blockInput_tags_differ`). A number below `r`: rejection sampling (`below`): a word `w` is
accepted when `w < r·⌊2⁶⁴/r⌋` and gives `w mod r`; each value has exactly `⌊2⁶⁴/r⌋` accepted
words (`accepted_split`, `accepted_join`: an exact bijection), so an accepted draw is exactly
uniform. At most 4 words per draw (no `partial def`): after 3 rejections the 4th word is used as
`w mod r` whatever it is (the fallback). A word is rejected with probability
`(2⁶⁴ mod r)/2⁶⁴ < r/2⁶⁴` (`rejected_few`); for `r ≤ 2³²` (the plan requires `n < 2³²`) the
fallback is reached with probability `< 2⁻¹²⁸` per draw, `< n·2⁻¹²⁶` per batch.

The shuffle is the selection form of Fisher–Yates (`encode`): draw `d₀ < n`, `d₁ < n − 1`, …,
and take the `dᵢ`-th remaining position. `encode` is a bijection between the draw vectors
(`Valid`) and the permutations of `0 … n-1` (`encode_perm`, `decode_encode`, `encode_decode`),
so uniform draws give a uniform permutation.

**What is assumed about the hash (H-PRF):** for a uniformly random 32-byte seed unknown to the
observer, the map `(tag, k) ↦ H(domain ‖ tag ‖ seed ‖ uint64 k)` is indistinguishable from a
uniformly random function to 32-byte strings (SHA-256 as a PRF keyed by the seed; it holds in the
random-oracle model). Under H-PRF the words are independent and uniform, so: the shuffle is a
uniform permutation up to statistical distance `n·2⁻¹²⁸` plus the PRF advantage; the two streams
are independent, hence the shuffle is independent of the slot/length schedule. Nothing in the
proofs below depends on H-PRF: they hold for every `H`. The seed must be fresh per batch (a new
`Random.joint`), and it is never sent to the server.

## Proved here (for every hash function `H`, seed, count and configuration)

T15 (the plan reveals nothing about ids):
* `plan`, `skeleton` take only `(H, seed, n, cfg, base)`: by construction, no contact id, text,
  per-contact state or result is an argument (T15 holds by the planner's signature);
* `plan_actions`: the actions are the skeleton (sends carrying send indices `0 … n-1`) relabelled
  by the shuffle; `skeleton` reads only the pool stream and `order` only the shuffle stream
  (`plan_order`, `skeleton_def`: definitional);
* `t15_erase`: for two input lists of the same length, the composed sender's actions agree once
  the payloads are erased;
* `t15_carriers`: the sequence of (slot, generation) carrying the i-th sent message is the
  skeleton's, whatever the inputs; `t15_sends`: the i-th sent message is input `order[i]`;
* `shuffle_perm`, `encode_perm`, `decode_encode`, `encode_decode`, `accepted_split`,
  `accepted_join`, `rejected_few`, `blockInput_tags_differ`: the shuffle is a permutation, and the
  pieces of its uniformity.

Well-formedness, against the executor model `Mon` (one slot table, the executor's semantics):
* `plan_accepted`: the monitor accepts the whole action list: an `open` only on a closed slot and
  with the next generation; a `send` only on an open slot whose connection has carried fewer than
  `maxLen` messages; a `close` only on an open slot whose connection carried at least one; at the
  end every slot is closed;
* `plan_sends_perm`: every position is sent exactly once;
* `plan_generations`: the generations opened are `base, base+1, …` in order: none reused;
* `plan_pool_bound`: after every prefix, at most `poolSize` connections are open;
* `plan_counts`: every connection carried between 1 and `maxLen` messages, the counts sum to `n`;
* `plan_connection_bounds`: the number of connections `k` satisfies `k ≤ n ≤ k·maxLen`;
* `plannedAt_bounds`, `plannedAt_zero`: the hold window: a message waits at most `hold` ms before
  its batch is planned, and with `hold = 0` no message waits.

Unlinkability in plain terms (from the above, under H-PRF): two messages share a connection exactly
when the skeleton put their send indices on the same generation, which the pool stream alone
decided; the shuffle, independent of it, then decides which inputs those indices are. So for any
two inputs a ≠ b, the probability that they share a connection is a function of the connection
sizes only (Σ_g k_g(k_g − 1) / (n(n − 1))), the same for every pair: it does not depend on who
they are. A given recipient shares its connection with `(4·mean − 1)/3 − 1` others on average
(uniform law), at most `2·mean − 2`. Over a batch of n messages there are between `⌈n/maxLen⌉`
and `n` connections (proved), about `n/mean` plus at most one partly used connection per slot
(renewal argument, ROTATION.md).
-/

namespace Rotation
open TlsMpc

abbrev Bytes := List UInt8

/-! ## 1. Configuration (`Config.rotation`, to be folded into `Node.Config`) -/

/-- The law of a connection's message count. -/
inductive Length where
  /-- Uniform on `[1, 2·mean − 1]` (the default). -/
  | uniform
  /-- After each message the connection ends with probability `1/mean`, at most `cap` messages. -/
  | geometric (cap : Nat)
  deriving Repr, DecidableEq

/-- The rotation settings (agreed by both nodes, as `Config.Agreed`). `hold` in milliseconds. -/
structure Config where
  mean : Nat := 10
  poolSize : Nat := 4
  hold : Nat := 0
  length : Length := .uniform
  deriving Repr, DecidableEq

namespace Config

/-- The most messages a connection carries. -/
def maxLen (c : Config) : Nat :=
  match c.length with
  | .uniform => 2 * c.mean - 1
  | .geometric cap => cap

/-- Accepted settings: a mean of 1..1000 messages, a pool of 1..16 connections (as
`SIGNAL_TOR_CIRCUITS`), a hold window of at most 10 minutes, a geometric cap of mean..65536. -/
def valid (c : Config) : Bool :=
  1 ≤ c.mean && c.mean ≤ 1000 && 1 ≤ c.poolSize && c.poolSize ≤ 16 && c.hold ≤ 600000 &&
    (match c.length with
     | .uniform => true
     | .geometric cap => c.mean ≤ cap && cap ≤ 65536)

theorem valid_pool (c : Config) (h : c.valid = true) : 0 < c.poolSize := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem valid_maxLen (c : Config) (h : c.valid = true) : 0 < c.maxLen := by
  unfold valid at h
  unfold maxLen
  cases hl : c.length with
  | uniform => simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; omega
  | geometric cap => simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; omega

end Config

/-- The plan's count bound: below it every draw range is at most 2³² (the fallback bound). -/
def maxCount : Nat := 2 ^ 32

/-! ## 2. The expander: 64-bit words from the seed -/

/-- SHA-256, the definition the send path hashes with (`TlsWire.hash`). -/
def sha256 (b : Bytes) : Bytes := TlsWire.hash b

def domain : Bytes := "tls-mpc rotation v1".toUTF8.data.toList
def shuffleTag : UInt8 := 0
def poolTag : UInt8 := 1

/-- The hash input of block `k` of stream `tag`: `domain ‖ tag ‖ seed ‖ uint64 k`. -/
def blockInput (seed : Bytes) (tag : UInt8) (k : Nat) : Bytes :=
  domain ++ tag :: (seed ++ TlsWire.uint 8 k)

/-- Four 64-bit big-endian words of a 32-byte block. -/
def lanes (b : Bytes) : List Nat :=
  (List.range 4).map (fun i => TlsWire.number ((b.drop (8 * i)).take 8))

/-- A stream of words: block function, next block, words of the current block not used yet. -/
structure Stream where
  blk : Nat → Bytes
  block : Nat := 0
  buf : List Nat := []

/-- Stream `tag` of `seed` under `H`. It depends on `H` only through `k ↦ H (blockInput seed tag k)`. -/
def Stream.start (H : Bytes → Bytes) (seed : Bytes) (tag : UInt8) : Stream :=
  { blk := fun k => H (blockInput seed tag k) }

/-- The next word. -/
def Stream.word (s : Stream) : Nat × Stream :=
  match s.buf with
  | w :: rest => (w, { s with buf := rest })
  | [] =>
    match lanes (s.blk s.block) with
    | w :: rest => (w, { s with block := s.block + 1, buf := rest })
    | [] => (0, { s with block := s.block + 1 })

/-- **Domain separation**: no block of the shuffle stream has the hash input of a block of the pool
stream (whatever the seeds and counters). -/
theorem blockInput_tags_differ (seed seed' : Bytes) (k k' : Nat) :
    blockInput seed shuffleTag k ≠ blockInput seed' poolTag k' := by
  intro h
  have := congrArg (fun l : Bytes => l[domain.length]?) h
  simp [blockInput, shuffleTag, poolTag] at this

/-! ## 3. Exact uniform draws by rejection -/

/-- The accepted words for range `r`: `w < r·⌊2⁶⁴/r⌋`. -/
def zone (r : Nat) : Nat := r * (2 ^ 64 / r)

/-- `k + 1` words at most; the last one is used whatever it is (the fallback). -/
def belowAux (r : Nat) : Nat → Stream → Nat × Stream
  | 0, s => let w := s.word; (w.1 % r, w.2)
  | k + 1, s => let w := s.word; if w.1 < zone r then (w.1 % r, w.2) else belowAux r k w.2

/-- A number below `r` (`r > 0`): at most 4 words. -/
def below (s : Stream) (r : Nat) : Nat × Stream := belowAux r 3 s

theorem belowAux_lt (r : Nat) (hr : 0 < r) : ∀ (k : Nat) (s : Stream), (belowAux r k s).1 < r
  | 0, s => by simp only [belowAux]; exact Nat.mod_lt _ hr
  | k + 1, s => by
    simp only [belowAux]
    split
    · exact Nat.mod_lt _ hr
    · exact belowAux_lt r hr k _

theorem below_lt (s : Stream) (r : Nat) (hr : 0 < r) : (below s r).1 < r := belowAux_lt r hr 3 s

/-- An accepted word is a value below `r` and an index below `⌊2⁶⁴/r⌋`, and is determined by them. -/
theorem accepted_split (r w : Nat) (hr : 0 < r) (hw : w < zone r) :
    w % r < r ∧ w / r < 2 ^ 64 / r ∧ w % r + r * (w / r) = w := by
  refine ⟨Nat.mod_lt _ hr, ?_, Nat.mod_add_div w r⟩
  rw [Nat.div_lt_iff_lt_mul hr]
  unfold zone at hw
  rw [Nat.mul_comm] at hw
  exact hw

/-- Every value `v < r` and index `j < ⌊2⁶⁴/r⌋` is the split of exactly one accepted word. With
`accepted_split`: the accepted words are in bijection with `[0, r) × [0, ⌊2⁶⁴/r⌋)`, so each value
has exactly `⌊2⁶⁴/r⌋` accepted words: an accepted uniform word gives an exactly uniform value. -/
theorem accepted_join (r v j : Nat) (hv : v < r) (hj : j < 2 ^ 64 / r) :
    v + r * j < zone r ∧ (v + r * j) % r = v ∧ (v + r * j) / r = j := by
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hv
  refine ⟨?_, ?_, ?_⟩
  · unfold zone
    have : r * (j + 1) ≤ r * (2 ^ 64 / r) := Nat.mul_le_mul_left r hj
    rw [Nat.mul_succ] at this
    omega
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hv, Nat.zero_add]

/-- Fewer than `r` of the `2⁶⁴` words are rejected. -/
theorem rejected_few (r : Nat) (hr : 0 < r) : 2 ^ 64 - zone r < r := by
  have h1 := Nat.mod_add_div (2 ^ 64) r
  have h2 := Nat.mod_lt (2 ^ 64) hr
  unfold zone
  omega

/-! ## 4. The shuffle: selection-form Fisher–Yates, a bijection -/

/-- The `i`-th element and the rest. -/
def takeAt {α : Type} : List α → Nat → Option (α × List α)
  | [], _ => none
  | x :: xs, 0 => some (x, xs)
  | x :: xs, i + 1 => (takeAt xs i).map (fun r => (r.1, x :: r.2))

/-- The draw vectors: `dᵢ < k − i` for a list of `k` elements. -/
def Valid : Nat → List Nat → Prop
  | 0, [] => True
  | k + 1, d :: ds => d < k + 1 ∧ Valid k ds
  | _, _ => False

/-- The permutation of `rest` that the draws select. -/
def encode {α : Type} : List α → List Nat → List α
  | _, [] => []
  | rest, d :: ds =>
    match takeAt rest d with
    | some (y, r) => y :: encode r ds
    | none => []

/-- Index of the first occurrence (the length when absent). -/
def position {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | x :: xs, a => if a = x then 0 else position xs a + 1

/-- The draws that select `π` from `rest` (the inverse of `encode`). -/
def decode {α : Type} [DecidableEq α] : List α → List α → List Nat
  | _, [] => []
  | rest, a :: as => position rest a :: decode (rest.erase a) as

/-- `n` draws: below `n`, below `n − 1`, …, below 1. -/
def draws : Nat → Stream → List Nat × Stream
  | 0, s => ([], s)
  | k + 1, s => let d := below s (k + 1); let r := draws k d.2; (d.1 :: r.1, r.2)

/-- The send order: `order[i]` is the position sent i-th. -/
def shuffle (s : Stream) (n : Nat) : List Nat := encode (List.range n) (draws n s).1

section Shuffle
variable {α : Type}

theorem takeAt_perm : ∀ (l : List α) (i : Nat) (y : α) (r : List α),
    takeAt l i = some (y, r) → List.Perm l (y :: r)
  | [], _, _, _, h => by simp [takeAt] at h
  | x :: xs, 0, y, r, h => by
    simp only [takeAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact List.Perm.refl _
  | x :: xs, i + 1, y, r, h => by
    cases h1 : takeAt xs i with
    | none => simp [takeAt, h1] at h
    | some p =>
      obtain ⟨y', r'⟩ := p
      simp only [takeAt, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ((takeAt_perm xs i y' r' h1).cons x).trans (List.Perm.swap _ _ _)

theorem takeAt_lt : ∀ (l : List α) (i : Nat), i < l.length →
    ∃ y r, takeAt l i = some (y, r) ∧ r.length + 1 = l.length
  | [], _, h => by simp at h
  | x :: xs, 0, _ => ⟨x, xs, rfl, rfl⟩
  | x :: xs, i + 1, h => by
    obtain ⟨y, r, h1, h2⟩ := takeAt_lt xs i (by simp at h; omega)
    exact ⟨y, x :: r, by simp [takeAt, h1], by simp [h2]⟩

theorem position_lt [DecidableEq α] : ∀ (l : List α) (a : α), a ∈ l → position l a < l.length
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    by_cases hax : a = x
    · simp [position, hax]
    · have hm : a ∈ xs := by simpa [hax] using h
      have := position_lt xs a hm
      simp [position, hax]
      omega

theorem takeAt_position [DecidableEq α] : ∀ (l : List α) (a : α), a ∈ l →
    takeAt l (position l a) = some (a, l.erase a)
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    by_cases hax : a = x
    · subst hax
      simp [position, takeAt]
    · have hm : a ∈ xs := by simpa [hax] using h
      have hne : ¬(x == a) = true := by simpa using fun e : x = a => hax e.symm
      simp only [position, hax, if_false, takeAt, takeAt_position xs a hm, Option.map_some,
        List.erase_cons_tail hne]

theorem position_takeAt [DecidableEq α] : ∀ (l : List α) (i : Nat) (y : α) (r : List α),
    l.Nodup → takeAt l i = some (y, r) → position l y = i ∧ l.erase y = r
  | [], _, _, _, _, h => by simp [takeAt] at h
  | x :: xs, 0, y, r, _, h => by
    simp only [takeAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [position]
  | x :: xs, i + 1, y, r, hd, h => by
    cases h1 : takeAt xs i with
    | none => simp [takeAt, h1] at h
    | some p =>
      obtain ⟨y', r'⟩ := p
      simp only [takeAt, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd' := List.nodup_cons.mp hd
      obtain ⟨h2, h3⟩ := position_takeAt xs i y' r' hd'.2 h1
      have hmem : y' ∈ xs := (takeAt_perm xs i y' r' h1).mem_iff.mpr (by simp)
      have hne : y' ≠ x := fun e => hd'.1 (e ▸ hmem)
      have hne' : ¬(x == y') = true := by simpa using fun e : x = y' => hne e.symm
      refine ⟨by simp [position, hne, h2], ?_⟩
      rw [List.erase_cons_tail hne', h3]

/-- **The shuffle is a permutation**: valid draws select a permutation of `rest`. -/
theorem encode_perm : ∀ (ds : List Nat) (l : List α), Valid l.length ds → List.Perm (encode l ds) l
  | [], l, h => by
    cases l with
    | nil => simp [encode]
    | cons x xs => simp [Valid] at h
  | d :: ds, l, h => by
    rcases hlen : l.length with _ | k
    · rw [hlen] at h; simp [Valid] at h
    · rw [hlen] at h
      simp only [Valid] at h
      obtain ⟨y, r, ht, hr⟩ := takeAt_lt l d (by omega)
      have hrk : r.length = k := by omega
      simp only [encode, ht]
      exact ((encode_perm ds r (hrk ▸ h.2)).cons y).trans (takeAt_perm l d y r ht).symm

/-- **Injective**: the draws are recovered from the permutation they select. -/
theorem decode_encode [DecidableEq α] : ∀ (ds : List Nat) (l : List α), l.Nodup →
    Valid l.length ds → decode l (encode l ds) = ds
  | [], _, _, _ => by simp [encode, decode]
  | d :: ds, l, hn, h => by
    rcases hlen : l.length with _ | k
    · rw [hlen] at h; simp [Valid] at h
    · rw [hlen] at h
      simp only [Valid] at h
      obtain ⟨y, r, ht, hr⟩ := takeAt_lt l d (by omega)
      obtain ⟨hp, he⟩ := position_takeAt l d y r hn ht
      have hnr : r.Nodup := (List.nodup_cons.mp ((takeAt_perm l d y r ht).nodup_iff.mp hn)).2
      have hrk : r.length = k := by omega
      simp only [encode, ht, decode, hp, he]
      rw [decode_encode ds r hnr (hrk ▸ h.2)]

/-- **Surjective**: every permutation of `rest` is selected, by valid draws. -/
theorem encode_decode [DecidableEq α] : ∀ (π l : List α), List.Perm π l →
    encode l (decode l π) = π ∧ Valid l.length (decode l π)
  | [], l, h => by
    have : l = [] := List.Perm.eq_nil h.symm
    subst this
    simp [encode, decode, Valid]
  | a :: π, l, h => by
    have ha : a ∈ l := h.mem_iff.mp (by simp)
    have hp : List.Perm π (l.erase a) := by simpa using h.erase a
    obtain ⟨h1, h2⟩ := encode_decode π (l.erase a) hp
    have hlen := List.length_erase_of_mem ha
    have hpos := position_lt l a ha
    refine ⟨by simp [decode, encode, takeAt_position l a ha, h1], ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 := ⟨l.length - 1, by omega⟩
    rw [hk]
    simp only [decode, Valid]
    exact ⟨by omega, by rw [hlen, hk] at h2; simpa using h2⟩

end Shuffle

theorem draws_valid : ∀ (n : Nat) (s : Stream), Valid n (draws n s).1
  | 0, _ => by simp [draws, Valid]
  | k + 1, s => by
    simp only [draws, Valid]
    exact ⟨below_lt s (k + 1) (Nat.succ_pos k), draws_valid k _⟩

/-- **The send order is a permutation of the positions.** -/
theorem shuffle_perm (s : Stream) (n : Nat) : List.Perm (shuffle s n) (List.range n) :=
  encode_perm _ _ (by simpa using draws_valid n s)

theorem shuffle_length (s : Stream) (n : Nat) : (shuffle s n).length = n := by
  simpa using (shuffle_perm s n).length_eq

/-! ## 5. Connection lengths -/

def geoAux (m : Nat) : Nat → Nat → Stream → Nat × Stream
  | 0, acc, s => (acc, s)
  | k + 1, acc, s => let d := below s m; if d.1 = 0 then (acc, d.2) else geoAux m k (acc + 1) d.2

/-- A new connection's budget (messages it will carry). -/
def drawLength (cfg : Config) (s : Stream) : Nat × Stream :=
  match cfg.length with
  | .uniform => let d := below s (2 * cfg.mean - 1); (d.1 + 1, d.2)
  | .geometric cap => geoAux cfg.mean (cap - 1) 1 s

theorem geoAux_bounds (m : Nat) : ∀ (k acc : Nat) (s : Stream),
    acc ≤ (geoAux m k acc s).1 ∧ (geoAux m k acc s).1 ≤ acc + k
  | 0, acc, s => by simp [geoAux]
  | k + 1, acc, s => by
    simp only [geoAux]
    split
    · omega
    · have := geoAux_bounds m k (acc + 1) (below s m).2
      omega

theorem drawLength_bounds (cfg : Config) (s : Stream) (h : 0 < cfg.maxLen) :
    1 ≤ (drawLength cfg s).1 ∧ (drawLength cfg s).1 ≤ cfg.maxLen := by
  unfold drawLength
  unfold Config.maxLen at h ⊢
  cases hl : cfg.length with
  | uniform =>
    simp only [hl] at h ⊢
    have := below_lt s (2 * cfg.mean - 1) h
    omega
  | geometric cap =>
    simp only [hl] at h ⊢
    have := geoAux_bounds cfg.mean (cap - 1) 1 s
    omega

/-- The support of the uniform law sums to `(support size)·mean`: its mean is `mean`. -/
theorem sum_range_succ (k : Nat) : ((List.range k).map (· + 1)).sum * 2 = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append]; simp; grind

theorem uniform_mean (m : Nat) (hm : 1 ≤ m) :
    ((List.range (2 * m - 1)).map (· + 1)).sum = m * (2 * m - 1) := by
  have h := sum_range_succ (2 * m - 1)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [h2] at h ⊢
  grind

/-- The second moment: `Σ_{L=1}^{2m−1} L² · 3 = m(2m − 1)(4m − 1)`, so `E[L²]/E[L] = (4m − 1)/3`:
the mean size of the connection a given message is on (13 for mean 10). -/
theorem sum_sq_range (k : Nat) : ((List.range k).map (fun i => (i + 1) * (i + 1))).sum * 6 =
    k * (k + 1) * (2 * k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append]; simp; grind

theorem uniform_second_moment (m : Nat) (hm : 1 ≤ m) :
    ((List.range (2 * m - 1)).map (fun i => (i + 1) * (i + 1))).sum * 3 =
      m * (2 * m - 1) * (4 * m - 1) := by
  have h := sum_sq_range (2 * m - 1)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h3 : 4 * (k + 1) - 1 = 4 * k + 3 := by omega
  rw [h2] at h ⊢
  rw [h3]
  grind

/-! ## 6. Actions and the planner -/

/-- What the executor does, in order. `open slot gen`: a new connection on that slot, on a fresh
circuit (credentials `labels session gen 0`), with its handshake and upgrade. `send position slot`:
the message at that position, on the slot's connection. `close slot`: close it (op 92). -/
inductive Action (α : Type) where
  | «open» (slot gen : Nat)
  | send (position : α) (slot : Nat)
  | close (slot : Nat)
  deriving Repr, DecidableEq

namespace Action
def map {α β : Type} (f : α → β) : Action α → Action β
  | .«open» s g => .«open» s g
  | .send x s => .send (f x) s
  | .close s => .close s

/-- The action without its payload. -/
def erase {α : Type} (a : Action α) : Action Unit := a.map (fun _ => ())

def sendOf {α : Type} : Action α → Option α
  | .send x _ => some x
  | _ => none

def openOf {α : Type} : Action α → Option Nat
  | .«open» _ g => some g
  | _ => none

theorem erase_map {α β : Type} (f : α → β) (a : Action α) : (a.map f).erase = a.erase := by
  cases a <;> rfl

theorem sendOf_map {α β : Type} (f : α → β) (a : Action α) : (a.map f).sendOf = a.sendOf.map f := by
  cases a <;> rfl
end Action

/-- The positions sent, in order. -/
def sendsOf {α : Type} (acts : List (Action α)) : List α := acts.filterMap Action.sendOf

/-- The generations opened, in order. -/
def opensOf {α : Type} (acts : List (Action α)) : List Nat := acts.filterMap Action.openOf

/-- An open connection: generation, messages it may still carry, messages carried. -/
structure Conn where
  gen : Nat
  left : Nat
  carried : Nat
  deriving Repr, DecidableEq

def Conn.view (c : Conn) : Nat × Nat := (c.gen, c.carried)

/-- The pool: one entry per slot (`none`: no connection), the next generation. -/
structure Pool where
  slots : List (Option Conn)
  next : Nat
  deriving Repr

def Pool.empty (poolSize base : Nat) : Pool := ⟨List.replicate poolSize none, base⟩

/-- Entry `i` of a slot table (`none` past its end). -/
def look {β : Type} (l : List (Option β)) (i : Nat) : Option β := l[i]?.getD none

/-- Send on `slot`'s connection `c`; close it when this was its last message. -/
def place {α : Type} (slot : Nat) (x : α) (c : Conn) (p : Pool) : List (Action α) × Pool :=
  if c.left ≤ 1 then ([.send x slot, .close slot], { p with slots := p.slots.set slot none })
  else ([.send x slot], { p with slots := p.slots.set slot (some { c with left := c.left - 1, carried := c.carried + 1 }) })

/-- One message: draw its slot; open a connection there if there is none (drawing its budget);
send; close when the budget is used up. -/
def stepMsg {α : Type} (cfg : Config) (x : α) (p : Pool) (s : Stream) : List (Action α) × Pool × Stream :=
  let d := below s cfg.poolSize
  match look p.slots d.1 with
  | some c => ((place d.1 x c p).1, (place d.1 x c p).2, d.2)
  | none =>
    let l := drawLength cfg d.2
    let r := place d.1 x ⟨p.next, l.1, 0⟩ { p with next := p.next + 1 }
    (.«open» d.1 p.next :: r.1, r.2, l.2)

def schedule {α : Type} (cfg : Config) : List α → Pool → Stream → List (Action α) × Pool × Stream
  | [], p, s => ([], p, s)
  | x :: xs, p, s =>
    let a := stepMsg cfg x p s
    let b := schedule cfg xs a.2.1 a.2.2
    (a.1 ++ b.1, b.2)

/-- At the end of the batch: close every slot still open, in slot order. -/
def closeFrom {α : Type} : Nat → List (Option Conn) → List (Action α)
  | _, [] => []
  | i, none :: r => closeFrom (i + 1) r
  | i, some _ :: r => .close i :: closeFrom (i + 1) r

/-- The actions for the messages `xs` (in send order) from an empty pool, generations from `base`. -/
def runPool {α : Type} (cfg : Config) (xs : List α) (base : Nat) (s : Stream) : List (Action α) :=
  let r := schedule cfg xs (Pool.empty cfg.poolSize base) s
  r.1 ++ closeFrom 0 r.2.1.slots

/-- A batch's plan: the send order and the actions (sends carry positions). -/
structure Plan where
  order : List Nat
  actions : List (Action Nat)
  deriving Repr

/-- The plan's skeleton: its actions with each send carrying its send index (0, 1, …). A function of
the pool stream alone. -/
def skeleton (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) : List (Action Nat) :=
  runPool cfg (List.range n) base (Stream.start H seed poolTag)

/-- **The plan of a batch.** Its arguments are all it depends on: the hash, the joint random seed,
the message count, the configuration, the first generation. -/
def plan (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) : Plan :=
  let order := shuffle (Stream.start H seed shuffleTag) n
  { order, actions := runPool cfg order base (Stream.start H seed poolTag) }

/-- The composed sender: the plan's actions with each position replaced by its input (contact,
text, state: anything). -/
def compose {β : Type} (H : Bytes → Bytes) (seed : Bytes) (cfg : Config) (base : Nat)
    (inputs : List β) (default : β) : List (Action β) :=
  (plan H seed inputs.length cfg base).actions.map (Action.map (fun p => inputs.getD p default))

/-- The (slot, generation) of the connection each send goes on, in send order. -/
def carriersAux {α : Type} : List (Option Nat) → List (Action α) → List (Nat × Nat)
  | _, [] => []
  | t, .«open» s g :: as => carriersAux (t.set s (some g)) as
  | t, .send _ s :: as => (s, (look t s).getD 0) :: carriersAux t as
  | t, .close s :: as => carriersAux (t.set s none) as

def carriers {α : Type} (poolSize : Nat) (acts : List (Action α)) : List (Nat × Nat) :=
  carriersAux (List.replicate poolSize none) acts

/-! ## 7. The executor interface -/

/-- What remains of a plan. The session drives it with `next` and never looks at the policy. -/
structure PlanState (α : Type) where
  pending : List (Action α)

def PlanState.ofPlan (p : Plan) : PlanState Nat := ⟨p.actions⟩

/-- The next action and the state after it; `none`: the batch is done. -/
def next {α : Type} (st : PlanState α) : Option (Action α × PlanState α) :=
  match st.pending with
  | [] => none
  | a :: rest => some (a, ⟨rest⟩)

/-- The next `open` still to come (slot, generation): the executor may build its circuit (and
connect) ahead, any time after that slot's previous connection was closed. -/
def nextOpen {α : Type} (st : PlanState α) : Option (Nat × Nat) :=
  st.pending.findSome? fun a => match a with
    | .«open» s g => some (s, g)
    | _ => none

/-- Driving `next` to the end yields the plan's actions, in order. -/
def drive {α : Type} : Nat → PlanState α → List (Action α)
  | 0, _ => []
  | fuel + 1, st =>
    match next st with
    | none => []
    | some (a, st') => a :: drive fuel st'

theorem drive_all {α : Type} : ∀ (st : PlanState α), drive st.pending.length st = st.pending
  | ⟨[]⟩ => rfl
  | ⟨a :: rest⟩ => by
    show a :: drive rest.length ⟨rest⟩ = a :: rest
    rw [drive_all ⟨rest⟩]

/-- SOCKS5 credentials of a send connection: generation `gen` of the session, its `reconnect`-th
replacement after a loss (0: the planned one). Fresh per (session, gen, reconnect), so Tor
(`IsolateSOCKSAuth`) never puts two of them on one circuit. The receive socket keeps
`Circuits.labels`' `receive`. -/
def labels (session : String) (gen reconnect : Nat) : String × String :=
  (s!"tls-mpc-{String.ofList (session.toList.take 16)}", s!"rot-{gen}-{reconnect}")

/-! ## 8. The hold window -/

/-- When each arrival's batch is planned (ms). An arrival at `t` joins the open batch if that
batch's deadline `d` has `t ≤ d ≤ t + hold`; otherwise it opens a batch with deadline `t + hold`.
A batch is planned (all its messages shuffled together) at its deadline. -/
def plannedAt (hold : Nat) : Option Nat → List Nat → List Nat
  | _, [] => []
  | some d, t :: ts =>
    if t ≤ d ∧ d ≤ t + hold then d :: plannedAt hold (some d) ts
    else (t + hold) :: plannedAt hold (some (t + hold)) ts
  | none, t :: ts => (t + hold) :: plannedAt hold (some (t + hold)) ts

/-- **A message waits at most `hold`**: planned no earlier than its arrival, no later than
`hold` after it. -/
theorem plannedAt_bounds (hold : Nat) : ∀ (o : Option Nat) (ts : List Nat),
    ∀ p ∈ ts.zip (plannedAt hold o ts), p.1 ≤ p.2 ∧ p.2 ≤ p.1 + hold
  | _, [] => by simp [plannedAt]
  | some d, t :: ts => by
    intro p hp
    simp only [plannedAt] at hp
    split at hp
    · next h =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h
      · exact plannedAt_bounds hold _ ts p hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · exact plannedAt_bounds hold _ ts p hp
  | none, t :: ts => by
    intro p hp
    simp only [plannedAt] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · exact plannedAt_bounds hold _ ts p hp

/-- **With `hold = 0` no message waits**: each is planned at its arrival. -/
theorem plannedAt_zero : ∀ (o : Option Nat) (ts : List Nat), plannedAt 0 o ts = ts
  | _, [] => rfl
  | some d, t :: ts => by
    simp only [plannedAt]
    split
    · next h =>
      have : d = t := by omega
      subst this
      rw [plannedAt_zero]
    · rw [Nat.add_zero, plannedAt_zero]
  | none, t :: ts => by simp only [plannedAt, Nat.add_zero]; rw [plannedAt_zero]

/-! ## 9. T15: the planner never looks at what it sends -/

section Parametric
variable {α β : Type}

theorem place_map (f : α → β) (slot : Nat) (x : α) (c : Conn) (p : Pool) :
    place slot (f x) c p = ((place slot x c p).1.map (Action.map f), (place slot x c p).2) := by
  unfold place
  split <;> rfl

theorem stepMsg_map (cfg : Config) (f : α → β) (x : α) (p : Pool) (s : Stream) :
    stepMsg cfg (f x) p s = ((stepMsg cfg x p s).1.map (Action.map f), (stepMsg cfg x p s).2) := by
  rcases h : look p.slots (below s cfg.poolSize).1 with _ | c
  · simp [stepMsg, h, place_map, Action.map]
  · simp [stepMsg, h, place_map]

theorem schedule_map (cfg : Config) (f : α → β) : ∀ (xs : List α) (p : Pool) (s : Stream),
    schedule cfg (xs.map f) p s = ((schedule cfg xs p s).1.map (Action.map f), (schedule cfg xs p s).2)
  | [], _, _ => rfl
  | x :: xs, p, s => by
    simp only [List.map_cons, schedule, stepMsg_map, schedule_map cfg f xs, List.map_append]

theorem closeFrom_map (f : α → β) : ∀ (i : Nat) (l : List (Option Conn)),
    (closeFrom i l : List (Action α)).map (Action.map f) = closeFrom i l
  | _, [] => rfl
  | i, none :: r => by simp only [closeFrom]; exact closeFrom_map f (i + 1) r
  | i, some _ :: r => by
    simp only [closeFrom, List.map_cons, Action.map]
    rw [closeFrom_map f (i + 1) r]

/-- **Parametricity**: relabelling the messages relabels the actions and changes nothing else. -/
theorem runPool_map (cfg : Config) (f : α → β) (xs : List α) (base : Nat) (s : Stream) :
    runPool cfg (xs.map f) base s = (runPool cfg xs base s).map (Action.map f) := by
  simp only [runPool, schedule_map, List.map_append, closeFrom_map]

theorem range_map_getD (l : List Nat) (n : Nat) (h : l.length = n) :
    (List.range n).map (fun i => l.getD i 0) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i _ h2
  simp [List.getElem?_eq_getElem h2]

/-- The order reads only the shuffle stream (definitional). -/
theorem plan_order (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) :
    (plan H seed n cfg base).order = shuffle (Stream.start H seed shuffleTag) n := rfl

/-- The skeleton reads only the pool stream (definitional). -/
theorem skeleton_def (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) :
    skeleton H seed n cfg base = runPool cfg (List.range n) base (Stream.start H seed poolTag) := rfl

/-- **The plan is the skeleton relabelled by the shuffle.** -/
theorem plan_actions (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) :
    (plan H seed n cfg base).actions =
      (skeleton H seed n cfg base).map (Action.map (fun i => (plan H seed n cfg base).order.getD i 0)) := by
  have he := range_map_getD (shuffle (Stream.start H seed shuffleTag) n) n (shuffle_length _ _)
  simp only [plan, skeleton]
  rw [← runPool_map, he]

theorem compose_eq (H : Bytes → Bytes) (seed : Bytes) (cfg : Config) (base : Nat) (inputs : List β) (d : β) :
    compose H seed cfg base inputs d = (skeleton H seed inputs.length cfg base).map
      (Action.map (fun i => inputs.getD ((plan H seed inputs.length cfg base).order.getD i 0) d)) := by
  rw [compose, plan_actions, List.map_map]
  congr 1
  funext a
  cases a <;> rfl

/-- **T15 (the actions)**: for two input lists of the same length (any contacts, texts, states),
the composed sender performs the same actions once the payloads are erased: the same opens (slot,
generation), the same closes, the same sends on the same slots, in the same order. -/
theorem t15_erase (H : Bytes → Bytes) (seed : Bytes) (cfg : Config) (base : Nat)
    (xs ys : List β) (dx dy : β) (h : xs.length = ys.length) :
    (compose H seed cfg base xs dx).map Action.erase = (compose H seed cfg base ys dy).map Action.erase := by
  simp only [compose, List.map_map]
  have e : ∀ (g : Nat → β), (Action.erase ∘ Action.map g) = Action.erase :=
    fun g => funext (Action.erase_map g)
  rw [e, e, h]

theorem carriersAux_map (f : α → β) : ∀ (t : List (Option Nat)) (acts : List (Action α)),
    carriersAux t (acts.map (Action.map f)) = carriersAux t acts
  | _, [] => rfl
  | t, .«open» s g :: as => by
    simp only [List.map_cons, Action.map, carriersAux]
    exact carriersAux_map f _ as
  | t, .send x s :: as => by
    simp only [List.map_cons, Action.map, carriersAux]
    rw [carriersAux_map f _ as]
  | t, .close s :: as => by
    simp only [List.map_cons, Action.map, carriersAux]
    exact carriersAux_map f _ as

/-- **T15 (the connections)**: the (slot, generation) carrying the i-th sent message is the
skeleton's, a function of the pool stream, `n`, the configuration and `base`; whatever the inputs. -/
theorem t15_carriers (H : Bytes → Bytes) (seed : Bytes) (cfg : Config) (base : Nat) (xs : List β) (d : β) :
    carriers cfg.poolSize (compose H seed cfg base xs d) =
      carriers cfg.poolSize (skeleton H seed xs.length cfg base) := by
  rw [compose_eq]
  exact carriersAux_map _ _ _

theorem sendsOf_map (f : α → β) (acts : List (Action α)) :
    sendsOf (acts.map (Action.map f)) = (sendsOf acts).map f := by
  simp only [sendsOf, List.filterMap_map, List.map_filterMap]
  congr 1
  funext a
  exact Action.sendOf_map f a

theorem sends_place (slot : Nat) (x : α) (c : Conn) (p : Pool) : sendsOf (place slot x c p).1 = [x] := by
  unfold place
  split <;> rfl

theorem sends_stepMsg (cfg : Config) (x : α) (p : Pool) (s : Stream) : sendsOf (stepMsg cfg x p s).1 = [x] := by
  rcases h : look p.slots (below s cfg.poolSize).1 with _ | c
  · simp only [stepMsg, h]
    exact sends_place _ _ _ _
  · simp only [stepMsg, h]
    exact sends_place _ _ _ _

theorem sends_schedule (cfg : Config) : ∀ (xs : List α) (p : Pool) (s : Stream),
    sendsOf (schedule cfg xs p s).1 = xs
  | [], _, _ => rfl
  | x :: xs, p, s => by
    simp only [schedule, sendsOf, List.filterMap_append] at *
    rw [show List.filterMap Action.sendOf (stepMsg cfg x p s).1 = [x] from sends_stepMsg cfg x p s]
    rw [show List.filterMap Action.sendOf (schedule cfg xs _ _).1 = xs from sends_schedule cfg xs _ _]
    rfl

theorem sends_closeFrom : ∀ (i : Nat) (l : List (Option Conn)), sendsOf (closeFrom i l : List (Action α)) = []
  | _, [] => rfl
  | i, none :: r => by simp only [closeFrom]; exact sends_closeFrom (i + 1) r
  | i, some _ :: r => by simp only [closeFrom]; exact sends_closeFrom (i + 1) r

theorem sends_runPool (cfg : Config) (xs : List α) (base : Nat) (s : Stream) : sendsOf (runPool cfg xs base s) = xs := by
  have h1 := sends_schedule cfg xs (Pool.empty cfg.poolSize base) s
  have h2 := sends_closeFrom (α := α) 0 (schedule cfg xs (Pool.empty cfg.poolSize base) s).2.1.slots
  simp only [sendsOf] at h1 h2
  simp only [runPool, sendsOf, List.filterMap_append, h1, h2, List.append_nil]

/-- **T15 (the messages)**: the i-th message sent is input `order[i]`. -/
theorem t15_sends (H : Bytes → Bytes) (seed : Bytes) (cfg : Config) (base : Nat) (xs : List β) (d : β) :
    sendsOf (compose H seed cfg base xs d) = (plan H seed xs.length cfg base).order.map (fun p => xs.getD p d) := by
  rw [compose, sendsOf_map]
  simp only [plan, sends_runPool]

/-- **Every position is sent exactly once** (the sends are a permutation of `0 … n-1`). -/
theorem plan_sends_perm (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) :
    List.Perm (sendsOf (plan H seed n cfg base).actions) (List.range n) := by
  simp only [plan, sends_runPool]
  exact shuffle_perm _ _

end Parametric

/-! ## 10. The executor model (`Mon`) and well-formedness -/

/-- The executor's view of the pool: per slot, the open connection's (generation, messages
carried); the next generation; the counts of the connections closed so far; the sends. -/
structure Mon where
  slots : List (Option (Nat × Nat))
  next : Nat
  closed : List Nat
  sends : Nat
  deriving Repr

namespace Mon

def init (poolSize base : Nat) : Mon := ⟨List.replicate poolSize none, base, [], 0⟩

/-- The rules. `open s g`: slot `s` exists and is closed, `g` is the next generation. `send _ s`:
slot `s` is open and its connection carried fewer than `maxLen` messages. `close s`: slot `s` is
open and its connection carried at least one message. Anything else is refused (`none`). -/
def step {α : Type} (maxLen : Nat) (m : Mon) : Action α → Option Mon
  | .«open» s g =>
    if s < m.slots.length ∧ look m.slots s = none ∧ g = m.next then
      some { m with slots := m.slots.set s (some (g, 0)), next := m.next + 1 }
    else none
  | .send _ s =>
    match look m.slots s with
    | some (g, c) =>
      if c < maxLen then some { m with slots := m.slots.set s (some (g, c + 1)), sends := m.sends + 1 }
      else none
    | none => none
  | .close s =>
    match look m.slots s with
    | some (_, c) =>
      if 1 ≤ c then some { m with slots := m.slots.set s none, closed := m.closed ++ [c] } else none
    | none => none

def run {α : Type} (maxLen : Nat) : Mon → List (Action α) → Option Mon
  | m, [] => some m
  | m, a :: as => (m.step maxLen a).bind (fun m' => run maxLen m' as)

/-- No connection open. -/
def idle (m : Mon) : Prop := ∀ e ∈ m.slots, e = none

end Mon

/-- The executable check (property tests): the monitor accepts and ends with every slot closed. -/
def accepts {α : Type} (cfg : Config) (base : Nat) (acts : List (Action α)) : Bool :=
  match Mon.run cfg.maxLen (Mon.init cfg.poolSize base) acts with
  | some m => m.slots.all (·.isNone)
  | none => false

def carriedOf : Option (Nat × Nat) → Nat
  | some (_, c) => c
  | none => 0

def isOpen : Option (Nat × Nat) → Nat
  | some _ => 1
  | none => 0

def openSum (l : List (Option (Nat × Nat))) : Nat := (l.map carriedOf).sum

/-- Connections open. -/
def openCount (l : List (Option (Nat × Nat))) : Nat := (l.map isOpen).sum

section Look
variable {β γ : Type}

theorem look_map (f : β → γ) (l : List (Option β)) (i : Nat) :
    look (l.map (Option.map f)) i = (look l i).map f := by
  simp only [look, List.getElem?_map]
  cases l[i]? with
  | none => rfl
  | some e => cases e <;> rfl

theorem look_set_self (l : List (Option β)) (i : Nat) (x : Option β) (h : i < l.length) :
    look (l.set i x) i = x := by
  simp [look, List.getElem?_set_self h]

theorem look_some {l : List (Option β)} {i : Nat} {v : β} (h : look l i = some v) :
    ∃ hi : i < l.length, l[i] = some v := by
  unfold look at h
  cases hl : l[i]? with
  | none => simp [hl] at h
  | some e =>
    simp only [hl, Option.getD_some] at h
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hl
    exact ⟨hi, he.trans h⟩

theorem look_none {l : List (Option β)} {i : Nat} (hi : i < l.length) (h : look l i = none) : l[i] = none := by
  simpa [look, List.getElem?_eq_getElem hi] using h

theorem look_mem {l : List (Option β)} {i : Nat} {v : β} (h : look l i = some v) : some v ∈ l := by
  obtain ⟨hi, he⟩ := look_some h
  exact he ▸ List.getElem_mem hi

theorem sum_set (f : γ → Nat) : ∀ (l : List γ) (i : Nat) (hi : i < l.length) (x : γ),
    ((l.set i x).map f).sum + f l[i] = (l.map f).sum + f x
  | [], _, hi, _ => by simp at hi
  | y :: ys, 0, _, x => by simp; omega
  | y :: ys, i + 1, hi, x => by
    have := sum_set f ys i (by simpa using hi) x
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    omega

end Look

/-- What every reachable monitor state satisfies. -/
structure Inv (maxLen base : Nat) (m : Mon) : Prop where
  sum : m.closed.sum + openSum m.slots = m.sends
  closedBounds : ∀ c ∈ m.closed, 1 ≤ c ∧ c ≤ maxLen
  openBounds : ∀ g c, some (g, c) ∈ m.slots → c ≤ maxLen
  count : m.closed.length + openCount m.slots + base = m.next

namespace Mon

theorem run_append {α : Type} (maxLen : Nat) : ∀ (m : Mon) (a b : List (Action α)),
    run maxLen m (a ++ b) = (run maxLen m a).bind (fun m' => run maxLen m' b)
  | _, [], _ => rfl
  | m, x :: a, b => by
    simp only [List.cons_append, run, Option.bind_assoc]
    congr 1
    funext m'
    exact run_append maxLen m' a b

theorem step_length {α : Type} (maxLen : Nat) (m m' : Mon) (a : Action α) (h : m.step maxLen a = some m') :
    m'.slots.length = m.slots.length := by
  cases a with
  | «open» s g =>
    simp only [step] at h
    split at h
    · cases h; simp
    · cases h
  | send x s =>
    simp only [step] at h
    split at h
    · split at h
      · cases h; simp
      · cases h
    · cases h
  | close s =>
    simp only [step] at h
    split at h
    · split at h
      · cases h; simp
      · cases h
    · cases h

theorem run_length {α : Type} (maxLen : Nat) : ∀ (m m' : Mon) (acts : List (Action α)),
    run maxLen m acts = some m' → m'.slots.length = m.slots.length
  | m, m', [], h => by cases h; rfl
  | m, m', a :: as, h => by
    simp only [run] at h
    cases hs : m.step maxLen a with
    | none => rw [hs] at h; simp at h
    | some m1 =>
      rw [hs] at h
      rw [run_length maxLen m1 m' as h, step_length maxLen m m1 a hs]

theorem step_inv {α : Type} (maxLen base : Nat) (m m' : Mon) (a : Action α) (hi : Inv maxLen base m)
    (h : m.step maxLen a = some m') : Inv maxLen base m' := by
  cases a with
  | «open» s g =>
    simp only [step] at h
    split at h
    · next hc =>
      cases h
      obtain ⟨hs, hl, hg⟩ := hc
      have h0 := look_none hs hl
      have e1 := sum_set carriedOf m.slots s hs (some (g, 0))
      have e2 := sum_set isOpen m.slots s hs (some (g, 0))
      rw [h0] at e1 e2
      simp only [carriedOf, isOpen] at e1 e2
      have i1 := hi.sum
      have i2 := hi.count
      simp only [openSum, openCount] at i1 i2
      refine ⟨?_, hi.closedBounds, ?_, ?_⟩
      · simp only [openSum]; omega
      · intro g' c' hm
        rcases List.mem_or_eq_of_mem_set hm with hm | hm
        · exact hi.openBounds g' c' hm
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm; omega
      · simp only [openCount]; omega
    · cases h
  | send x s =>
    simp only [step] at h
    split at h
    · next g c hl =>
      split at h
      · next hc =>
        cases h
        obtain ⟨hs, he⟩ := look_some hl
        have e1 := sum_set carriedOf m.slots s hs (some (g, c + 1))
        have e2 := sum_set isOpen m.slots s hs (some (g, c + 1))
        rw [he] at e1 e2
        simp only [carriedOf, isOpen] at e1 e2
        have i1 := hi.sum
        have i2 := hi.count
        simp only [openSum, openCount] at i1 i2
        refine ⟨?_, hi.closedBounds, ?_, ?_⟩
        · simp only [openSum]; omega
        · intro g' c' hm
          rcases List.mem_or_eq_of_mem_set hm with hm | hm
          · exact hi.openBounds g' c' hm
          · simp only [Option.some.injEq, Prod.mk.injEq] at hm; omega
        · simp only [openCount]; omega
      · cases h
    · cases h
  | close s =>
    simp only [step] at h
    split at h
    · next g c hl =>
      split at h
      · next hc =>
        cases h
        obtain ⟨hs, he⟩ := look_some hl
        have hb := hi.openBounds g c (look_mem hl)
        have e1 := sum_set carriedOf m.slots s hs none
        have e2 := sum_set isOpen m.slots s hs none
        rw [he] at e1 e2
        simp only [carriedOf, isOpen] at e1 e2
        have i1 := hi.sum
        have i2 := hi.count
        simp only [openSum, openCount] at i1 i2
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [openSum, List.sum_append, List.sum_cons, List.sum_nil]; omega
        · intro c' hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hi.closedBounds c' hm
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
        · intro g' c' hm
          rcases List.mem_or_eq_of_mem_set hm with hm | hm
          · exact hi.openBounds g' c' hm
          · simp at hm
        · simp only [openCount, List.length_append, List.length_cons, List.length_nil]; omega
      · cases h
    · cases h

theorem run_inv {α : Type} (maxLen base : Nat) : ∀ (m m' : Mon) (acts : List (Action α)),
    Inv maxLen base m → run maxLen m acts = some m' → Inv maxLen base m'
  | m, m', [], hi, h => by cases h; exact hi
  | m, m', a :: as, hi, h => by
    simp only [run] at h
    cases hs : m.step maxLen a with
    | none => rw [hs] at h; simp at h
    | some m1 =>
      rw [hs] at h
      exact run_inv maxLen base m1 m' as (step_inv maxLen base m m1 a hi hs) h

theorem init_inv (maxLen poolSize base : Nat) : Inv maxLen base (init poolSize base) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [init, openSum, openCount, carriedOf, isOpen, List.map_replicate]

theorem idle_zero (l : List (Option (Nat × Nat))) (h : ∀ e ∈ l, e = none) : openSum l = 0 ∧ openCount l = 0 := by
  induction l with
  | nil => simp [openSum, openCount]
  | cons e l ih =>
    have he := h e (by simp)
    subst he
    have := ih (fun e' h' => h e' (by simp [h']))
    simp only [openSum, openCount, List.map_cons, List.sum_cons, carriedOf, isOpen] at this ⊢
    omega

/-- In an accepted trace that ends idle: the closed connections' counts sum to the sends, each is
in `[1, maxLen]`, and there is one per generation handed out. -/
theorem accepted_counts {α : Type} (maxLen poolSize base : Nat) (acts : List (Action α)) (m : Mon)
    (h : run maxLen (init poolSize base) acts = some m) (hid : m.idle) :
    m.closed.sum = m.sends ∧ (∀ c ∈ m.closed, 1 ≤ c ∧ c ≤ maxLen) ∧ m.closed.length + base = m.next := by
  have hi := run_inv maxLen base _ m acts (init_inv maxLen poolSize base) h
  obtain ⟨z1, z2⟩ := idle_zero m.slots hid
  exact ⟨by have := hi.sum; omega, hi.closedBounds, by have := hi.count; omega⟩

theorem step_open {α : Type} (maxLen : Nat) (m m' : Mon) (s g : Nat)
    (h : m.step maxLen (Action.«open» s g : Action α) = some m') : g = m.next ∧ m'.next = m.next + 1 := by
  simp only [step] at h
  split at h
  · next hc => cases h; exact ⟨hc.2.2, rfl⟩
  · cases h

theorem step_send {α : Type} (maxLen : Nat) (m m' : Mon) (x : α) (s : Nat)
    (h : m.step maxLen (Action.send x s) = some m') : m'.next = m.next ∧ m'.sends = m.sends + 1 := by
  simp only [step] at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem step_close {α : Type} (maxLen : Nat) (m m' : Mon) (s : Nat)
    (h : m.step maxLen (Action.close s : Action α) = some m') : m'.next = m.next := by
  simp only [step] at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- **Generations**: the opens of an accepted trace hand out `m.next, m.next + 1, …` in order. -/
theorem run_opens {α : Type} (maxLen : Nat) : ∀ (m m' : Mon) (acts : List (Action α)),
    run maxLen m acts = some m' →
      opensOf acts = List.range' m.next (opensOf acts).length ∧ m'.next = m.next + (opensOf acts).length
  | m, m', [], h => by cases h; simp [opensOf]
  | m, m', a :: as, h => by
    simp only [run] at h
    cases hs : m.step maxLen a with
    | none => rw [hs] at h; simp at h
    | some m1 =>
      rw [hs] at h
      obtain ⟨ih1, ih2⟩ := run_opens maxLen m1 m' as h
      cases a with
      | «open» s g =>
        obtain ⟨hg, hn⟩ := step_open maxLen m m1 s g hs
        have e : opensOf (Action.«open» s g :: as) = g :: opensOf as := rfl
        rw [e, List.length_cons]
        refine ⟨?_, by omega⟩
        show g :: opensOf as = m.next :: List.range' (m.next + 1) (opensOf as).length
        rw [hg, ← hn, ← ih1]
      | send x s =>
        have hn := (step_send maxLen m m1 x s hs).1
        have e : opensOf (Action.send x s :: as) = opensOf as := rfl
        rw [e]
        rw [hn] at ih1 ih2
        exact ⟨ih1, ih2⟩
      | close s =>
        have hn := step_close maxLen m m1 s hs
        have e : opensOf (Action.close s :: as) = opensOf as := rfl
        rw [e]
        rw [hn] at ih1 ih2
        exact ⟨ih1, ih2⟩

/-- Every prefix of an accepted trace is accepted, with as many slots. -/
theorem run_prefix {α : Type} (maxLen : Nat) (m m' : Mon) (acts : List (Action α))
    (h : run maxLen m acts = some m') (j : Nat) :
    ∃ mj, run maxLen m (acts.take j) = some mj ∧ mj.slots.length = m.slots.length := by
  rw [← List.take_append_drop j acts, run_append] at h
  cases hj : run maxLen m (acts.take j) with
  | none => rw [hj] at h; simp at h
  | some mj => exact ⟨mj, rfl, run_length maxLen m mj _ hj⟩

end Mon

theorem openCount_le (l : List (Option (Nat × Nat))) : openCount l ≤ l.length := by
  induction l with
  | nil => simp [openCount]
  | cons e l ih =>
    simp only [openCount, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    cases e <;> simp only [isOpen] <;> omega

theorem bounded_sum (M : Nat) : ∀ (l : List Nat), (∀ c ∈ l, 1 ≤ c ∧ c ≤ M) →
    l.length ≤ l.sum ∧ l.sum ≤ l.length * M
  | [], _ => by simp
  | c :: l, h => by
    have hc := h c (by simp)
    have ih := bounded_sum M l (fun c' h' => h c' (by simp [h']))
    simp only [List.length_cons, List.sum_cons, Nat.succ_mul]
    omega

/-! ### The planner against the monitor -/

/-- The planner's pool and the monitor agree, and the pool's connections are within bounds. -/
structure Rel (cfg : Config) (p : Pool) (m : Mon) : Prop where
  slots : m.slots = p.slots.map (Option.map Conn.view)
  next : m.next = p.next
  size : p.slots.length = cfg.poolSize
  conns : ∀ c, some c ∈ p.slots → 1 ≤ c.left ∧ 1 ≤ c.carried ∧ c.carried + c.left ≤ cfg.maxLen

theorem place_sim {α : Type} (cfg : Config) (slot : Nat) (x : α) (c : Conn) (p : Pool) (m : Mon)
    (hs : slot < p.slots.length) (hsize : p.slots.length = cfg.poolSize)
    (hm : m.slots = (p.slots.set slot (some c)).map (Option.map Conn.view)) (hn : m.next = p.next)
    (hc1 : 1 ≤ c.left) (hc2 : c.carried + c.left ≤ cfg.maxLen)
    (hp : ∀ c', some c' ∈ p.slots → 1 ≤ c'.left ∧ 1 ≤ c'.carried ∧ c'.carried + c'.left ≤ cfg.maxLen) :
    ∃ m', Mon.run cfg.maxLen m (place slot x c p).1 = some m' ∧ Rel cfg (place slot x c p).2 m' ∧
      m'.sends = m.sends + 1 := by
  have hlen : slot < m.slots.length := by rw [hm]; simpa using hs
  have hl : look m.slots slot = some (c.gen, c.carried) := by
    rw [hm, look_map, look_set_self _ _ _ hs]; rfl
  have hlt : c.carried < cfg.maxLen := by omega
  unfold place
  split
  · let m2 : Mon := { m with slots := (m.slots.set slot (some (c.gen, c.carried + 1))).set slot none, sends := m.sends + 1, closed := m.closed ++ [c.carried + 1] }
    refine ⟨m2, ?_, ?_, rfl⟩
    · simp [m2, Mon.run, Mon.step, hl, hlt, look_set_self _ _ _ hlen]
    · refine ⟨?_, hn, by simpa using hsize, ?_⟩
      · simp only [m2, List.set_set, hm, List.map_set, Option.map_none]
      · intro c' hc'
        rcases List.mem_or_eq_of_mem_set hc' with h | h
        · exact hp c' h
        · simp at h
  · let m1 : Mon := { m with slots := m.slots.set slot (some (c.gen, c.carried + 1)), sends := m.sends + 1 }
    refine ⟨m1, ?_, ?_, rfl⟩
    · simp [m1, Mon.run, Mon.step, hl, hlt]
    · refine ⟨?_, hn, by simpa using hsize, ?_⟩
      · simp only [m1, List.set_set, hm, List.map_set, Option.map_some]
        rfl
      · intro c' hc'
        rcases List.mem_or_eq_of_mem_set hc' with h | h
        · exact hp c' h
        · simp only [Option.some.injEq] at h
          subst h
          simp only
          omega

theorem stepMsg_sim {α : Type} (cfg : Config) (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen)
    (x : α) (p : Pool) (s : Stream) (m : Mon) (hr : Rel cfg p m) :
    ∃ m', Mon.run cfg.maxLen m (stepMsg cfg x p s).1 = some m' ∧ Rel cfg (stepMsg cfg x p s).2.1 m' ∧
      m'.sends = m.sends + 1 := by
  have hs : (below s cfg.poolSize).1 < p.slots.length := by rw [hr.size]; exact below_lt s _ hpool
  rcases hl : look p.slots (below s cfg.poolSize).1 with _ | c
  · have hb := drawLength_bounds cfg (below s cfg.poolSize).2 hmax
    have h1 : (below s cfg.poolSize).1 < m.slots.length := by rw [hr.slots]; simpa using hs
    have h2 : look m.slots (below s cfg.poolSize).1 = none := by rw [hr.slots, look_map, hl]; rfl
    have hstep : m.step cfg.maxLen (Action.«open» (below s cfg.poolSize).1 p.next : Action α) =
        some { m with slots := m.slots.set (below s cfg.poolSize).1 (some (p.next, 0)), next := m.next + 1 } := by
      simp [Mon.step, h1, h2, hr.next]
    obtain ⟨m', e1, e2, e3⟩ := place_sim cfg (below s cfg.poolSize).1 x
      ⟨p.next, (drawLength cfg (below s cfg.poolSize).2).1, 0⟩ { p with next := p.next + 1 }
      { m with slots := m.slots.set (below s cfg.poolSize).1 (some (p.next, 0)), next := m.next + 1 }
      hs hr.size (by simp only [hr.slots, List.map_set]; rfl) (by simp [hr.next])
      hb.1 (by simpa using hb.2) hr.conns
    refine ⟨m', ?_, ?_, ?_⟩
    · simp only [stepMsg, hl, Mon.run, hstep, Option.bind_some]
      exact e1
    · simp only [stepMsg, hl]
      exact e2
    · rw [e3]
  · obtain ⟨hi, hc⟩ := look_some hl
    have hcp := hr.conns c (look_mem hl)
    have hset : p.slots.set (below s cfg.poolSize).1 (some c) = p.slots := by
      rw [← hc]; exact List.set_getElem_self hi
    obtain ⟨m', e1, e2, e3⟩ := place_sim cfg (below s cfg.poolSize).1 x c p m hs hr.size
      (by rw [hset, hr.slots]) hr.next hcp.1 hcp.2.2 hr.conns
    refine ⟨m', ?_, ?_, e3⟩
    · simp only [stepMsg, hl]
      exact e1
    · simp only [stepMsg, hl]
      exact e2

theorem schedule_sim {α : Type} (cfg : Config) (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    ∀ (xs : List α) (p : Pool) (s : Stream) (m : Mon), Rel cfg p m →
      ∃ m', Mon.run cfg.maxLen m (schedule cfg xs p s).1 = some m' ∧ Rel cfg (schedule cfg xs p s).2.1 m' ∧
        m'.sends = m.sends + xs.length
  | [], _, _, m, hr => ⟨m, rfl, hr, rfl⟩
  | x :: xs, p, s, m, hr => by
    obtain ⟨m1, h1, r1, s1⟩ := stepMsg_sim cfg hpool hmax x p s m hr
    obtain ⟨m2, h2, r2, s2⟩ := schedule_sim cfg hpool hmax xs _ _ m1 r1
    refine ⟨m2, ?_, r2, by simp only [List.length_cons]; omega⟩
    simp only [schedule, Mon.run_append, h1, Option.bind_some]
    exact h2

theorem closeFrom_sim {α : Type} (maxLen : Nat) : ∀ (rest : List (Option Conn)) (pre : List (Option (Nat × Nat)))
    (m : Mon), m.slots = pre ++ rest.map (Option.map Conn.view) → (∀ e ∈ pre, e = none) →
    (∀ c, some c ∈ rest → 1 ≤ c.carried) →
    ∃ m', Mon.run maxLen m (closeFrom pre.length rest : List (Action α)) = some m' ∧ m'.idle ∧ m'.sends = m.sends
  | [], pre, m, hm, hpre, _ => by
    refine ⟨m, rfl, ?_, rfl⟩
    intro e he
    rw [hm, List.map_nil, List.append_nil] at he
    exact hpre e he
  | none :: r, pre, m, hm, hpre, hc => by
    have := closeFrom_sim (α := α) maxLen r (pre ++ [none]) m (by rw [hm]; simp)
      (by intro e he; rcases List.mem_append.mp he with h | h; exact hpre e h; simpa using h)
      (fun c h => hc c (by simp [h]))
    simpa [closeFrom] using this
  | some c :: r, pre, m, hm, hpre, hc => by
    have hc1 := hc c (by simp)
    have hl : look m.slots pre.length = some (c.gen, c.carried) := by
      simp [look, hm, Conn.view]
    let m1 : Mon := { m with slots := m.slots.set pre.length none, closed := m.closed ++ [c.carried] }
    have hstep : m.step maxLen (Action.close pre.length : Action α) = some m1 := by
      simp [Mon.step, hl, hc1, m1]
    have hm1 : m1.slots = (pre ++ [none]) ++ r.map (Option.map Conn.view) := by
      simp [m1, hm, List.set_append_right]
    obtain ⟨m', e1, e2, e3⟩ := closeFrom_sim (α := α) maxLen r (pre ++ [none]) m1 hm1
      (by intro e he; rcases List.mem_append.mp he with h | h; exact hpre e h; simpa using h)
      (fun c' h => hc c' (by simp [h]))
    refine ⟨m', ?_, e2, e3⟩
    simp only [closeFrom, Mon.run, hstep, Option.bind_some]
    simpa using e1

/-- **The monitor accepts the planner's actions**, ending idle, with one send per message. -/
theorem runPool_accepted {α : Type} (cfg : Config) (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen)
    (xs : List α) (base : Nat) (s : Stream) :
    ∃ m, Mon.run cfg.maxLen (Mon.init cfg.poolSize base) (runPool cfg xs base s) = some m ∧ m.idle ∧
      m.sends = xs.length := by
  have hr : Rel cfg (Pool.empty cfg.poolSize base) (Mon.init cfg.poolSize base) :=
    ⟨by simp [Mon.init, Pool.empty, List.map_replicate], rfl, by simp [Pool.empty],
      by intro c h; simp [Pool.empty] at h⟩
  obtain ⟨m1, h1, r1, s1⟩ := schedule_sim cfg hpool hmax xs _ s _ hr
  obtain ⟨m2, h2, i2, s2⟩ := closeFrom_sim (α := α) cfg.maxLen
    (schedule cfg xs (Pool.empty cfg.poolSize base) s).2.1.slots [] m1 (by rw [r1.slots]; rfl)
    (by simp) (fun c h => (r1.conns c h).2.1)
  refine ⟨m2, ?_, i2, by rw [s2, s1]; simp [Mon.init]⟩
  simp only [runPool, Mon.run_append, h1, Option.bind_some]
  exact h2

/-! ### Well-formedness of the plan -/

section Plan
variable (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat)

/-- **The executor model accepts the plan**: every open is on a closed slot with the next
generation, every send on an open slot below the connection's maximum, every close on an open
slot whose connection carried a message, and at the end no connection is open; one send per
message. -/
theorem plan_accepted (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    ∃ m, Mon.run cfg.maxLen (Mon.init cfg.poolSize base) (plan H seed n cfg base).actions = some m ∧
      m.idle ∧ m.sends = n := by
  obtain ⟨m, h1, h2, h3⟩ := runPool_accepted cfg hpool hmax (shuffle (Stream.start H seed shuffleTag) n)
    base (Stream.start H seed poolTag)
  exact ⟨m, h1, h2, by rw [h3, shuffle_length]⟩

/-- The executable form holds (`accepts`). -/
theorem plan_accepts (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    accepts cfg base (plan H seed n cfg base).actions = true := by
  obtain ⟨m, h1, h2, _⟩ := plan_accepted H seed n cfg base hpool hmax
  simp only [accepts, h1, List.all_eq_true]
  intro e he
  simp [h2 e he]

/-- **No generation is reused**: the plan opens generations `base, base + 1, …`, in order. -/
theorem plan_generations (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    opensOf (plan H seed n cfg base).actions =
      List.range' base (opensOf (plan H seed n cfg base).actions).length ∧
    (opensOf (plan H seed n cfg base).actions).Nodup := by
  obtain ⟨m, h1, _, _⟩ := plan_accepted H seed n cfg base hpool hmax
  have := (Mon.run_opens cfg.maxLen _ m _ h1).1
  exact ⟨this, by rw [this]; exact List.nodup_range'⟩

/-- **At most `poolSize` connections are open at once**: after every prefix of the actions. -/
theorem plan_pool_bound (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) (j : Nat) :
    ∃ mj, Mon.run cfg.maxLen (Mon.init cfg.poolSize base) ((plan H seed n cfg base).actions.take j) = some mj ∧
      openCount mj.slots ≤ cfg.poolSize := by
  obtain ⟨m, h1, _, _⟩ := plan_accepted H seed n cfg base hpool hmax
  obtain ⟨mj, e1, e2⟩ := Mon.run_prefix cfg.maxLen _ m _ h1 j
  refine ⟨mj, e1, ?_⟩
  have := openCount_le mj.slots
  simp only [Mon.init, List.length_replicate] at e2
  omega

/-- **Every connection carries between 1 and `maxLen` messages**; their counts (in the order the
connections close) sum to `n`; there is one per generation opened. -/
theorem plan_counts (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    ∃ m, Mon.run cfg.maxLen (Mon.init cfg.poolSize base) (plan H seed n cfg base).actions = some m ∧
      m.idle ∧ m.closed.sum = n ∧ (∀ c ∈ m.closed, 1 ≤ c ∧ c ≤ cfg.maxLen) ∧
      m.closed.length = (opensOf (plan H seed n cfg base).actions).length := by
  obtain ⟨m, h1, h2, h3⟩ := plan_accepted H seed n cfg base hpool hmax
  obtain ⟨c1, c2, c3⟩ := Mon.accepted_counts cfg.maxLen cfg.poolSize base _ m h1 h2
  have := (Mon.run_opens cfg.maxLen _ m _ h1).2
  simp only [Mon.init] at this
  exact ⟨m, h1, h2, by rw [c1, h3], c2, by omega⟩

/-- **The number of connections** `k` of a batch of `n` messages: `k ≤ n ≤ k·maxLen` (so
`⌈n/maxLen⌉ ≤ k ≤ n`). -/
theorem plan_connection_bounds (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    (opensOf (plan H seed n cfg base).actions).length ≤ n ∧
      n ≤ (opensOf (plan H seed n cfg base).actions).length * cfg.maxLen := by
  obtain ⟨m, _, _, hs, hb, hk⟩ := plan_counts H seed n cfg base hpool hmax
  have := bounded_sum cfg.maxLen m.closed hb
  rw [hk, hs] at this
  exact this

end Plan

end Rotation
