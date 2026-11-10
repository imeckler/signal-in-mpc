import TlsMpc.Ghash

/-!
GCM tags from XOR shares of the GHASH key powers (design:
`handshake_backend/EmpHybridWork/GHASH_SHARES.md`).

Each party holds one XOR share of every key power. On PUBLIC blocks each party
evaluates its half of the tag polynomial locally; the engines XOR the two
halves with the per-record pad `E = AES_K(J0)` and either open the tag (seal)
or compare it with the received tag (open).

Proved here, for any multiplication that is additive in the key argument:

* correctness of the split: the two local halves XOR to the polynomial
  evaluated at the real powers (`localTag_shares`);
* a share reveals nothing about the key it masks (`share_hides`,
  `share_views_equal`);
* a party that supplies a wrong half while sealing changes the opened tag by
  exactly the difference it chose (`seal_deviation`), so the opened value is a
  function of the public honest tag and its own choice;
* for ANY blocks, received tag, and halves (in particular any forged record and
  any value a deviating party supplies), exactly one pad value makes the check
  accept (`accept_unique_pad`); a genuine record is rejected under any nonzero
  deviation (`genuine_rejected`).

These security statements use no property of the multiplication at all. The
pad being a fresh pseudorandom value unknown to the parties (AES as a PRF,
unique nonces) is a cryptographic assumption outside Lean; with it,
`accept_unique_pad` bounds a forgery attempt by 2^-128.

Proved for the repository's GHASH multiplication: it is additive in the key
(`multiply_key_additive`), which is what the split needs.

Assumed, as explicit hypotheses where used (`Laws`): commutativity and
associativity of GF(2^128) multiplication. Commutativity justifies squaring
shares locally (`square_additive`). Identifying the polynomial in the key
powers with the standard's Horner form also needs both laws; that identity is
NOT yet proved here, so the statement "the combined tag is the GCM tag" is
established by interoperation tests, not by a theorem. No security statement
uses the laws.
-/
namespace TlsMpc.GhashShares

abbrev W := BitVec 128

/-- A party's local half: `⊕ blockᵢ · shareᵢ`. -/
def localTag (mul : W → W → W) : List W → List W → W
  | block :: blocks, share :: shares => mul block share ^^^ localTag mul blocks shares
  | _, _ => 0

theorem xor_exchange (p q r s : W) : p ^^^ q ^^^ (r ^^^ s) = p ^^^ r ^^^ (q ^^^ s) := by
  ext i
  simp only [BitVec.getElem_xor]
  cases p[i] <;> cases q[i] <;> cases r[i] <;> cases s[i] <;> rfl

/-- `mul` is additive in its second (key) argument. -/
def KeyAdditive (mul : W → W → W) : Prop := ∀ x h k, mul x (h ^^^ k) = mul x h ^^^ mul x k

theorem localTag_shares (mul : W → W → W) (additive : KeyAdditive mul)
    (blocks first second : List W) (same : first.length = second.length) :
    localTag mul blocks first ^^^ localTag mul blocks second =
      localTag mul blocks (List.zipWith (· ^^^ ·) first second) := by
  induction blocks generalizing first second with
  | nil => cases first <;> cases second <;> simp [localTag]
  | cons block rest ih =>
      cases first with
      | nil => cases second <;> simp [localTag] at same ⊢
      | cons a first =>
          cases second with
          | nil => simp at same
          | cons b second =>
              have tail := ih first second (by simpa using same)
              simp only [localTag, List.zipWith_cons_cons, ← tail]
              rw [additive block a b]
              exact xor_exchange _ _ _ _

/-! ### Shares hide the key -/

/-- Whatever masked value a party sees, every candidate key is consistent with
it through exactly one mask. -/
theorem share_hides (key seen : W) : ∃ mask : W, key ^^^ mask = seen ∧ ∀ other, key ^^^ other = seen → other = mask := by
  refine ⟨key ^^^ seen, ?_, ?_⟩
  · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · intro other h
    rw [← h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The views under two different keys are related by a bijection on masks:
shifting the mask by the difference of the keys gives the same view. -/
theorem share_views_equal (key other mask : W) : key ^^^ mask = other ^^^ (mask ^^^ (key ^^^ other)) := by
  ext i
  simp only [BitVec.getElem_xor]
  cases key[i] <;> cases other[i] <;> cases mask[i] <;> rfl

/-! ### Sealing and checking -/

def openedTag (pad first second : W) : W := pad ^^^ first ^^^ second

def accepts (pad first second received : W) : Bool := openedTag pad first second == received

/-- A wrong half shifts the opened tag by exactly the chosen difference. -/
theorem seal_deviation (pad first second deviation : W) :
    openedTag pad (first ^^^ deviation) second = openedTag pad first second ^^^ deviation := by
  ext i
  simp only [openedTag, BitVec.getElem_xor]
  cases pad[i] <;> cases first[i] <;> cases second[i] <;> cases deviation[i] <;> rfl

/-- For any halves and any received tag there is exactly one accepting pad. -/
theorem accept_unique_pad (first second received : W) :
    ∃ pad : W, accepts pad first second received = true ∧
      ∀ other, accepts other first second received = true → other = pad := by
  have cancel (p : W) : p ^^^ first ^^^ second = received ↔ p = received ^^^ first ^^^ second := by
    constructor
    · intro h
      rw [← h]
      ext i
      simp only [BitVec.getElem_xor]
      cases p[i] <;> cases first[i] <;> cases second[i] <;> rfl
    · intro h
      rw [h]
      ext i
      simp only [BitVec.getElem_xor]
      cases received[i] <;> cases first[i] <;> cases second[i] <;> rfl
  refine ⟨received ^^^ first ^^^ second, ?_, ?_⟩
  · simp only [accepts, openedTag, beq_iff_eq]
    exact (cancel _).mpr rfl
  · intro other h
    simp only [accepts, openedTag, beq_iff_eq] at h
    exact (cancel other).mp h

/-- The genuine tag is rejected under any nonzero deviation of one half. -/
theorem genuine_rejected (pad first second deviation : W) (nonzero : deviation ≠ 0) :
    accepts pad (first ^^^ deviation) second (openedTag pad first second) = false := by
  simp only [accepts, seal_deviation]
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [beq_iff_eq] at h
  apply nonzero
  have : openedTag pad first second ^^^ (openedTag pad first second ^^^ deviation) =
      openedTag pad first second ^^^ openedTag pad first second := congrArg (openedTag pad first second ^^^ ·) h
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] at this
  exact this

/-- With honest halves the check is the comparison with the true tag. -/
theorem honest_accepts (mul : W → W → W) (additive : KeyAdditive mul) (pad received : W)
    (blocks first second : List W) (same : first.length = second.length) :
    accepts pad (localTag mul blocks first) (localTag mul blocks second) received =
      (pad ^^^ localTag mul blocks (List.zipWith (· ^^^ ·) first second) == received) := by
  simp only [accepts, openedTag, BitVec.xor_assoc, localTag_shares mul additive blocks first second same]

/-! ### The repository's GHASH multiplication is additive in the key -/

open Ghash in
theorem nextPower_additive (h k : W) :
    nextPower concrete (h ^^^ k) = nextPower concrete h ^^^ nextPower concrete k := by
  simp only [nextPower, concrete]
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_extractLsb', BitVec.getElem_replicate,
    BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb']
  generalize h.getLsbD (1 + i) = a
  generalize k.getLsbD (1 + i) = b
  generalize (BitVec.ofNat 128 reduction)[i] = c
  cases a <;> cases b <;> cases c <;> simp

open Ghash in
theorem powers_additive (n : Nat) (h k : W) :
    powers concrete n (h ^^^ k) = List.zipWith (· ^^^ ·) (powers concrete n h) (powers concrete n k) := by
  induction n generalizing h k with
  | zero => rfl
  | succ n ih => simp only [powers, nextPower_additive, ih, List.zipWith_cons_cons]

open Ghash in
theorem powers_length (n : Nat) (h : W) : (powers concrete n h).length = n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [powers, List.length_cons, ih]

theorem select_exchange (z y m v w : W) :
    z ^^^ y ^^^ (m &&& (v ^^^ w)) = z ^^^ (m &&& v) ^^^ (y ^^^ (m &&& w)) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and]
  cases z[i] <;> cases y[i] <;> cases m[i] <;> cases v[i] <;> cases w[i] <;> rfl

open Ghash in
theorem multiplyLoop_additive (x : W) (first second : List W) (same : first.length = second.length)
    (i : Nat) (z y : W) :
    multiplyLoop concrete x (List.zipWith (· ^^^ ·) first second) i (z ^^^ y) =
      multiplyLoop concrete x first i z ^^^ multiplyLoop concrete x second i y := by
  induction first generalizing second i z y with
  | nil => cases second <;> simp [multiplyLoop] at same ⊢
  | cons v first ih =>
      cases second with
      | nil => simp at same
      | cons w second =>
          simp only [List.zipWith_cons_cons, multiplyLoop]
          show multiplyLoop concrete x _ (i + 1) (z ^^^ y ^^^ (concrete.maskBit x (127 - i) &&& (v ^^^ w))) = _
          rw [select_exchange]
          exact ih second (by simpa using same) (i + 1) _ _

/-- The repository's GHASH multiplication is additive in the key. -/
theorem multiply_key_additive : KeyAdditive (Ghash.multiply Ghash.concrete) := by
  intro x h k
  simp only [Ghash.multiply, Ghash.multiplyPrepared, powers_additive]
  have zero : Ghash.concrete.const 0 = (Ghash.concrete.const 0 : W) ^^^ Ghash.concrete.const 0 :=
    (BitVec.xor_self (x := (Ghash.concrete.const 0 : W))).symm
  rw [zero]
  exact multiplyLoop_additive x _ _ (by rw [powers_length, powers_length]) 0 _ _

/-! ### What needs the field laws -/

/-- Commutativity and associativity of GF(2^128) multiplication, assumed (not
proved in this development) where the statements below need them. -/
structure Laws (mul : W → W → W) : Prop where
  comm : ∀ x y, mul x y = mul y x
  assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)

theorem cancel_middle (p q s : W) : p ^^^ q ^^^ (q ^^^ s) = p ^^^ s := by
  ext i
  simp only [BitVec.getElem_xor]
  cases p[i] <;> cases q[i] <;> cases s[i] <;> rfl

/-- Squaring is additive, so shares of an even power can be obtained by each
party squaring its own share. Uses commutativity. -/
theorem square_additive (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (a b : W) :
    mul (a ^^^ b) (a ^^^ b) = mul a a ^^^ mul b b := by
  have left (c : W) : mul (a ^^^ b) c = mul a c ^^^ mul b c := by
    rw [laws.comm, additive, laws.comm c a, laws.comm c b]
  rw [left, additive, additive, laws.comm b a]
  exact cancel_middle _ _ _

#print axioms localTag_shares
#print axioms share_hides
#print axioms seal_deviation
#print axioms accept_unique_pad
#print axioms genuine_rejected
#print axioms multiply_key_additive
#print axioms square_additive

end TlsMpc.GhashShares
