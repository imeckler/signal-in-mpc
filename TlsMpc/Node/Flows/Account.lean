import TlsMpc.Node.Flows.ContactsTable

/-!
# `Account.key`, `Account.seal`: the account's own record at rest (ops 53, 54)

REORGANIZATION_PLAN.md stage S9 (op 55, `Account.open`, is S10: it needs `bits_to_field`).
Replaces `service_kernels.h` `account_key` (line 216) and `account_seal` (line 223).

WHAT THE C++ DOES.
  op 53 `account_key(share)`: exactly `contact_key` (kernel `contact-key` on A's and B's private
    shares), the block kept as `account_traffic`. Only the request's size is agreed (dispatch,
    line 162: op 53's prefix is empty).
  op 54 `account_seal(version)`: needs the account key, the account scalar (256 bits: from op 46's
    admission or op 55's open), the certificate (op 46 or 55) and the credentials: either the
    combined handle (op 55) or op 47's two private shares, in which case it first computes
    credentials = xor-bit (copies 8·38) on interleave(shareA, shareB) and keeps it. Then
    `contact-seal N` on (key, version, scalar ‖ credentials ‖ certificate), N = 32 + 38 + |cert|;
    opens check and ciphertext; reply check ‖ ciphertext.

THE SCRIPTS. `Account.keyScript` is `Contacts.keyScript`. `combineBlock` is the credential XOR
(concat, pick for the interleave, run `xor-bit`, frees). `sealScript n key scalar cred cert len
version`: concat n := scalar ‖ cred ‖ cert; `Contacts.sealBlock (n+1) key n`; free n; OPEN n+3
(label sealedBlob); free n+3. The account's handles live in `State` (Lean-side, public), filled
by the legacy ops 46, 47, 55 through `legacy_get` until those move (S10, S16).

ASSUMED BEYOND `Loaded`: nothing for T3 of op 54 with stored credentials. With shares, the
`xor-bit` word circuit runs by name: it is not a kernel of the manifest, and the Rust loader
registers it from its own pinned file, as `word_mask.h` line 27 loads it (node_worker loader.rs
`WORD_CIRCUITS`: signature 2 inputs, 1 private output; the end-to-end tests run this block's shape
on the real engines). Its correctness is the pinned Lean export's (TlsMpc/WordMask.lean).

PROVED: `accountKey_disclosure` (nothing released), `accountSeal_disclosure` (at most the sealed
blob of the key, version and content handles), `opSeal_disclosure` (both credential cases: at
most one release, labelled sealedBlob, the seal kernel's output on the key, the version and the
account content), `accountKey_honest` (T4: the block of `contactKey_spec`).
-/

namespace TlsMpc.Node.Flows.Account

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts

/-- The account's handles (all Boolean). `certificate`: handle and byte length. -/
structure State where
  key : Option BoolH := none
  scalar : Option BoolH := none
  credentials : Option BoolH := none
  shares : Option (BoolH × BoolH) := none
  certificate : Option (BoolH × Nat) := none

/-- Account id (16) and password (22). -/
def credentialBytes : Nat := 16 + 22

def xorName : Bytes := ascii "xor-bit"

/-- `DynSession::interleave` of two `w`-bit halves of one bundle: a0 b0 a1 b1 … -/
def interleave (w : Nat) : List Nat := (List.range w).flatMap fun i => [i, w + i]

/-- Credentials = shareA ⊕ shareB (handles n, n+1, n+2; n+2 is kept). -/
def combineBlock (n : Nat) (ca cb : BoolH) : List Instr :=
  [.concat ⟨n⟩ [ca, cb], .pick ⟨n + 1⟩ ⟨n⟩ (interleave (8 * credentialBytes)),
   .run ⟨n + 2⟩ xorName (8 * credentialBytes) ⟨n + 1⟩, .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]

/-- **Op 53.** -/
abbrev keyScript (n slot : Nat) : Script BoolH := Contacts.keyScript n slot

/-- The content's byte length. -/
def contentBytes (certLen : Nat) : Nat := 32 + credentialBytes + certLen

/-- The instructions before the opening (handles n .. n+3). -/
def accountBlock (n : Nat) (key scalar cred cert : BoolH) (certLen : Nat) (version : B8) : List Instr :=
  .concat ⟨n⟩ [scalar, cred, cert] :: sealBlock (n + 1) key ⟨n⟩ (contentBytes certLen) version ++ [.freeBool ⟨n⟩]

/-- **Op 54's seal.** Reply: check ‖ ciphertext. -/
def sealScript (n : Nat) (key scalar cred cert : BoolH) (certLen : Nat) (version : B8) : Script B8 :=
  if versionOk version = true ∧ contentBytes certLen ≤ 16384 then
    seqs (accountBlock n key scalar cred cert certLen version)
      (openThen ⟨n + 3⟩ sealedBlob fun out =>
        seqs [.freeBool ⟨n + 3⟩] (.done (sealReply (contentBytes certLen) out)))
  else .abort "account seal arguments"

/-- **Op 54** on the account's state from handle `n` on: the script, the next free handle and the
state after it. -/
def opSeal (a : State) (n : Nat) (version : B8) : Script B8 × Nat × State :=
  match a.key, a.scalar, a.certificate, a.credentials, a.shares with
  | some k, some s, some (cert, len), some cr, _ => (sealScript n k s cr cert len version, n + 4, a)
  | some k, some s, some (cert, len), none, some (ca, cb) =>
    (seqs (combineBlock n ca cb) (sealScript (n + 3) k s ⟨n + 2⟩ cert len version), n + 7,
      { a with credentials := some ⟨n + 2⟩ })
  | _, _, _, _, _ => (.abort "account seal unavailable", n, a)

/-! ## T3 -/

section Disclosure

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

/-- **T3 for op 53.** Nothing is released. -/
theorem accountKey_disclosure (n slot : Nat) :
    (withAdv E me adv (keyScript n slot) σ I vD).viewD = [] ∧
      (withAdv E me adv (keyScript n slot) σ I vD).viewH = [] :=
  key_disclosure E me adv σ I vD n slot

/-- The release of an account seal: the `contact-seal` kernel's output on key, version and
content = scalar ‖ credentials ‖ certificate. -/
def released (certLen : Nat) (version : B8) (kv sv cv tv : Bits) : Release :=
  ⟨sealedBlob, .bits (bitsOf (kernelOut (HybridKernel.contactSeal (contentBytes certLen))
    (bytesOf (kv ++ (bitsOf version ++ (sv ++ (cv ++ tv)))))))⟩

/-- **T3 for op 54's seal.** At most one release, labelled `sealedBlob`. -/
theorem accountSeal_disclosure (hE : Loaded E) (n : Nat) (key scalar cred cert : BoolH) (certLen : Nat)
    (version : B8) (kv sv cv tv : Bits) (hkn : key.id < n)
    (hk : I.bools key.id = some kv) (hs : I.bools scalar.id = some sv)
    (hc : I.bools cred.id = some cv) (ht : I.bools cert.id = some tv) :
    (withAdv E me adv (sealScript n key scalar cred cert certLen version) σ I vD).viewD <+:
      [released certLen version kv sv cv tv] := by
  unfold sealScript
  split
  · next hcond =>
    obtain ⟨-, h1⟩ := hcond
    have hcirc := hE.sealing (contentBytes certLen) (by simp [contentBytes, credentialBytes] <;> omega) h1
    apply viewD_seqs E me adv _ σ _ _ (by simp [accountBlock, sealBlock, plain]) I vD
    intro I' hI'
    have a0 : key.id ≠ n := by omega
    have a1 : key.id ≠ n + 1 := by omega
    simp [accountBlock, sealBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool,
      Ideal.dropBool, hk, hs, hc, ht, a0, a1, hcirc, kernelCircuit] at hI'
    by_cases hlen : kv.length + (8 * version.length + (sv.length + (cv.length + tv.length))) =
        8 * (68 + contentBytes certLen)
    · simp only [hlen, if_true] at hI'
      simp at hI'
      subst hI'
      apply viewD_openThen E me adv _ _ _ σ _ vD _ []
      · simp [runCopies_one, hlen]
      · exact silent_prefix E me adv _ (Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])) _ _ _ _
    · simp [hlen] at hI'
  · simp [withAdv]

/-- **T3 for op 54, stored credentials.** At most one release, labelled `sealedBlob`: the seal
kernel's output on the key, the version and the content scalar ‖ credentials ‖ certificate. -/
theorem opSeal_disclosure_stored (hE : Loaded E) (a : State) (n : Nat) (version : B8)
    (k s cr cert : BoolH) (len : Nat) (kv sv cv tv : Bits)
    (hk : a.key = some k) (hs : a.scalar = some s) (ht : a.certificate = some (cert, len))
    (hcr : a.credentials = some cr)
    (hkn : k.id < n)
    (hkv : I.bools k.id = some kv) (hsv : I.bools s.id = some sv) (hcv : I.bools cr.id = some cv)
    (htv : I.bools cert.id = some tv) :
    (withAdv E me adv (opSeal a n version).1 σ I vD).viewD <+: [released len version kv sv cv tv] := by
  simp only [opSeal, hk, hs, ht, hcr]
  exact accountSeal_disclosure E me adv σ I vD hE n k s cr cert len version kv sv cv tv hkn
    hkv hsv hcv htv

/-- **T3 for op 54, credentials from the two shares.** The XOR of the shares stays in the engines;
at most one release, labelled `sealedBlob`: the value of the seal kernel's output handle. -/
theorem opSeal_disclosure_shares (a : State) (n : Nat) (version : B8)
    (k s cert ca cb : BoolH) (len : Nat)
    (hk : a.key = some k) (hs : a.scalar = some s) (ht : a.certificate = some (cert, len))
    (hcr : a.credentials = none) (hsh : a.shares = some (ca, cb)) :
    (withAdv E me adv (opSeal a n version).1 σ I vD).viewD <+:
      [⟨sealedBlob, .bits (openedAfter E (combineBlock n ca cb ++ accountBlock (n + 3) k s ⟨n + 2⟩ cert len version)
        ⟨n + 3 + 3⟩ I)⟩] := by
  simp only [opSeal, hk, hs, ht, hcr, hsh]
  unfold sealScript
  split
  · rw [seqs_append]
    exact viewD_block_open E me adv _ (by simp [combineBlock, accountBlock, sealBlock, plain]) _ _ _
      (fun v => Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])) σ I vD
  · exact silent_prefix E me adv _ (Silent.seqs (Silent.abort _) _ (by simp [combineBlock, InstrP.label?])) _ _ _ _

end Disclosure

/-! ## T4 for op 53 -/

/-- **T4 for `Account.key`** (it is `Contacts.key`): the account key handle holds the block of
`contactKey_spec` from the two shares. -/
theorem accountKey_honest (E : Env) (σA σB : Store) (hE : Loaded E) (I : Ideal) (n slotA slotB : Nat) (a b : B8)
    (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus)
    (hσA : σA.bits slotA = bitsOf a) (hσB : σB.bits slotB = bitsOf b) :
    (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).ideal.bools (n + 3) =
      some (bitsOf (keyBlock a b)) :=
  (key_honest E σA σB hE I n slotA slotB a b ha hb haB hbB hσA hσB).2.1

end TlsMpc.Node.Flows.Account
