import TlsMpc.Node.Flows.ContactsTable
import TlsMpc.Node.Flows.Convert

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
On the session's counters: `sealStep`, `keyStep` (blocks from `State.ctr`), `sealStep_eq`.
The reveal list: `sealScript_reveals`, `opSeal_reveals`, `sealStep_reveals` (`sealKinds`),
`keyStep_reveals` (no kind), `opSeal_viewD_kinds`.
-/

namespace TlsMpc.Node.Flows.Account

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts

/-- The account's handles. `certificate`: handle and byte length. `ctr`: the session's handle
counters (Engine.lean decision D12), from which `keyStep` and `sealStep` take their blocks.
`identity` (J8, J12): the identity scalar's 252 ladder swap bits as FIELD handles (op 55's
`bitsToField`, or op 46's), the C++'s `account.identity`: what every agreement with the identity key
uses; field handles have no `once` (Engine.lean D3), so they stay for the session.
`senderPublic` (J12): the account's identity public key as the 255-bit word X25519 uses, the
C++'s `account.sender_public` = `agreement_word(identity, 9)` (`service_kernels.h` line 62): made
once from `identity` by an agreement with the base point (`Flows/ContactsPrepare.lean`
`senderPublicG`), kept for the session (live, not once). -/
structure State where
  key : Option BoolH := none
  scalar : Option BoolH := none
  credentials : Option BoolH := none
  shares : Option (BoolH × BoolH) := none
  certificate : Option (BoolH × Nat) := none
  ctr : Counters := {}
  identity : Option (List FieldH) := none
  senderPublic : Option BoolH := none

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

/-! ## On the session's counters (Engine.lean decision D12)

`opSeal a n` takes its first handle id `n` from the caller. `sealStep` and `keyStep` take it from
the state's counters instead: a block of `Counters.allocB` (7 ids when the credentials are combined
from the shares, 4 otherwise; 4 for the key), and the state after the step carries the counters past
the block. `sealStep_eq`: `sealStep` is `opSeal` at the counter, the counter moved to `opSeal`'s
next free id; so every theorem about `opSeal a n` applies with `n = a.ctr.bool`. -/

/-- **Op 54 on the counters.** The script and the state after it. -/
def sealStep (a : State) (version : B8) : Script B8 × State :=
  match a.key, a.scalar, a.certificate, a.credentials, a.shares with
  | some k, some s, some (cert, len), some cr, _ =>
    (sealScript (a.ctr.allocB 4).1 k s cr cert len version, { a with ctr := (a.ctr.allocB 4).2 })
  | some k, some s, some (cert, len), none, some (ca, cb) =>
    (seqs (combineBlock (a.ctr.allocB 7).1 ca cb)
        (sealScript ((a.ctr.allocB 7).1 + 3) k s ⟨(a.ctr.allocB 7).1 + 2⟩ cert len version),
      { a with credentials := some ⟨(a.ctr.allocB 7).1 + 2⟩, ctr := (a.ctr.allocB 7).2 })
  | _, _, _, _, _ => (.abort "account seal unavailable", a)

/-- **`sealStep` is `opSeal` at the counter**, the counter moved to `opSeal`'s next free id. -/
theorem sealStep_eq (a : State) (version : B8) :
    (sealStep a version).1 = (opSeal a a.ctr.bool version).1 ∧
      (sealStep a version).2 =
        { (opSeal a a.ctr.bool version).2.2 with ctr := { a.ctr with bool := (opSeal a a.ctr.bool version).2.1 } } := by
  obtain ⟨key, scalar, cred, shares, cert, ctr, _, _⟩ := a
  cases key <;> cases scalar <;> cases cert <;> cases cred <;> cases shares <;> exact ⟨rfl, rfl⟩

/-- **Op 53 on the counters.** Frees the previous account key (as `Contacts.opKey` does), then
`keyScript` on a block of 4 ids; the state after it holds the new key. -/
def keyStep (a : State) (slot : Nat) : Script BoolH × (BoolH → State) :=
  (seqs (frees a.key.toList) (keyScript (a.ctr.allocB 4).1 slot),
    fun h => { a with key := some h, ctr := (a.ctr.allocB 4).2 })

/-- `keyStep` moves the counter past its block of 4 ids. -/
theorem keyStep_ctr (a : State) (slot : Nat) (h : BoolH) : ((keyStep a slot).2 h).ctr.bool = a.ctr.bool + 4 := rfl

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

/-! ### The reveal list (Engine/Reveal.lean): op 54 declares `sealKinds`, op 53 no kind -/

theorem sealScript_reveals (n : Nat) (key scalar cred cert : BoolH) (certLen : Nat) (version : B8) :
    Reveals sealKinds (sealScript n key scalar cred cert certLen version) := by
  unfold sealScript
  split
  · exact every_seqs (every_openThen (LabelIn.of_mem (k := .sealedBlob) (by simp [sealKinds]) rfl)
      (fun b => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
      (labelIn_of_none (by simp [accountBlock, sealBlock, InstrP.label?]))
  · exact Every.abort _

theorem opSeal_reveals (a : State) (n : Nat) (version : B8) : Reveals sealKinds (opSeal a n version).1 := by
  unfold opSeal
  split
  · exact sealScript_reveals _ _ _ _ _ _ _
  · exact every_seqs (sealScript_reveals _ _ _ _ _ _ _) _ (labelIn_of_none (by simp [combineBlock, InstrP.label?]))
  · exact Every.abort _

theorem sealStep_reveals (a : State) (version : B8) : Reveals sealKinds (sealStep a version).1 := by
  rw [(sealStep_eq a version).1]
  exact opSeal_reveals a _ version

theorem keyStep_reveals (a : State) (slot : Nat) : Reveals keyKinds (keyStep a slot).1 :=
  (Silent.seqs (keyScript_silent _ _) _ (frees_silent _)).reveals _

/-- **T3 for op 54 in the reveal list's vocabulary** (both credential cases, any state): every
release the adversary receives is labelled `ofKind .sealedBlob`. -/
theorem opSeal_viewD_kinds (a : State) (n : Nat) (version : B8) :
    ∀ r ∈ (withAdv E me adv (opSeal a n version).1 σ I vD).viewD, ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (opSeal_reveals a n version) σ I vD

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

/-! ## Op 55: `Account.open` (stage S10)

Replaces `service_kernels.h` `account_open` (232-243). Loads the account's record from its stored
ciphertext under the account key (op 53): `contact-open N` (N = the ciphertext's length), the
`accepted` byte opened (label `blobAccepted`) and required to be 255 (the C++ aborts otherwise:
"account key does not match the stored state"); the content is split into the scalar (256 bits),
the credentials (8·38) and the certificate. Then the ladder's swap bits: the `swap-bits` circuit
(`X25519SwapBits.circuit`, 252 outputs, private) on the scalar, into the field engine through
`Convert.bitsToField` with 252 bit pairs from the pool; with `hinted`, also the scalar's bits
3 … 253 (251 pairs). Nothing else is opened.

Handles: Boolean from `n` (`n … n + 8`, then `bitsToField`'s four from `n + 9`, the hinted slice
`n + 13`, its four from `n + 14`); field from `f` (the swap bits' `bitsToField` uses `f … f + 253`,
the hinted one `f + 254 … f + 506`). -/

open TlsMpc.Node.Flows.Conv in
/-- The stored record's fixed part: scalar 32, account id 16, password 22. -/
def fixedBytes : Nat := 32 + credentialBytes

def openArgs55 (version check ct : B8) : Prop :=
  versionOk version = true ∧ check.length = 16 ∧ fixedBytes < ct.length ∧ ct.length ≤ fixedBytes + 1024

instance (version check ct : B8) : Decidable (openArgs55 version check ct) := by
  unfold openArgs55; infer_instance

/-- What op 55 leaves: the account state (scalar, credentials, certificate), the swap bits in the
field engine, the hinted bits when asked, and the pool without the pairs used. -/
structure Opened where
  state : State
  swaps : List FieldH
  hintedBits : Option (List FieldH)
  pool : Conv.MaskPool

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
/-- The split of the content handle `c` and the swap bits (after the key check). -/
def splitBlock (n : Nat) (c : BoolH) (len : Nat) : List Instr :=
  [.slice ⟨n + 5⟩ c 0 256, .slice ⟨n + 6⟩ c 256 (8 * fixedBytes), .slice ⟨n + 7⟩ c (8 * fixedBytes) (8 * len),
   .freeBool c, .run ⟨n + 8⟩ swapBitsName 1 ⟨n + 5⟩]

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
/-- The hinted bits (scalar bits 3 … 253), when asked. -/
def hintedStep (n f : Nat) (pool : MaskPool) (hinted : Bool) : Script (Option (List FieldH) × MaskPool) :=
  if hinted then
    match pool.takeBits 251 with
    | some (ps, pool') =>
      seqs [.slice ⟨n + 13⟩ ⟨n + 5⟩ 3 254] <|
      (bitsToField (n + 14) (f + 254) ⟨n + 13⟩ ps).bind fun hs => .done (some hs, pool')
    | none => .abort "bit pairs exhausted"
  else .done (none, pool)

/-- The account state after op 55: the scalar, the credentials and the certificate handles. -/
def openedState (a : State) (n len : Nat) : State :=
  { a with scalar := some ⟨n + 5⟩, credentials := some ⟨n + 6⟩, certificate := some (⟨n + 7⟩, len - fixedBytes) }

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
/-- **Op 55** on the account state `a` (its key from op 53), the stored record (version, check,
ciphertext), the pool, and whether the hinted bits are needed. -/
def openStep (a : State) (n f : Nat) (pool : MaskPool) (hinted : Bool) (version check ct : B8) : Script Opened :=
  match a.key with
  | none => .abort "account open unavailable"
  | some k =>
    if openArgs55 version check ct then
      (Contacts.openScript n k version check ct).bind fun c? =>
      match c? with
      | none => .abort "account key does not match the stored state"
      | some c =>
        match pool.takeBits 252 with
        | none => .abort "bit pairs exhausted"
        | some (ps, pool1) =>
          seqs (splitBlock n c ct.length) <|
          (bitsToField (n + 9) f ⟨n + 8⟩ ps).bind fun swaps =>
          (hintedStep n f pool1 hinted).bind fun r =>
          .done ⟨{ openedState a n ct.length with identity := some swaps }, swaps, r.1, r.2⟩
    else .abort "account open arguments"

/-- The kinds op 55 declares: the `accepted` byte and the masked bits of the conversions. -/
def openKinds55 : List TlsMpc.Node.RevealKind := [.blobAccepted, .maskedBit]

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
theorem openStep_reveals (a : State) (n f : Nat) (pool : MaskPool) (hinted : Bool) (version check ct : B8) :
    Reveals openKinds55 (openStep a n f pool hinted version check ct) := by
  have hb2f : ∀ n0 f0 x ps, Reveals openKinds55 (bitsToField n0 f0 x ps) := fun n0 f0 x ps =>
    (b2f_reveals n0 f0 x ps).mono (by simp [b2fKinds, openKinds55])
  unfold openStep
  split
  · exact Every.abort _
  · split
    · refine Every.bind ((openScript_reveals _ _ _ _ _).mono (by simp [openKinds, openKinds55])) fun c? => ?_
      split
      · exact Every.abort _
      · split
        · exact Every.abort _
        · refine every_seqs (Every.bind (hb2f _ _ _ _) fun swaps => Every.bind ?_ fun r => Every.done _) _
            (fun i hi => ?_)
          · unfold hintedStep
            split
            · split
              · exact every_seqs (Every.bind (hb2f _ _ _ _) fun _ => Every.done _) _ (fun i hi => by
                  simp at hi; subst hi; exact LabelIn.of_none rfl)
              · exact Every.abort _
            · exact Every.done _
          · simp only [splitBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact LabelIn.of_none rfl
    · exact Every.abort _

/-- **T3 for op 55 in the reveal list's vocabulary**: every release the adversary receives is the
`accepted` byte (`blobAccepted`) or a masked bit of a conversion (`maskedBit`): nothing of the
scalar, the credentials or the certificate. -/
theorem openStep_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (a : State) (n f : Nat) (pool : Conv.MaskPool) (hinted : Bool) (version check ct : B8) :
    ∀ r ∈ (withAdv E me adv (openStep a n f pool hinted version check ct) σ I vD).viewD,
      ∃ k ∈ openKinds55, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (openStep_reveals a n f pool hinted version check ct) σ I vD

open TlsMpc.Node.Flows.Conv in
/-- **Correctness of the swap bits (op 55)**: the `swap-bits` circuit's output k is the swap bit of
ladder step k + 2 of the scalar whose bits are the input (`X25519Fast.swapBitSpec`, through
`X25519SwapBits.swapBit_eval`); bits to field then carries each into the field engine
(`Convert.b2f_value`). -/
theorem swapBits_spec (v : Bits) :
    swapBitsEval v = (List.range 252).map fun k => X25519Fast.swapBitSpec (fun i => v.getD i false) (k + 2) := by
  unfold swapBitsEval
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [← X25519SwapBits.swapBit_eval (fun i => v.getD i false) (k + 2) (by omega) (by omega)]
  unfold swapBit X25519SwapBits.swapBit
  split
  · rfl
  · split
    · simp [TlsMpc.WordMask.not', TlsMpc.BoolDag.Expr.eval]
    · simp [TlsMpc.BoolDag.Expr.eval]

/-- **The pairs op 55 uses are not left in the pool** (P-PAIR (c), `MaskPool.takeBits_fresh`). -/
theorem openStep_pool (pool pool1 : Conv.MaskPool) (ps : List Conv.BitPair) (hd : pool.Distinct)
    (h : pool.takeBits 252 = some (ps, pool1)) : (∀ q ∈ ps, q ∉ pool1.bits) ∧ pool1.Distinct :=
  ⟨(Conv.MaskPool.takeBits_fresh hd h).1, (Conv.MaskPool.takeBits_fresh hd h).2.2.2.1⟩

/-! ## Op 47: `Account.credentials` (stage S16, J11)

Replaces `service_kernels.h` `account_credentials` (252-257): each party's XOR share of the account
id and password (38 bytes) is its own private input (`input_private(ALICE, …)`,
`input_private(BOB, …)`), neither party can open the authenticated socket alone. Here one
`boolInputBoth` (A's share at `n`, B's at `n + 1`, 304 bits each, private, NOT once: the authenticated
upgrade and the account seal both read them). Refused when the shares are already in (the C++'s
`!credentials_a.size()`). Releases nothing. -/

/-- **Op 47's engine part**: both shares from this party's store slot `slot`. -/
def credentialsScript (n slot : Nat) : Script (BoolH × BoolH) :=
  seqs [.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * credentialBytes) false false slot] (.done (⟨n⟩, ⟨n + 1⟩))

/-- **Op 47 on the counters**: a block of 2 ids; the state after it holds the two shares. -/
def credentialsStep (a : State) (slot : Nat) : Script (BoolH × BoolH) × (BoolH × BoolH → State) :=
  match a.shares with
  | some _ => (.abort "account credentials", fun _ => a)
  | none => (credentialsScript (a.ctr.allocB 2).1 slot,
      fun p => { a with shares := some p, ctr := (a.ctr.allocB 2).2 })

theorem credentialsStep_reveals (a : State) (slot : Nat) : Reveals [] (credentialsStep a slot).1 := by
  unfold credentialsStep
  split
  · exact Every.abort _
  · exact every_seqs (Every.done _) _ (fun i hi => by simp at hi; subst hi; exact LabelIn.of_none rfl)

/-- The credential shares are two fresh handles of the step's block, side by side. -/
theorem credentialsStep_shares (a : State) (slot : Nat) (p : BoolH × BoolH) (h : a.shares = none) :
    ((credentialsStep a slot).2 p).shares = some p ∧ ((credentialsStep a slot).2 p).ctr.bool = a.ctr.bool + 2 := by
  simp [credentialsStep, h, Counters.allocB]

/-! ## Op 46 (TEST): `Account.admitTest` (stage S16, J11)

Replaces `service_kernels.h` `admit_account` (204-211): the account from a local-server export, both
controllers hold the same disposable test state and party A enters it as private wires: the
identity key's 32 bytes (A's input; B sends none) and the sender certificate (A's input, its exact
length, 1 … 1024 bytes). The identity's ladder swap bits as op 55 makes them (`swap-bits`, then
bits to field with 252 pairs from the pool; with `hinted` the scalar's bits 3 … 253 too). Same
handle layout as `openStep` (scalar `n + 5`, certificate `n + 7`, swap bits `n + 8`, conversions
from `n + 9`; field ids from `f`), so the same blocks (19 Boolean ids, 507 field ids) serve.
Releases only the conversions' masked bits. -/

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
/-- **Op 46.** `scalarSlot`: this party's 256 bits of the identity key (A's are read); `certSlot`:
the certificate's bits (A's are read). -/
def admitStep (a : State) (n f : Nat) (pool : MaskPool) (hinted : Bool) (scalarSlot certSlot certLen : Nat) :
    Script Opened :=
  if 0 < certLen ∧ certLen ≤ 1024 ∧ a.scalar.isNone then
    match pool.takeBits 252 with
    | none => .abort "bit pairs exhausted"
    | some (ps, pool1) =>
      seqs [.boolInput ⟨n + 5⟩ .a 256 false false scalarSlot, .boolInput ⟨n + 7⟩ .a (8 * certLen) false false certSlot,
        .run ⟨n + 8⟩ swapBitsName 1 ⟨n + 5⟩] <|
      (bitsToField (n + 9) f ⟨n + 8⟩ ps).bind fun swaps =>
      (hintedStep n f pool1 hinted).bind fun r =>
      .done ⟨{ a with scalar := some ⟨n + 5⟩, certificate := some (⟨n + 7⟩, certLen), identity := some swaps },
        swaps, r.1, r.2⟩
  else .abort "account admission"

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
theorem hintedStep_reveals (n f : Nat) (pool : MaskPool) (hinted : Bool) :
    Reveals openKinds55 (hintedStep n f pool hinted) := by
  have hb2f : ∀ n0 f0 x ps, Reveals openKinds55 (bitsToField n0 f0 x ps) := fun n0 f0 x ps =>
    (b2f_reveals n0 f0 x ps).mono (by simp [b2fKinds, openKinds55])
  unfold hintedStep
  split
  · split
    · exact every_seqs (Every.bind (hb2f _ _ _ _) fun _ => Every.done _) _ (fun i hi => by
        simp at hi; subst hi; exact LabelIn.of_none rfl)
    · exact Every.abort _
  · exact Every.done _

open TlsMpc.Node.Flows.Conv TlsMpc.Node.Flows.Convert in
/-- **T3 for op 46 in the reveal list's vocabulary**: only the conversions' masked bits
(`openKinds55`'s `maskedBit`; the key and the certificate are never opened). -/
theorem admitStep_reveals (a : State) (n f : Nat) (pool : MaskPool) (hinted : Bool) (scalarSlot certSlot certLen : Nat) :
    Reveals openKinds55 (admitStep a n f pool hinted scalarSlot certSlot certLen) := by
  have hb2f : ∀ n0 f0 x ps, Reveals openKinds55 (bitsToField n0 f0 x ps) := fun n0 f0 x ps =>
    (b2f_reveals n0 f0 x ps).mono (by simp [b2fKinds, openKinds55])
  unfold admitStep
  split
  · split
    · exact Every.abort _
    · refine every_seqs (Every.bind (hb2f _ _ _ _) fun swaps =>
        Every.bind (hintedStep_reveals _ _ _ _) fun r => Every.done _) _ (fun i hi => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact LabelIn.of_none rfl
  · exact Every.abort _

end TlsMpc.Node.Flows.Account
