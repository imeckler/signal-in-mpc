import TlsMpc.Node.Flows.ContactsBase

/-!
# `Contacts.key`, `Contacts.seal`, `Contacts.open`: a contact's state at rest (ops 36, 38, 37)

REORGANIZATION_PLAN.md stage S9; replaces `service_kernels.h` `contact_key`, `contact_seal`,
`contact_open` (lines 422-451) and the dispatch of `tls_worker_v3.cpp` ops 36-38. Advance work in a
new file; the C++ ops stay in use until the controller switches.

WHAT THE C++ DOES, AND THE SCRIPTS HERE (handles: Boolean wire bundles; `n` is the session's next
free Boolean handle id; bits of bytes least significant first, `kernel.h` `byte_bits`):

  op 36 `contact_key(id, share)`: A inputs its 32-byte share privately, B its own (two
  `input_private`), kernel `contact-key` (inputs shareA 32, shareB 32 bytes; output traffic 60
  bytes, private) gives the record key block, kept as `conversations[id].key`. Nothing is opened;
  only the request's public prefix (the id) and its size are agreed (`dispatch`, line 162).
    `keyScript n slot`: boolInputBoth (n: A's share, n+1: B's share; 256 bits each, `once`, from
    this party's store slot `slot`), concat n+2, run `contact-key` -> n+3. Returns n+3. The shares
    are `once`: consumed by the concat, whose result is consumed by the run.

  op 38 `contact_seal(id, version)`: needs the key and the loaded state; version 8 bytes, not
  2^64-1; kernel `contact-seal N` (traffic 60, version 8 public, content N; outputs ciphertext N
  and check 16, both public) on (key, version, state); opens check and ciphertext; reply
  check ‖ ciphertext.
    `sealScript n key state size version`: public bits n := version; concat n+1 := key ‖ n ‖ state;
    run `contact-seal size` -> n+2; free n, n+1; OPEN n+2 (label sealedBlob: ciphertext ‖ check,
    one opening for the C++'s two of the same public outputs); free n+2. Returns check ‖ ciphertext.

  op 37 `contact_open(id, version, check, ciphertext)`: needs the key and no loaded state; check
  16 bytes; ciphertext 319 bytes (op 63 below: the device list's size); kernel `contact-open N`
  (traffic, version, ciphertext, check; outputs accepted 1 byte public, content N private) on the
  key and the public values; opens `accepted`; 255: the content becomes the contact's state
  (derived caches dropped), reply 255; otherwise reply 0 and the contact stays unloaded.
    `openScript n key version check ct`: public bits n := version ‖ ct ‖ check; concat n+1 :=
    key ‖ n; run `contact-open |ct|` -> n+2; slice n+3 := bits 0..8 (accepted), n+4 := bits
    8..8+8|ct| (content); free n, n+1, n+2; OPEN n+3 (label blobAccepted); free n+3; accepted
    (the bits of byte 255): returns n+4, the state's handle; otherwise frees n+4, returns none.

  The per-contact table (`conversations` in the C++) is Lean-side public state here: see
  `ContactsTable.lean` (`Contacts.key/seal/open/openDevices/evict/assign` on the table).

PROVED (ideal model of Engine/Model.lean; `Loaded E`: the three kernels' circuits compute their
Lean definitions, ContactsBase.lean):
  WF: `keyScript_wf`, `sealScript_wf`, `openScript_wf` (the shell's `check` accepts every
    instruction on every branch, from any context in which the handle counter is fresh and the
    operands are live with the kernel widths), and with the context each leaves
    (`keyScript_wfp`, `sealScript_wfp`, `openScript_wfp`: `KeyPost`, `SealPost`, `OpenPost`: the
    returned handle and its marks, the handles below the counter untouched, the counter past the
    script's block), which ContactsTable.lean uses for the table invariant.
  T3 (disclosure, against ANY adversary): `key_disclosure` (nothing is released to either party);
    `seal_disclosure` (at most one release, labelled sealedBlob: the `contact-seal` kernel's output
    on the key, version and state handles' values); `open_disclosure` (at most one release,
    labelled blobAccepted: the first byte of the `contact-open` kernel's output, its `accepted`
    field) and `open_released_byte` (for a key of 60 bytes that byte is 255 or 0 according as the
    check value matches: the adversary learns exactly whether the stored check value is this key's).
  T4-CONTACT (two honest parties): `key_honest` (the key handle holds
    `contactKey_spec`'s block from the two shares, other handles untouched), `seal_honest`
    (the result is checkOf K ‖ ctrOf K version S, `contactSeal_spec`), `open_honest` (accepted iff
    check = checkOf K, `contactOpen_accepted_iff`; accepted: the state handle holds
    ctrOf K version ct; not accepted: result none and the content handle is freed), and
    `open_after_seal` / `key_seal_open` (opening what an honest seal produced, under a key derived
    from the same shares, returns the sealed state).
-/

namespace TlsMpc.Node.Flows.Contacts

open TlsMpc.Node.Engine
open Std.Tactic.BVDecide

/-! ## The scripts -/

/-- A version number that may be used (8 bytes, not the reserved 2^64 − 1). -/
def versionOk (v : B8) : Bool := v.length == 8 && v != List.replicate 8 255

/-- **Op 36's engine part.** `slot`: this party's store slot holding its share's 256 bits. -/
def keyScript (n slot : Nat) : Script BoolH :=
  seqs [.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false slot,
        .concat ⟨n + 2⟩ [⟨n⟩, ⟨n + 1⟩],
        .run ⟨n + 3⟩ keyName 1 ⟨n + 2⟩]
    (.done ⟨n + 3⟩)

/-- The instructions of a seal before its opening. -/
def sealBlock (n : Nat) (key state : BoolH) (size : Nat) (version : B8) : List Instr :=
  [.boolPublic ⟨n⟩ (bitsOf version),
   .concat ⟨n + 1⟩ [key, ⟨n⟩, state],
   .run ⟨n + 2⟩ (sealName size) 1 ⟨n + 1⟩,
   .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩]

/-- What a seal returns from the opened output bundle (ciphertext ‖ check): check ‖ ciphertext. -/
def sealReply (size : Nat) (out : Bits) : B8 := (bytesOf out).drop size ++ (bytesOf out).take size

/-- **Op 38's engine part.** `size`: the state's length in bytes. -/
def sealScript (n : Nat) (key state : BoolH) (size : Nat) (version : B8) : Script B8 :=
  if versionOk version = true ∧ 0 < size ∧ size ≤ 16384 then
    seqs (sealBlock n key state size version)
      (openThen ⟨n + 2⟩ sealedBlob fun out =>
        seqs [.freeBool ⟨n + 2⟩] (.done (sealReply size out)))
  else .abort "contact seal arguments"

/-- The instructions of an open before its opening. -/
def openBlock (n : Nat) (key : BoolH) (version check ct : B8) : List Instr :=
  [.boolPublic ⟨n⟩ (bitsOf (version ++ ct ++ check)),
   .concat ⟨n + 1⟩ [key, ⟨n⟩],
   .run ⟨n + 2⟩ (openName ct.length) 1 ⟨n + 1⟩,
   .slice ⟨n + 3⟩ ⟨n + 2⟩ 0 8,
   .slice ⟨n + 4⟩ ⟨n + 2⟩ 8 (8 + 8 * ct.length),
   .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩]

/-- After the opening of `accepted`. -/
def openRest (n : Nat) (acc : Bits) : Script (Option BoolH) :=
  if acc = bitsOf [255] then seqs [.freeBool ⟨n + 3⟩] (.done (some ⟨n + 4⟩))
  else seqs [.freeBool ⟨n + 3⟩, .freeBool ⟨n + 4⟩] (.done none)

def openArgsOk (version check ct : B8) : Prop :=
  versionOk version = true ∧ check.length = 16 ∧ 0 < ct.length ∧ ct.length ≤ 16384

instance (version check ct : B8) : Decidable (openArgsOk version check ct) := by
  unfold openArgsOk; infer_instance

/-- **Op 37's engine part** (and op 63's, `openDevices`). Returns the loaded state's handle, or
`none` when the key does not match the stored check value. -/
def openScript (n : Nat) (key : BoolH) (version check ct : B8) : Script (Option BoolH) :=
  if openArgsOk version check ct then
    seqs (openBlock n key version check ct) (openThen ⟨n + 3⟩ blobAccepted (openRest n))
  else .abort "contact open arguments"

/-! ## Kernel values (from `ContactKernelsProofs.lean`) -/

/-- `contactKey_spec`'s record key block from shares `a`, `b`. -/
def keyBlock (a b : B8) : B8 :=
  List.replicate 32 0 ++ (Sha256.hash Sha256.concrete (HybridKernel.contactLabel ++
    ModAdd.leBytes 32 ((ModAdd.leValue a + ModAdd.leValue b) % HybridKernel.shareModulus))).take 28

/-- The sealed blob (the C++ reply): check value, then ciphertext. -/
def sealed (K version S : B8) : B8 := HybridKernel.checkOf K ++ HybridKernel.ctrOf K version S

theorem keyBlock_length (a b : B8) : (keyBlock a b).length = 60 := by
  simp [keyBlock, Sha256.hash_length]

theorem kernelOut_key (a b : B8) (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus) :
    kernelOut HybridKernel.contactKey (a ++ b) = keyBlock a b := by
  have e1 : HybridKernel.inputValue (assignOf (a ++ b)) 0 32 = a := by
    rw [inputValue_assignOf _ 0 32 (by simp; omega), List.drop_zero, List.take_left' ha]
  have e2 : HybridKernel.inputValue (assignOf (a ++ b)) 32 32 = b := by
    rw [inputValue_assignOf _ 32 32 (by simp; omega), List.drop_left' ha, List.take_of_length_le (by omega)]
  unfold kernelOut
  rw [HybridKernel.contactKey_spec _ (by rw [e1]; exact haB) (by rw [e2]; exact hbB), e1, e2]
  simp [keyBlock]

theorem kernelOut_seal (size : Nat) (K version S : B8) (hK : K.length = 60) (hv : version.length = 8)
    (hS : S.length = size) :
    kernelOut (HybridKernel.contactSeal size) (K ++ (version ++ S)) =
      HybridKernel.ctrOf K version S ++ HybridKernel.checkOf K := by
  have e1 : HybridKernel.inputValue (assignOf (K ++ (version ++ S))) 0 60 = K := by
    rw [inputValue_assignOf _ 0 60 (by simp; omega), List.drop_zero, List.take_left' hK]
  have e2 : HybridKernel.inputValue (assignOf (K ++ (version ++ S))) 60 8 = version := by
    rw [inputValue_assignOf _ 60 8 (by simp; omega), List.drop_left' hK, List.take_left' hv]
  have e3 : HybridKernel.inputValue (assignOf (K ++ (version ++ S))) 68 size = S := by
    rw [inputValue_assignOf _ 68 size (by simp; omega), ← List.append_assoc,
      List.drop_left' (by simp; omega), List.take_of_length_le (by omega)]
  unfold kernelOut
  rw [HybridKernel.contactSeal_spec, e1, e2, e3]
  simp

theorem kernelOut_open (size : Nat) (K version ct check : B8) (hK : K.length = 60) (hv : version.length = 8)
    (hct : ct.length = size) (hc : check.length = 16) :
    kernelOut (HybridKernel.contactOpen size) (K ++ (version ++ (ct ++ check))) =
      HybridKernel.contactMask K check ::
        ByteAuth.release ByteAuth.concrete (HybridKernel.contactMask K check) (HybridKernel.ctrOf K version ct) := by
  have e1 : HybridKernel.inputValue (assignOf (K ++ (version ++ (ct ++ check)))) 0 60 = K := by
    rw [inputValue_assignOf _ 0 60 (by simp; omega), List.drop_zero, List.take_left' hK]
  have e2 : HybridKernel.inputValue (assignOf (K ++ (version ++ (ct ++ check)))) 60 8 = version := by
    rw [inputValue_assignOf _ 60 8 (by simp; omega), List.drop_left' hK, List.take_left' hv]
  have e3 : HybridKernel.inputValue (assignOf (K ++ (version ++ (ct ++ check)))) 68 size = ct := by
    rw [inputValue_assignOf _ 68 size (by simp; omega), ← List.append_assoc,
      List.drop_left' (by simp; omega), List.take_left' hct]
  have e4 : HybridKernel.inputValue (assignOf (K ++ (version ++ (ct ++ check)))) (68 + size) 16 = check := by
    rw [inputValue_assignOf _ (68 + size) 16 (by simp; omega), ← List.append_assoc, ← List.append_assoc,
      List.drop_left' (by simp; omega), List.take_of_length_le (by omega)]
  unfold kernelOut
  rw [HybridKernel.contactOpen_spec, e1, e2, e3, e4]
  simp

theorem runCopies_one (c : Engine.Circuit) (v : Bits) (h : v.length = c.inWidth) : runCopies c 1 v = c.eval v := by
  simp [runCopies, List.take_of_length_le, h]

theorem checkOf_length (K : B8) (hK : K.length = 60) : (HybridKernel.checkOf K).length = 16 :=
  Aes.encryptExpanded_length _ 10 _ _ (HybridKernel.expandedOf_length K hK)

theorem versionOk_length (v : B8) (h : versionOk v = true) : v.length = 8 := by
  simp [versionOk] at h
  exact h.1

/-! ## Well-formedness -/

theorem shares_length (w : Nat) (m : Mark) :
    ((List.map BoolInfo.marks [⟨List.replicate w m, true⟩, ⟨List.replicate w m, true⟩]).flatten).length =
      1 * (w + w) := by
  simp

/-- What `keyScript n` leaves: it returns handle `n + 3`, which holds the key (480 private bits,
not once); the handles below `n` are as before; no id from `n + 4` on was defined. -/
def KeyPost (c : Ctx) (n : Nat) (c' : Ctx) (h : BoolH) : Prop :=
  h = ⟨n + 3⟩ ∧ c'.bool? ⟨n + 3⟩ = some ⟨keyMarks, false⟩ ∧ (∀ g : BoolH, g.id < n → c'.bool? g = c.bool? g) ∧
    Fresh c' (n + 4)

theorem keyScript_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n slot : Nat) (hf : Fresh c n)
    (hsig : sigs keyName = some ⟨512, keyMarks⟩) : WFP sigs (KeyPost c n) c (keyScript n slot) := by
  unfold keyScript
  simp only [seqs_cons, seqs_nil]
  have hf1 := (hf.push n (Nat.le_refl n) ⟨List.replicate 256 (Mark.ofInput false), true⟩).push (n + 1)
    (Nat.le_refl _) ⟨List.replicate 256 (Mark.ofInput false), true⟩
  have hf2 := (hf1.drop n).drop (n + 1)
  refine WFP_seq sigs c _ _ _ (check_boolInputBoth sigs hf 256 true false (by decide)) ?_
  refine WFP_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_once ((bool?_push_of_ne _ _ _ _ (by simp)).trans (bool?_push_self _ _ _)) rfl)
      (useBools_cons (useBool_once ((bool?_drop_of_ne _ _ _ (by simp)).trans (bool?_push_self _ _ _)) rfl)
        (useBools_nil _))) hf2
      (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.length_append, List.length_replicate, maxWidth_eq]; omega)) ?_
  have hf3 := (hf2.push (n + 2) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨List.replicate 256 (Mark.ofInput false), true⟩,
    ⟨List.replicate 256 (Mark.ofInput false), true⟩]).flatten, true⟩).drop (n + 2)
  refine WFP_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_once (bool?_push_self _ _ _) rfl)
    (shares_length 256 _) hf3 (by decide) (by simp only [keyMarks, List.length_replicate, maxWidth_eq]; omega)) ?_
  refine WFP.done _ _ ⟨rfl, ?_, fun g hg => ?_, hf3.push (n + 3) (Nat.le_refl _) _⟩
  · rw [bool?_push_self]
    simp only [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil]
  · have e0 : g.id ≠ n := by omega
    have e1 : g.id ≠ n + 1 := by omega
    have e2 : g.id ≠ n + 2 := by omega
    have e3 : g.id ≠ n + 3 := by omega
    simp only [bool?_push, bool?_drop, e0, e1, e2, e3, if_false]

theorem keyScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n slot : Nat) (hf : Fresh c n)
    (hsig : sigs keyName = some ⟨512, keyMarks⟩) : WF sigs c (keyScript n slot) :=
  (keyScript_wfp sigs c n slot hf hsig).wf

/-- What a seal leaves: the handles below `n` as before, nothing defined from `n + 3` on. -/
def SealPost (c : Ctx) (n : Nat) (c' : Ctx) (_ : B8) : Prop :=
  (∀ g : BoolH, g.id < n → c'.bool? g = c.bool? g) ∧ Fresh c' (n + 3)

theorem sealScript_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (key state : BoolH) (size : Nat)
    (version : B8) (km sm : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hsn : state.id < n)
    (hk : c.bool? key = some ⟨km, false⟩) (hs : c.bool? state = some ⟨sm, false⟩)
    (hkm : km.length = 480) (hsm : sm.length = 8 * size)
    (hsig' : 0 < size → size ≤ 16384 → sigs (sealName size) = some ⟨8 * (68 + size), sealMarks size⟩) :
    WFP sigs (SealPost c n) c (sealScript n key state size version) := by
  unfold sealScript
  split
  · next hc =>
    obtain ⟨hv, h0, h1⟩ := hc
    have hsig := hsig' h0 h1
    have hvl := versionOk_length version hv
    simp only [sealBlock, seqs_cons, seqs_nil]
    have hf1 := hf.push n (Nat.le_refl n) ⟨List.replicate (bitsOf version).length .pub, false⟩
    refine WFP_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp [hvl, maxWidth])) ?_
    refine WFP_seq sigs _ _ _ _ (check_concat sigs
      (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans hk) rfl)
        (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
          (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans hs) rfl)
            (useBools_nil _)))) hf1 (by simp [hkm, hsm, hvl, maxWidth] <;> omega)) ?_
    have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨km, false⟩,
      ⟨List.replicate (bitsOf version).length Mark.pub, false⟩, ⟨sm, false⟩]).flatten, false⟩
    refine WFP_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
      (by simp [hkm, hsm, hvl] <;> omega) hf2 (by decide) (by simp [sealMarks, maxWidth] <;> omega)) ?_
    have hf3 := hf2.push (n + 2) (Nat.le_refl _) ⟨(List.replicate 1 (sealMarks size)).flatten, false⟩
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push])) ?_
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
    refine WFP_openThen sigs _ _ _ _ _ _ (check_openBool sigs (by decide)
      (useBool_keep ((bool?_drop_of_ne _ _ _ (by simp)).trans ((bool?_drop_of_ne _ _ _ (by simp)).trans
        (bool?_push_self _ _ _))) rfl)
      (by simp [sealMarks, Mark.openable])) ?_
    intro b _
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
    refine WFP.done _ _ ⟨fun g hg => ?_, ((hf3.drop n).drop (n + 1)).drop (n + 2)⟩
    have e0 : g.id ≠ n := by omega
    have e1 : g.id ≠ n + 1 := by omega
    have e2 : g.id ≠ n + 2 := by omega
    simp only [bool?_push, bool?_drop, e0, e1, e2, if_false]
  · exact WFP.abort _ _

theorem sealScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (key state : BoolH) (size : Nat)
    (version : B8) (km sm : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hsn : state.id < n)
    (hk : c.bool? key = some ⟨km, false⟩) (hs : c.bool? state = some ⟨sm, false⟩)
    (hkm : km.length = 480) (hsm : sm.length = 8 * size)
    (hsig : sigs (sealName size) = some ⟨8 * (68 + size), sealMarks size⟩) :
    WF sigs c (sealScript n key state size version) :=
  (sealScript_wfp sigs c n key state size version km sm hf hkn hsn hk hs hkm hsm (fun _ _ => hsig)).wf

/-- What an open leaves: the handles below `n` as before, nothing defined from `n + 5` on, and,
when it returns a handle, that is `n + 4` holding the content (8·|ct| private bits, not once). -/
def OpenPost (c : Ctx) (n size : Nat) (c' : Ctx) (r : Option BoolH) : Prop :=
  (∀ g : BoolH, g.id < n → c'.bool? g = c.bool? g) ∧ Fresh c' (n + 5) ∧
    ∀ h, r = some h → h = ⟨n + 4⟩ ∧ c'.bool? ⟨n + 4⟩ = some ⟨List.replicate (8 * size) .never, false⟩

theorem openScript_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (key : BoolH) (version check ct : B8)
    (km : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hk : c.bool? key = some ⟨km, false⟩)
    (hkm : km.length = 480)
    (hsig' : 0 < ct.length → ct.length ≤ 16384 →
      sigs (openName ct.length) = some ⟨8 * (84 + ct.length), openMarks ct.length⟩) :
    WFP sigs (OpenPost c n ct.length) c (openScript n key version check ct) := by
  unfold openScript
  split
  · next hc =>
    obtain ⟨hv, hcl, h0, h1⟩ := hc
    have hsig := hsig' h0 h1
    have hvl := versionOk_length version hv
    simp only [openBlock, seqs_cons, seqs_nil]
    have hf1 := hf.push n (Nat.le_refl n) ⟨List.replicate (bitsOf (version ++ ct ++ check)).length .pub, false⟩
    refine WFP_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp [hvl, hcl, maxWidth] <;> omega)) ?_
    refine WFP_seq sigs _ _ _ _ (check_concat sigs
      (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans hk) rfl)
        (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl) (useBools_nil _))) hf1
      (by simp [hkm, hvl, hcl, maxWidth] <;> omega)) ?_
    have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨km, false⟩,
      ⟨List.replicate (bitsOf (version ++ ct ++ check)).length Mark.pub, false⟩]).flatten, false⟩
    refine WFP_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
      (by simp [hkm, hvl, hcl] <;> omega) hf2 (by decide) (by simp [openMarks, maxWidth] <;> omega)) ?_
    have hf3 := hf2.push (n + 2) (Nat.le_refl _) ⟨(List.replicate 1 (openMarks ct.length)).flatten, false⟩
    refine WFP_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (bool?_push_self _ _ _) rfl)
      (by simp [openMarks]) hf3 (by simp [maxWidth])) ?_
    have hf4 := hf3.push (n + 3) (Nat.le_refl _)
      ⟨((((List.replicate 1 (openMarks ct.length)).flatten).drop 0).take (8 - 0)), false⟩
    refine WFP_seq sigs _ _ _ _ (check_slice sigs
      (useBool_keep ((bool?_push_of_ne _ _ _ _ (by simp)).trans (bool?_push_self _ _ _)) rfl)
      (by simp [openMarks] <;> omega) hf4 (by simp [maxWidth] <;> omega)) ?_
    have hf5 := hf4.push (n + 4) (Nat.le_refl _)
      ⟨((((List.replicate 1 (openMarks ct.length)).flatten).drop 8).take (8 + 8 * ct.length - 8)), false⟩
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push])) ?_
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
    refine WFP_openThen sigs _ _ _ _ _ _ (check_openBool sigs (by decide)
      (useBool_keep ((bool?_drop_of_ne _ _ _ (by simp)).trans ((bool?_drop_of_ne _ _ _ (by simp)).trans
        ((bool?_drop_of_ne _ _ _ (by simp)).trans ((bool?_push_of_ne _ _ _ _ (by simp)).trans
          (bool?_push_self _ _ _))))) rfl)
      (by simp [openMarks, Mark.openable])) ?_
    intro b _
    have hlow : ∀ g : BoolH, g.id < n → g.id ≠ n ∧ g.id ≠ n + 1 ∧ g.id ≠ n + 2 ∧ g.id ≠ n + 3 ∧ g.id ≠ n + 4 :=
      fun g hg => ⟨by omega, by omega, by omega, by omega, by omega⟩
    unfold openRest
    split
    · refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
      refine WFP.done _ _ ⟨fun g hg => ?_, (((hf5.drop n).drop (n + 1)).drop (n + 2)).drop (n + 3),
        fun h hh => ⟨(Option.some.inj hh).symm, ?_⟩⟩
      · obtain ⟨e0, e1, e2, e3, e4⟩ := hlow g hg
        simp only [bool?_push, bool?_drop, e0, e1, e2, e3, e4, if_false]
      · simp [bool?_push, bool?_drop, openMarks]
    · refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
      refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
      refine WFP.done _ _ ⟨fun g hg => ?_, ((((hf5.drop n).drop (n + 1)).drop (n + 2)).drop (n + 3)).drop (n + 4),
        fun h hh => by cases hh⟩
      obtain ⟨e0, e1, e2, e3, e4⟩ := hlow g hg
      simp only [bool?_push, bool?_drop, e0, e1, e2, e3, e4, if_false]
  · exact WFP.abort _ _

theorem openScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (key : BoolH) (version check ct : B8)
    (km : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hk : c.bool? key = some ⟨km, false⟩)
    (hkm : km.length = 480)
    (hsig : sigs (openName ct.length) = some ⟨8 * (84 + ct.length), openMarks ct.length⟩) :
    WF sigs c (openScript n key version check ct) :=
  (openScript_wfp sigs c n key version check ct km hf hkn hk hkm (fun _ _ => hsig)).wf

/-! ## T3: disclosure against any adversary -/

section Disclosure

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

theorem keyScript_silent (n slot : Nat) : Silent (keyScript n slot) :=
  Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])

/-- **T3 for `Contacts.key`.** Nothing is released, to either party. -/
theorem key_disclosure (n slot : Nat) :
    (withAdv E me adv (keyScript n slot) σ I vD).viewD = [] ∧
      (withAdv E me adv (keyScript n slot) σ I vD).viewH = [] :=
  silent_view E me adv _ (keyScript_silent n slot) σ I vD

/-- **T3 for `Contacts.seal`.** At most one release, labelled `sealedBlob`: the `contact-seal`
kernel's output (ciphertext ‖ check) on the values of the key handle, the public version and the
state handle. -/
theorem seal_disclosure (hE : Loaded E) (n : Nat) (key state : BoolH) (size : Nat) (version : B8)
    (k s : Bits) (hkn : key.id < n) (hsn : state.id < n) (hk : I.bools key.id = some k)
    (hs : I.bools state.id = some s) :
    (withAdv E me adv (sealScript n key state size version) σ I vD).viewD <+:
      [⟨sealedBlob, .bits (bitsOf (kernelOut (HybridKernel.contactSeal size) (bytesOf (k ++ (bitsOf version ++ s)))))⟩] := by
  unfold sealScript
  split
  · next hc =>
    obtain ⟨-, h0, h1⟩ := hc
    have hc := hE.sealing size h0 h1
    apply viewD_seqs E me adv _ σ _ _ (by simp [sealBlock, plain]) I vD
    intro I' hI'
    have hkn0 : key.id ≠ n := by omega
    have hsn0 : state.id ≠ n := by omega
    simp [sealBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool,
      hk, hs, hkn0, hsn0, hc, kernelCircuit] at hI'
    by_cases hlen : k.length + (8 * version.length + s.length) = 8 * (68 + size)
    · simp only [hlen, if_true] at hI'
      simp at hI'
      subst hI'
      apply viewD_openThen E me adv _ _ _ σ _ vD _ []
      · simp [runCopies_one, hlen]
      · exact silent_prefix E me adv _ (Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])) _ _ _ _
    · simp [hlen] at hI'
  · simp [withAdv]

/-- **T3 for `Contacts.open`.** At most one release, labelled `blobAccepted`: the first byte of the
`contact-open` kernel's output (its `accepted` field) on the key handle's value and the public
version, ciphertext and check value. The content never leaves the engines. -/
theorem open_disclosure (hE : Loaded E) (n : Nat) (key : BoolH) (version check ct : B8) (k : Bits)
    (hkn : key.id < n) (hk : I.bools key.id = some k) :
    (withAdv E me adv (openScript n key version check ct) σ I vD).viewD <+:
      [⟨blobAccepted, .bits ((bitsOf (kernelOut (HybridKernel.contactOpen ct.length)
        (bytesOf (k ++ bitsOf (version ++ ct ++ check))))).take 8)⟩] := by
  unfold openScript
  split
  · next hc =>
    obtain ⟨-, -, h0, h1⟩ := hc
    have hc := hE.opening ct.length h0 h1
    apply viewD_seqs E me adv _ σ _ _ (by simp [openBlock, plain]) I vD
    intro I' hI'
    have hkn0 : key.id ≠ n := by omega
    simp [openBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool,
      hk, hkn0, hc, kernelCircuit] at hI'
    by_cases hlen : k.length + (8 * version.length + (8 * ct.length + 8 * check.length)) = 8 * (84 + ct.length)
    · simp [hlen, runCopies_one] at hI'
      by_cases hc1 : 8 ≤ 8 * (kernelOut (HybridKernel.contactOpen ct.length)
          (bytesOf (k ++ (bitsOf version ++ (bitsOf ct ++ bitsOf check))))).length
      · by_cases hc2 : 8 + 8 * ct.length ≤ 8 * (kernelOut (HybridKernel.contactOpen ct.length)
            (bytesOf (k ++ (bitsOf version ++ (bitsOf ct ++ bitsOf check))))).length
        · simp [hc1, hc2] at hI'
          subst hI'
          apply viewD_openThen E me adv _ _ _ σ _ vD _ []
          · simp
          · unfold openRest
            split
            · exact silent_prefix E me adv _ (Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])) _ _ _ _
            · exact silent_prefix E me adv _ (Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])) _ _ _ _
        · simp [hc1, hc2] at hI'
      · simp [hc1] at hI'
    · simp [hlen] at hI'
  · simp [withAdv]

/-- **What `open_disclosure` releases**, for a key of 60 bytes and well-formed arguments: the bits of
the byte `contactMask K check`, which is 255 when `check` is this key's check value and 0
otherwise (`contactMask_accept_iff`). -/
theorem open_released_byte (K version check ct : B8) (hK : K.length = 60) (hargs : openArgsOk version check ct) :
    (bitsOf (kernelOut (HybridKernel.contactOpen ct.length)
      (bytesOf (bitsOf K ++ bitsOf (version ++ ct ++ check))))).take 8 =
      bitsOf [HybridKernel.contactMask K check] := by
  obtain ⟨hv, hc, -, -⟩ := hargs
  rw [← bitsOf_append, bytesOf_bitsOf, List.append_assoc version,
    kernelOut_open ct.length K version ct check hK (versionOk_length _ hv) rfl hc, bitsOf_cons,
    List.take_left' (length_bitsOfByte _)]
  simp

end Disclosure

/-! ## T4-CONTACT: two honest parties -/

section Honest

variable (E : Env) (σA σB : Store)

def keyRest (n : Nat) : Script BoolH :=
  seqs [.concat ⟨n + 2⟩ [⟨n⟩, ⟨n + 1⟩], .run ⟨n + 3⟩ keyName 1 ⟨n + 2⟩] (.done ⟨n + 3⟩)

theorem keyScript_eq (n slot : Nat) :
    keyScript n slot = seq (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false slot) (keyRest n) := rfl

/-- **T4-CONTACT for `Contacts.key`.** Two honest parties with shares `a` (A) and `b` (B) below
the modulus: the key handle `n + 3` holds `contactKey_spec`'s block, SHA-256's first 28 bytes of
"CONTACT_STATE_KEY_V1" ‖ le32((a + b) mod (2^255 − 19)) after 32 zero bytes; handles below `n`
are untouched. -/
theorem key_honest (hE : Loaded E) (I : Ideal) (n slotA slotB : Nat) (a b : B8)
    (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus)
    (hσA : σA.bits slotA = bitsOf a) (hσB : σB.bits slotB = bitsOf b) :
    (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).result = some (⟨n + 3⟩, ⟨n + 3⟩) ∧
    (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).ideal.bools (n + 3) =
      some (bitsOf (keyBlock a b)) ∧
    ∀ j, j < n → (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).ideal.bools j = I.bools j := by
  have hfA : fill E.hash .a σA (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false slotA) =
      some (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false (bitsOf a)) := by simp [fill, hσA, ha]
  have hfB : fill E.hash .b σB (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false slotB) =
      some (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false (bitsOf b)) := by simp [fill, hσB, hb]
  have hst : idealStep E .a (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false (bitsOf a))
      (Wire.part (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false (bitsOf b))) I =
      some ((I.setBool ⟨n⟩ (bitsOf a)).setBool ⟨n + 1⟩ (bitsOf b), none, none) := by
    simp [idealStep, Wire.part, ha, hb]
  obtain ⟨r1, d1⟩ := jointRun_seq E (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false slotA)
    (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 256 true false slotB) (keyRest n) (keyRest n) σA σB I _ _ _ rfl hfA hfB hst
  rw [keyScript_eq, keyScript_eq, r1, d1]
  unfold keyRest
  have hlen : 8 * a.length + 8 * b.length = 8 * 64 := by omega
  cases hI : runPlain E [.concat ⟨n + 2⟩ [⟨n⟩, ⟨n + 1⟩], .run ⟨n + 3⟩ keyName 1 ⟨n + 2⟩]
      ((I.setBool ⟨n⟩ (bitsOf a)).setBool ⟨n + 1⟩ (bitsOf b)) with
  | none =>
    simp [runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, hE.key, kernelCircuit, hlen] at hI
  | some I2 =>
    obtain ⟨r2, d2⟩ := jointRun_seqs E (.done (⟨n + 3⟩ : BoolH)) (.done (⟨n + 3⟩ : BoolH)) σA σB _
      (by simp [plain]) _ I2 hI
    rw [r2, d2]
    simp [runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, hE.key, kernelCircuit, hlen] at hI
    subst hI
    refine ⟨rfl, ?_, ?_⟩
    · simp [jointRun, runCopies_one, ha, hb, bytesOf_bitsOf_append, kernelOut_key a b ha hb haB hbB]
    · intro j hj
      have h1 : j ≠ n + 3 := by omega
      have h2 : j ≠ n + 2 := by omega
      have h3 : j ≠ n + 1 := by omega
      have h4 : j ≠ n := by omega
      simp [jointRun, h1, h2, h3, h4]

/-- **T4-CONTACT for `Contacts.seal`.** Two honest parties, the key handle holding a 60-byte block
`K` and the state handle a state `S`: both return checkOf K ‖ ctrOf K version S
(`contactSeal_spec`: the pad block for the reserved version, and AES-CTR of the state under the
block's key and IV with `version` as the record sequence). -/
theorem seal_honest (hE : Loaded E) (I : Ideal) (n : Nat) (key state : BoolH) (size : Nat) (version K S : B8)
    (hkn : key.id < n) (hsn : state.id < n) (hK : K.length = 60) (hS : S.length = size)
    (h0 : 0 < size) (h1 : size ≤ 16384) (hv : versionOk version = true)
    (hk : I.bools key.id = some (bitsOf K)) (hs : I.bools state.id = some (bitsOf S)) :
    (jointRun E (sealScript n key state size version) (sealScript n key state size version) σA σB I).result =
      some (sealed K version S, sealed K version S) := by
  have hvl := versionOk_length version hv
  have hc := hE.sealing size h0 h1
  have hkn0 : key.id ≠ n := by omega
  have hsn0 : state.id ≠ n := by omega
  have hlen : 8 * K.length + (8 * version.length + 8 * S.length) = 8 * (68 + size) := by omega
  unfold sealScript
  rw [if_pos ⟨hv, h0, h1⟩]
  cases hI : runPlain E (sealBlock n key state size version) I with
  | none =>
    simp [sealBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool,
      hk, hs, hkn0, hsn0, hc, kernelCircuit, hlen] at hI
  | some I' =>
    rw [(jointRun_seqs E _ _ σA σB _ (by simp [sealBlock, plain]) I I' hI).1]
    simp [sealBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool,
      hk, hs, hkn0, hsn0, hc, kernelCircuit, hlen] at hI
    subst hI
    rw [(jointRun_openThen E _ _ _ _ σA σB _ (bitsOf (HybridKernel.ctrOf K version S ++ HybridKernel.checkOf K))
      (by simp [runCopies_one, hlen, bytesOf_bitsOf_append, kernelOut_seal size K version S hK hvl hS])).1]
    rw [(jointRun_seqs E _ _ σA σB [.freeBool ⟨n + 2⟩] (by simp [plain]) _ _ (runPlain_free _ _ _)).1]
    have hct : (HybridKernel.ctrOf K version S).length = size := by
      rw [HybridKernel.ctrOf_length K version S hK, hS]
    simp [jointRun, sealReply, sealed, bytesOf_bitsOf_append, List.drop_left' hct, List.take_left' hct]

/-- **T4-CONTACT for `Contacts.open`.** Two honest parties, the key handle holding a 60-byte block
`K`. If the check value is `checkOf K`, both return the new handle `n + 4`, which holds
ctrOf K version ct (`contactOpen_spec`, `contactOpen_accepted_iff`). Otherwise both return
`none` and the content handle is freed: nothing of the content remains or was released. -/
theorem open_honest (hE : Loaded E) (I : Ideal) (n : Nat) (key : BoolH) (version check ct K : B8)
    (hkn : key.id < n) (hK : K.length = 60) (hk : I.bools key.id = some (bitsOf K))
    (hargs : openArgsOk version check ct) :
    (check = HybridKernel.checkOf K →
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).result =
        some (some ⟨n + 4⟩, some ⟨n + 4⟩) ∧
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).ideal.bools
        (n + 4) = some (bitsOf (HybridKernel.ctrOf K version ct))) ∧
    (check ≠ HybridKernel.checkOf K →
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).result =
        some (none, none) ∧
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).ideal.bools
        (n + 4) = none) := by
  obtain ⟨hv, hcl, h0, h1⟩ := hargs
  have hvl := versionOk_length version hv
  have hc := hE.opening ct.length h0 h1
  have hkn0 : key.id ≠ n := by omega
  have hlen : 8 * K.length + (8 * version.length + (8 * ct.length + 8 * check.length)) = 8 * (84 + ct.length) := by
    omega
  have hO := kernelOut_open ct.length K version ct check hK hvl rfl hcl
  have hbytes : bytesOf (bitsOf K ++ (bitsOf version ++ (bitsOf ct ++ bitsOf check))) = K ++ (version ++ (ct ++ check)) := by
    simp [bytesOf_bitsOf_append]
  -- the content's length, accepted or not
  have hrel : (ByteAuth.release ByteAuth.concrete (HybridKernel.contactMask K check) (HybridKernel.ctrOf K version ct)).length =
      ct.length := by
    unfold HybridKernel.contactMask
    split
    · rw [ByteAuth.release_accept, HybridKernel.ctrOf_length K version ct hK]
    · rw [ByteAuth.release_reject, List.length_replicate, HybridKernel.ctrOf_length K version ct hK]
  have hc1 : 8 ≤ 8 * (kernelOut (HybridKernel.contactOpen ct.length)
      (bytesOf (bitsOf K ++ (bitsOf version ++ (bitsOf ct ++ bitsOf check))))).length := by
    rw [hbytes, hO]; simp [hrel] <;> omega
  have hc2 : 8 + 8 * ct.length ≤ 8 * (kernelOut (HybridKernel.contactOpen ct.length)
      (bytesOf (bitsOf K ++ (bitsOf version ++ (bitsOf ct ++ bitsOf check))))).length := by
    rw [hbytes, hO]; simp [hrel]; omega
  unfold openScript
  rw [if_pos ⟨hv, hcl, h0, h1⟩]
  cases hI : runPlain E (openBlock n key version check ct) I with
  | none =>
    simp [openBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool,
      hk, hkn0, hc, kernelCircuit, hlen, runCopies_one, hc1, hc2] at hI
  | some I' =>
    have r1 := jointRun_seqs E (openThen ⟨n + 3⟩ blobAccepted (openRest n))
      (openThen ⟨n + 3⟩ blobAccepted (openRest n)) σA σB _ (by simp [openBlock, plain]) I I' hI
    rw [r1.1, r1.2]
    simp [openBlock, runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool,
      hk, hkn0, hc, kernelCircuit, hlen, runCopies_one, hc1, hc2] at hI
    subst hI
    have hacc := open_released_byte K version check ct hK ⟨hv, hcl, h0, h1⟩
    rw [(jointRun_openThen E ⟨n + 3⟩ blobAccepted (openRest n) (openRest n) σA σB _
        (bitsOf [HybridKernel.contactMask K check]) (by simp; simpa using hacc)).1,
      (jointRun_openThen E ⟨n + 3⟩ blobAccepted (openRest n) (openRest n) σA σB _
        (bitsOf [HybridKernel.contactMask K check]) (by simp; simpa using hacc)).2]
    have hct := HybridKernel.ctrOf_length K version ct hK
    refine ⟨fun hcheck => ?_, fun hcheck => ?_⟩
    · have hm : HybridKernel.contactMask K check = 255 := (HybridKernel.contactMask_accept_iff K check).mpr hcheck
      unfold openRest
      rw [if_pos (by rw [hm])]
      rw [(jointRun_seqs E (Script.done (some (⟨n + 4⟩ : BoolH))) (Script.done (some (⟨n + 4⟩ : BoolH)))
          σA σB [.freeBool ⟨n + 3⟩] (by simp [plain]) _ _ (runPlain_free _ _ _)).1,
        (jointRun_seqs E (Script.done (some (⟨n + 4⟩ : BoolH))) (Script.done (some (⟨n + 4⟩ : BoolH)))
          σA σB [.freeBool ⟨n + 3⟩] (by simp [plain]) _ _ (runPlain_free _ _ _)).2]
      refine ⟨rfl, ?_⟩
      have hO' : kernelOut (HybridKernel.contactOpen ct.length) (K ++ (version ++ (ct ++ check))) =
          255 :: HybridKernel.ctrOf K version ct := by
        rw [hO, hm, ByteAuth.release_accept]
      simp [jointRun, Ideal.dropBool, hbytes, hO', List.take_of_length_le, hct]
    · have hm : HybridKernel.contactMask K check = 0 := HybridKernel.contactMask_reject K check
        (fun h => hcheck ((HybridKernel.contactMask_accept_iff K check).mp h))
      unfold openRest
      rw [if_neg (by rw [hm]; decide)]
      rw [(jointRun_seqs E (Script.done (none : Option BoolH)) (Script.done (none : Option BoolH))
          σA σB [.freeBool ⟨n + 3⟩, .freeBool ⟨n + 4⟩] (by simp [plain]) _ _ (runPlain_free2 _ _ _ _)).1,
        (jointRun_seqs E (Script.done (none : Option BoolH)) (Script.done (none : Option BoolH))
          σA σB [.freeBool ⟨n + 3⟩, .freeBool ⟨n + 4⟩] (by simp [plain]) _ _ (runPlain_free2 _ _ _ _)).2]
      refine ⟨rfl, ?_⟩
      simp [jointRun, Ideal.dropBool]

/-- **Open after seal (T4-CONTACT).** Opening the check value and ciphertext that an honest seal of
`S` under the block `K` and `version` produced, under a key handle holding the same `K`, accepts
and gives a handle holding `S` (`contact_round_trip`, through the model). -/
theorem open_after_seal (hE : Loaded E) (I : Ideal) (n : Nat) (key : BoolH) (version K S : B8)
    (hkn : key.id < n) (hK : K.length = 60) (hk : I.bools key.id = some (bitsOf K))
    (hv : versionOk version = true) (hS0 : 0 < S.length) (hS1 : S.length ≤ 16384) :
    (jointRun E (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16))
        (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16)) σA σB I).result =
      some (some ⟨n + 4⟩, some ⟨n + 4⟩) ∧
    (jointRun E (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16))
        (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16)) σA σB I).ideal.bools
        (n + 4) = some (bitsOf S) := by
  have hcl := checkOf_length K hK
  have ht : (sealed K version S).take 16 = HybridKernel.checkOf K := by simp [sealed, List.take_left' hcl]
  have hd : (sealed K version S).drop 16 = HybridKernel.ctrOf K version S := by simp [sealed, List.drop_left' hcl]
  have hct := HybridKernel.ctrOf_length K version S hK
  rw [ht, hd]
  have h := (open_honest E σA σB hE I n key version (HybridKernel.checkOf K) (HybridKernel.ctrOf K version S) K
    hkn hK hk ⟨hv, hcl, by omega, by omega⟩).1 rfl
  rw [HybridKernel.ctrOf_involutive K version S hK] at h
  exact h

/-- **T4-CONTACT end to end.** Session 1 (stores σ, ideal state I₁): the key from the shares `a`
(A) and `b` (B), handles from `n`; then the seal, handles from `n + 4`, of the state `S` held at
handle `st`. Session 2 (stores τ, ANY ideal state I₂, handles from `m`): the key from the same
shares, then the open of the sealed blob. The seal returns checkOf K ‖ ctrOf K version S for
K = `keyBlock a b`, and the open accepts with its handle holding `S`. -/
theorem key_seal_open (hE : Loaded E) (τA τB : Store) (I₁ I₂ : Ideal) (n m slotA slotB slotA' slotB' : Nat)
    (st : BoolH) (a b version S : B8) (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus)
    (hσA : σA.bits slotA = bitsOf a) (hσB : σB.bits slotB = bitsOf b)
    (hτA : τA.bits slotA' = bitsOf a) (hτB : τB.bits slotB' = bitsOf b)
    (hst : st.id < n) (hS : I₁.bools st.id = some (bitsOf S)) (hv : versionOk version = true)
    (hS0 : 0 < S.length) (hS1 : S.length ≤ 16384) :
    (jointRun E (sealScript (n + 4) ⟨n + 3⟩ st S.length version) (sealScript (n + 4) ⟨n + 3⟩ st S.length version)
        σA σB (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I₁).ideal).result =
      some (sealed (keyBlock a b) version S, sealed (keyBlock a b) version S) ∧
    (jointRun E
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        τA τB (jointRun E (keyScript m slotA') (keyScript m slotB') τA τB I₂).ideal).result =
      some (some ⟨m + 4 + 4⟩, some ⟨m + 4 + 4⟩) ∧
    (jointRun E
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        τA τB (jointRun E (keyScript m slotA') (keyScript m slotB') τA τB I₂).ideal).ideal.bools (m + 4 + 4) =
      some (bitsOf S) := by
  obtain ⟨-, k1, k1o⟩ := key_honest E σA σB hE I₁ n slotA slotB a b ha hb haB hbB hσA hσB
  obtain ⟨-, k2, -⟩ := key_honest E τA τB hE I₂ m slotA' slotB' a b ha hb haB hbB hτA hτB
  have hK := keyBlock_length a b
  refine ⟨?_, open_after_seal E τA τB hE _ (m + 4) ⟨m + 3⟩ version (keyBlock a b) S (by simp) hK k2 hv hS0 hS1⟩
  exact seal_honest E σA σB hE _ (n + 4) ⟨n + 3⟩ st S.length version (keyBlock a b) S (by simp) (by omega) hK rfl
    hS0 hS1 hv k1 (by rw [k1o st.id hst]; exact hS)

end Honest

/-! ## The signatures the shell checks against, from `Loaded` -/

theorem Loaded.sigs_key {E : Env} (hE : Loaded E) : E.sigs keyName = some ⟨512, keyMarks⟩ := by
  simp [Env.sigs, hE.key, kernelCircuit]

theorem Loaded.sigs_seal {E : Env} (hE : Loaded E) (size : Nat) (h0 : 0 < size) (h1 : size ≤ 16384) :
    E.sigs (sealName size) = some ⟨8 * (68 + size), sealMarks size⟩ := by
  simp [Env.sigs, hE.sealing size h0 h1, kernelCircuit]

theorem Loaded.sigs_open {E : Env} (hE : Loaded E) (size : Nat) (h0 : 0 < size) (h1 : size ≤ 16384) :
    E.sigs (openName size) = some ⟨8 * (84 + size), openMarks size⟩ := by
  simp [Env.sigs, hE.opening size h0 h1, kernelCircuit]

end TlsMpc.Node.Flows.Contacts
