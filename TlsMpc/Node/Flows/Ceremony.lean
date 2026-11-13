import TlsMpc.Node.Flows.ContactsBase
import TlsMpc.CeremonyKernels

/-!
# `Ceremony.secrets`, `Ceremony.register`: the registration ceremony as scripts (ops 80, 81)

REORGANIZATION_PLAN.md stage S16 (`Flows/Ceremony`, T4-CEREMONY). Replaces
`handshake_backend/EmpHybridWork/service_kernels.h` `ceremony_secrets` (689-701) and
`ceremony_register` (705-713) with the dispatch of `tls_worker_v3.cpp` ops 80 and 81 (lines
202-208). The kernels are the existing `ceremony-secrets` and `ceremony-register-ctr SIZE PAYLOAD
AUTH TAIL RECOVERY` (`TlsMpc/CeremonyKernels.lean`, theorems in `TlsMpc/CeremonyProofs.lean`); no
kernel is new.

WHAT THE C++ DOES.
  op 80 `ceremony_secrets()`: once per session (`!ceremony_password.size()`). Each party draws its
    own seed (18 bytes), password mask (22) and recovery half (32) and enters them as its private
    inputs (`input_private(ALICE, …)`, `input_private(BOB, …)`); `ceremony-secrets` on seedA, seedB,
    maskA, maskB, recoveryA, recoveryB; OPENS `masked` (= password ⊕ maskA ⊕ maskB) to both; keeps
    `password` and `recovery` as wires. Reply, this party's XOR shares: A: maskA ⊕ masked ‖
    recoveryA; B: maskB ‖ recoveryB (so the password shares XOR to the password, the recovery shares
    to the recovery password).
  op 81 `ceremony_register(payloadAt, authAt, recoveryAt, mask, tail, frame)`: once per session
    (`ceremony_sealed`), after op 80; a request buffer (frame, mask) whose sealer is
    `ceremony-register-ctr |frame| payloadAt authAt |tail| recoveryAt` with the extra input `secrets`
    = tail (public, 0..2 bytes) ‖ password ‖ recovery. The record is sealed later by the record
    layer (`seal_application` with a sealer).

THE SCRIPTS (Boolean handles from `n`; every opening labelled by its reveal kind).
  `secretsScript n seedSlot maskSlot recoverySlot` (op 80): three `boolInputBoth` (each party's own
    seed, mask, recovery half from its store slots; A's at the even id, B's at the odd one), the
    concatenation in the kernel's input order, `ceremony-secrets`, the three output fields sliced
    (password `n + 8`, recovery `n + 9`, masked `n + 10`), the inputs and the bundles freed, OPEN
    masked (label `maskedPassword`, kind 70), free it. Returns the two kept handles and the opened
    22 bytes. This party's shares are then computed by the controller from its own mask and
    recovery half and the opened value (`shareOf`, as the C++'s reply).
  `registerScript n password recovery tail` (op 81's engine part): secrets := tail (public bits)
    ‖ password ‖ recovery (handle `n + 1`); the password and recovery handles are freed (the request
    owns the copy; a second op 81 finds no secrets: the C++'s `ceremony_sealed`). The record seal is
    S13's `Send.requestCtrScript` with the name `registerName` (the request is kept as a
    `SendBackend.Request`; `Flows/Select.lean`), then S12's `Tls.tagScript`.

DEVIATIONS FROM THE C++ (both parties change together; the legacy library keeps its own).
  * The randomness is drawn on the Lean side (rule 5, `Channels.random`), not by `emp::PRG`.
  * The plan (4.2 row 4) names `openBoolTo` replies; the kernel declares `masked` PUBLIC (`pub`), and
    the shell's `check` allows `openBoolTo` only on bits marked for that recipient, so the script
    opens it to both, as the C++ does. B learns masked ⊕ maskB = password ⊕ maskA, uniform for a
    uniform maskA (`masked_hides_list`); an `openBoolTo A` variant needs a kernel whose `masked` is
    marked `toA` (a re-lowering; listed in S16_NOTES.md, not needed for the disclosure statement).
  * Op 81 checks `find`'s ranges at registration time (`registerOk`; the C++ failed at seal time) and
    frees the password and recovery handles (the C++ kept the wires and refused a second op 81).
  * The legacy C++ needed the legacy service's upgrade state (`public_receive`); the script does not.

PROVED HERE: `secrets_reveals` (op 80 releases only under `maskedPassword`), `register_reveals`
(op 81's engine part releases nothing), their `viewD` forms against any adversary; `secretsScript_wf`,
`registerScript_wf` (well formed from any context in which the ids from `n` are fresh, the kernel's
signature is as declared and, for op 81, the two handles are live with op 80's marks);
`masked_hides_list` (7.0's bijection form: for every password and every value of the other party's
mask, each opened value comes from exactly one honest mask); `shares_xor` (the two parties' replies
XOR to password ‖ recovery). The honest runs are in `Flows/CeremonyRun.lean`.
-/

namespace TlsMpc.Node.Flows.Ceremony

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts

/-! ## Sizes and names -/

/-- Each party's seed (`TlsMpc.Ceremony.seedBytes`). -/
def seedBytes : Nat := 18
/-- The account password (`TlsMpc.Ceremony.passwordBytes`). -/
def passwordBytes : Nat := 22
/-- The recovery password (`TlsMpc.Ceremony.recoveryBytes`). -/
def recoveryBytes : Nat := 32

theorem sizes_eq : seedBytes = TlsMpc.Ceremony.seedBytes ∧ passwordBytes = TlsMpc.Ceremony.passwordBytes ∧
    recoveryBytes = TlsMpc.Ceremony.recoveryBytes := ⟨rfl, rfl, rfl⟩

/-- The input bundle's byte length: seedA, seedB, maskA, maskB, recoveryA, recoveryB. -/
def inputBytes : Nat := 2 * seedBytes + 2 * passwordBytes + 2 * recoveryBytes

/-- The output bundle's byte length: password, recovery, masked. -/
def outputBytes : Nat := 2 * passwordBytes + recoveryBytes

def secretsName : Bytes := ascii "ceremony-secrets"

/-- `ceremony-register-ctr SIZE PAYLOAD AUTH TAIL RECOVERY` (`CeremonyKernel.find`; the C++'s
`buffer.sealer`). -/
def registerName (size payloadAt authAt tail recoveryAt : Nat) : Bytes :=
  ascii ("ceremony-register-ctr " ++ toString size ++ " " ++ toString payloadAt ++ " " ++ toString authAt ++ " " ++
    toString tail ++ " " ++ toString recoveryAt)

/-- `find`'s conditions for `ceremony-register-ctr` (and the C++'s `!frame.empty()`). -/
def registerOk (size payloadAt authAt tail recoveryAt : Nat) : Bool :=
  0 < size && size ≤ 16384 && 6 ≤ payloadAt && tail ≤ 2 &&
    BundleKernel.slotsOk size payloadAt [(authAt, 32), (recoveryAt, 44)]

/-- The output marks of `ceremony-secrets` (`CeremonyKernel.ceremonySecrets`: password and recovery
private, masked public). -/
def secretsMarks : List Mark :=
  List.replicate (8 * passwordBytes) .never ++ List.replicate (8 * recoveryBytes) .never ++
    List.replicate (8 * passwordBytes) .pub

/-! ## Op 80 -/

/-- The three inputs: each party's seed, mask and recovery half (A's at `n`, `n + 2`, `n + 4`; B's
at `n + 1`, `n + 3`, `n + 5`), private, not once. -/
def inputBlock (n seedSlot maskSlot recoverySlot : Nat) : List Instr :=
  [.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * seedBytes) false false seedSlot,
   .boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ (8 * passwordBytes) false false maskSlot,
   .boolInputBoth ⟨n + 4⟩ ⟨n + 5⟩ (8 * recoveryBytes) false false recoverySlot]

/-- The kernel and the slices (handles `n + 6 … n + 10`), the inputs and bundles freed. -/
def kernelBlock (n : Nat) : List Instr :=
  [.concat ⟨n + 6⟩ [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩],
   .run ⟨n + 7⟩ secretsName 1 ⟨n + 6⟩,
   .slice ⟨n + 8⟩ ⟨n + 7⟩ 0 (8 * passwordBytes),
   .slice ⟨n + 9⟩ ⟨n + 7⟩ (8 * passwordBytes) (8 * (passwordBytes + recoveryBytes)),
   .slice ⟨n + 10⟩ ⟨n + 7⟩ (8 * (passwordBytes + recoveryBytes)) (8 * outputBytes),
   .freeBool ⟨n⟩, .freeBool ⟨n + 1⟩, .freeBool ⟨n + 2⟩, .freeBool ⟨n + 3⟩, .freeBool ⟨n + 4⟩,
   .freeBool ⟨n + 5⟩, .freeBool ⟨n + 6⟩, .freeBool ⟨n + 7⟩]

/-- What op 80 leaves: the password and the recovery password (kept in the engines) and the opened
masked password. -/
structure Made where
  password : BoolH
  recovery : BoolH
  masked : B8

/-- After the opening of `masked`. -/
def afterMasked (n : Nat) (out : Bits) : Script Made :=
  seqs [.freeBool ⟨n + 10⟩]
    (if (bytesOf out).length = passwordBytes then .done ⟨⟨n + 8⟩, ⟨n + 9⟩, bytesOf out⟩
     else .abort "ceremony secrets shape")

/-- **Op 80's engine part.** Ids `n … n + 10`; `n + 8`, `n + 9` are kept. -/
def secretsScript (n seedSlot maskSlot recoverySlot : Nat) : Script Made :=
  seqs (inputBlock n seedSlot maskSlot recoverySlot ++ kernelBlock n)
    (openThen ⟨n + 10⟩ Label.maskedPassword (afterMasked n))

/-- **This party's XOR shares** (the C++'s reply): the password share (A: its mask ⊕ the opened
value; B: its mask) ‖ its own recovery half. -/
def shareOf (me : Party) (mask recovery masked : B8) : B8 :=
  (match me with
   | .a => List.zipWith (· ^^^ ·) mask masked
   | .b => mask) ++ recovery

/-! ## Op 81 -/

/-- The secrets input `tail ‖ password ‖ recovery` (handle `n + 1`; `n` holds the public tail when
there is one); the password and recovery handles are freed. -/
def registerBlock (n : Nat) (password recovery : BoolH) (tail : B8) : List Instr :=
  if tail = [] then [.concat ⟨n + 1⟩ [password, recovery], .freeBool password, .freeBool recovery]
  else [.boolPublic ⟨n⟩ (bitsOf tail), .concat ⟨n + 1⟩ [⟨n⟩, password, recovery], .freeBool ⟨n⟩,
    .freeBool password, .freeBool recovery]

/-- **Op 81's engine part.** Ids `n`, `n + 1`; returns the secrets handle the request seal reads. -/
def registerScript (n : Nat) (password recovery : BoolH) (tail : B8) : Script BoolH :=
  if tail.length ≤ 2 then seqs (registerBlock n password recovery tail) (.done ⟨n + 1⟩)
  else .abort "ceremony register tail"

/-! ## The session state of the two operations -/

/-- The ceremony's handles between ops 80 and 81. `made`: op 80 ran (once per session, the C++'s
`!ceremony_password.size()`); `secrets`: the password and recovery handles until op 81 consumes
them (once per session, `ceremony_sealed`). -/
structure State where
  made : Bool := false
  secrets : Option (BoolH × BoolH) := none

/-- Op 80 on the state: refused when it ran before. -/
def secretsStep (st : State) (n seedSlot maskSlot recoverySlot : Nat) : Script Made :=
  if st.made then .abort "ceremony secrets unavailable" else secretsScript n seedSlot maskSlot recoverySlot

/-- The state after op 80. -/
def State.afterSecrets (m : Made) : State := { made := true, secrets := some (m.password, m.recovery) }

/-- Op 81 on the state: refused without op 80's handles (before op 80, or a second time). -/
def registerStep (st : State) (n : Nat) (tail : B8) : Script BoolH :=
  match st.secrets with
  | some (p, r) => registerScript n p r tail
  | none => .abort "ceremony register unavailable"

/-- The state after op 81: the secrets are gone. -/
def State.afterRegister (st : State) : State := { st with secrets := none }

/-! ## The reveal list -/

def secretsKinds : List TlsMpc.Node.RevealKind := [.maskedPassword]

theorem plain_none (i : Instr) (h : plain i = true) : i.label? = none := by
  cases i <;> simp_all [plain, InstrP.label?]

theorem inputBlock_none (n a b c : Nat) : ∀ i ∈ inputBlock n a b c, i.label? = none := by
  intro i hi
  simp only [inputBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem kernelBlock_plain (n : Nat) : ∀ i ∈ kernelBlock n, plain i = true := by
  intro i hi
  simp only [kernelBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem afterMasked_silent (n : Nat) (out : Bits) : Silent (afterMasked n out) := by
  unfold afterMasked
  refine Silent.seqs ?_ _ (fun i hi => by simp at hi; subst hi; rfl)
  split
  · exact Silent.done _
  · exact Silent.abort _

/-- **T3 for op 80**: every release is labelled `maskedPassword`. -/
theorem secrets_reveals (n seedSlot maskSlot recoverySlot : Nat) :
    Reveals secretsKinds (secretsScript n seedSlot maskSlot recoverySlot) := by
  unfold secretsScript
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .maskedPassword) (by simp [secretsKinds]) rfl)
    (fun out => (afterMasked_silent n out).reveals _)) _ (fun i hi => ?_)
  rcases List.mem_append.mp hi with h | h
  · exact LabelIn.of_none (inputBlock_none _ _ _ _ i h)
  · exact LabelIn.of_none (plain_none i (kernelBlock_plain n i h))

theorem secretsStep_reveals (st : State) (n seedSlot maskSlot recoverySlot : Nat) :
    Reveals secretsKinds (secretsStep st n seedSlot maskSlot recoverySlot) := by
  unfold secretsStep
  split
  · exact Every.abort _
  · exact secrets_reveals _ _ _ _

theorem registerBlock_plain (n : Nat) (password recovery : BoolH) (tail : B8) :
    ∀ i ∈ registerBlock n password recovery tail, plain i = true := by
  intro i hi
  unfold registerBlock at hi
  split at hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem register_silent (n : Nat) (password recovery : BoolH) (tail : B8) :
    Silent (registerScript n password recovery tail) := by
  unfold registerScript
  split
  · exact Silent.seqs (Silent.done _) _ (fun i hi => plain_none i (registerBlock_plain n password recovery tail i hi))
  · exact Silent.abort _

/-- **T3 for op 81's engine part**: nothing is released (the record seal releases under S13's
`requestSealKinds` only: `Send.requestCtr_reveals`). -/
theorem register_reveals (n : Nat) (password recovery : BoolH) (tail : B8) :
    Reveals [] (registerScript n password recovery tail) :=
  (register_silent n password recovery tail).reveals _

theorem registerStep_reveals (st : State) (n : Nat) (tail : B8) : Reveals [] (registerStep st n tail) := by
  unfold registerStep
  split
  · exact register_reveals _ _ _ _
  · exact Every.abort _

section Views

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

/-- **T3 for op 80 against any adversary**: every release the adversary receives is labelled
`ofKind .maskedPassword`. -/
theorem secrets_viewD_kinds (n seedSlot maskSlot recoverySlot : Nat) :
    ∀ r ∈ (withAdv E me adv (secretsScript n seedSlot maskSlot recoverySlot) σ I vD).viewD,
      ∃ k ∈ secretsKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (secrets_reveals n seedSlot maskSlot recoverySlot) σ I vD

/-- **T3 for op 81's engine part against any adversary**: the adversary's view is empty. -/
theorem register_viewD (n : Nat) (password recovery : BoolH) (tail : B8) :
    (withAdv E me adv (registerScript n password recovery tail) σ I vD).viewD = [] :=
  (silent_view E me adv _ (register_silent n password recovery tail) σ I vD).1

end Views

/-! ## The shares (7.0's bijection form of hiding) -/

/-- `TlsMpc.CeremonyProofs`' `Ceremony.masked_hides`, restated here so that this module does not
import the receive proofs: the opened byte takes a given value for exactly one mask byte. -/
theorem masked_hides_byte (word other value : BitVec 8) :
    ∃ mask : BitVec 8, word ^^^ (other ^^^ mask) = value ∧ ∀ m : BitVec 8, word ^^^ (other ^^^ m) = value → m = mask := by
  refine ⟨word ^^^ other ^^^ value, ?_, ?_⟩
  · ext i hi
    simp only [BitVec.getElem_xor]
    cases word[i] <;> cases other[i] <;> cases value[i] <;> rfl
  · intro m hm
    rw [← hm]
    ext i hi
    simp only [BitVec.getElem_xor]
    cases word[i] <;> cases other[i] <;> cases m[i] <;> rfl

/-- **The opened value hides the password** (per list, `CeremonyProofs.masked_hides` for every
byte): for every password `word` and every value `other` of the other party's mask, and every
target value of the same length, exactly one honest mask makes the opened `word ⊕ (other ⊕ mask)`
equal the target. So for a uniform honest mask the opened value is uniform, whatever the password. -/
theorem masked_hides_list : ∀ (word other target : B8), word.length = target.length → other.length = target.length →
    ∃ mask : B8, mask.length = target.length ∧
      List.zipWith (· ^^^ ·) word (List.zipWith (· ^^^ ·) other mask) = target ∧
      ∀ m : B8, m.length = target.length → List.zipWith (· ^^^ ·) word (List.zipWith (· ^^^ ·) other m) = target → m = mask
  | [], [], [], _, _ => ⟨[], rfl, rfl, fun m hm _ => by cases m <;> simp_all⟩
  | w :: ws, o :: os, t :: ts, hw, ho => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hw ho
    obtain ⟨b, hb, hbu⟩ := masked_hides_byte w o t
    obtain ⟨ms, hl, hms, hu⟩ := masked_hides_list ws os ts hw ho
    refine ⟨b :: ms, by simp [hl], by simp [hb, hms], fun m hm he => ?_⟩
    cases m with
    | nil => simp at hm
    | cons x xs =>
      simp only [List.zipWith_cons_cons, List.cons.injEq] at he
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hm
      rw [hbu x he.1, hu xs hm he.2]
  | [], _ :: _, _, hw, ho => by simp at hw ho; omega
  | [], [], _ :: _, hw, _ => by simp at hw
  | _ :: _, [], _, hw, ho => by simp at hw ho; omega
  | _ :: _, _ :: _, [], hw, _ => by simp at hw

theorem xor_cancel (p a b : BitVec 8) : (a ^^^ (p ^^^ (a ^^^ b))) ^^^ b = p := by
  ext i hi
  simp only [BitVec.getElem_xor]
  cases a[i] <;> cases p[i] <;> cases b[i] <;> rfl

/-- A's password share XOR B's is the password (bytewise `xor_cancel`). -/
theorem password_shares : ∀ (p a b : B8), a.length = p.length → b.length = p.length →
    List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) a (List.zipWith (· ^^^ ·) p (List.zipWith (· ^^^ ·) a b))) b = p
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, ha, hb => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hb
    simp only [List.zipWith_cons_cons, xor_cancel, password_shares xs ys zs ha hb]
  | [], _ :: _, _, ha, _ => by simp at ha
  | [], [], _ :: _, _, hb => by simp at hb
  | _ :: _, [], _, ha, _ => by simp at ha
  | _ :: _, _ :: _, [], _, hb => by simp at hb

/-- **The two parties' replies XOR to password ‖ recovery** (the C++'s reply, `shareOf`): with the
opened `masked = password ⊕ (maskA ⊕ maskB)` (`ceremonySecrets_spec`), A's reply XOR B's reply is the
password ‖ recoveryA ⊕ recoveryB, the kernel's two private outputs. -/
theorem shares_xor (password maskA maskB recoveryA recoveryB : B8)
    (hp : password.length = passwordBytes) (ha : maskA.length = passwordBytes) (hb : maskB.length = passwordBytes) :
    List.zipWith (· ^^^ ·)
        (shareOf .a maskA recoveryA (List.zipWith (· ^^^ ·) password (List.zipWith (· ^^^ ·) maskA maskB)))
        (shareOf .b maskB recoveryB (List.zipWith (· ^^^ ·) password (List.zipWith (· ^^^ ·) maskA maskB))) =
      password ++ List.zipWith (· ^^^ ·) recoveryA recoveryB := by
  have hlA : (List.zipWith (· ^^^ ·) maskA (List.zipWith (· ^^^ ·) password (List.zipWith (· ^^^ ·) maskA maskB))).length =
      maskB.length := by simp [hp, ha, hb]
  simp only [shareOf]
  rw [List.zipWith_append hlA]
  rw [password_shares password maskA maskB (by rw [ha, hp]) (by rw [hb, hp])]

end TlsMpc.Node.Flows.Ceremony
