import TlsMpc.Node.Flows.TlsProofs

/-!
# Well-formedness of the remaining S12 scripts (gap F14)

REORGANIZATION_PLAN.md stage S12. `Flows/TlsProofs.lean` proved WF for seven scripts (`sealCtr`,
`tag`, `update`, `public`, `range`, `drop`; `Ghash.keyShare`). Here the rest: the shell's `check`
accepts every instruction on every branch of

  `Tls.parserScript_wf`, `Tls.revealScript_wf`, `Tls.openHandshakeScript_wf`, `Tls.verifyScript_wf`,
  `Tls.finishScript_wf`, `Tls.deriveScript_wf`, `Tls.agreeScript_wf`, `Tls.sealClassScript_wf`,
  `Tls.openScript_wf` (both branches after the handshake bit, and the abort), `Ghash.roundScript_wf`,

from any context in which the operand handles are live with the marks the backend gives them
(traffic blocks and the main secret 480 / 256 private bits, not once; the parser state 88 private
bits; the agreement word 255 private bits; received payloads any marks), no handle id from `n` on
was ever defined (`Fresh c n`, the session counter), and each kernel's signature is the one its Lean
kernel declares (input width in bits; output marks per bit: `pub` for an `opened` field, `toB` for
audience 2, `never` otherwise). Each signature is a hypothesis in the style of
`sealCtrScript_wf`: it is what `circuitOf` of the kernel gives (`TlsBase.circuitOf`), stated
explicitly so that no kernel term is unfolded.

The proofs go through the `check_*` lemmas of ContactsBase.lean / TlsBase.lean; three small tactics
discharge their side conditions on the symbolic context (`fresh_tac`: an id above every defined one;
`live_tac`: a handle's entry after pushes and drops; `len_tac`: widths). No I/O; no emitter imports
this module.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase

/-! ## The symbolic context -/

@[simp] theorem seenB_push (c : Ctx) (n : Nat) (i : BoolInfo) : (push c n i).seenB = n :: c.seenB := rfl
@[simp] theorem seenB_dropBool (c : Ctx) (id : Nat) : (c.dropBool id).seenB = c.seenB := rfl

theorem flatten_replicate_one {α : Type} (l : List α) : (List.replicate 1 l).flatten = l := by simp

/-- An id at or above the first fresh one is not in a context built from a fresh one by pushes of
smaller ids and drops (the hypothesis `Fresh _ _` in the local context). -/
macro "fresh_tac" : tactic => `(tactic| (
  intro j hj hmem
  have hj0 := ‹Fresh _ _› j (by omega)
  simp only [seenB_push, seenB_dropBool, List.mem_cons, hj0, or_false] at hmem
  all_goals omega))

/-- Two handle ids differ (after reducing `{ id := k }.id`). -/
macro "ne_tac" : tactic => `(tactic| first | omega | (dsimp only; omega))

/-- A handle's entry in a context built by pushes and drops. -/
macro "live_tac" : tactic => `(tactic| first
  | assumption
  | (simp only [*, Option.isSome_some]; done)
  | (simp (disch := ne_tac) only [bool?_push_self, bool?_push_of_ne, bool?_drop_of_ne, Option.isSome_some] <;>
      first | rfl | assumption | (simp only [*, Option.isSome_some])))

/-- Width and length side conditions. -/
macro "len_tac" : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_append, List.length_replicate, length_bitsOf, List.length_cons, List.length_nil,
    List.length_take, List.length_drop, flatten_replicate_one, maxWidth_eq, innerLength] at * <;> omega))

/-- Every mark of a slice inside a public prefix is openable. -/
theorem all_openable_slice (a lo hi : Nat) (R : List Mark) (h : hi ≤ a) :
    (((List.replicate a Mark.pub ++ R).drop lo).take (hi - lo)).all Mark.openable = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take, List.length_drop] at hi'
  rw [List.getElem_take, List.getElem_drop, List.getElem_append_left (by simp; omega), List.getElem_replicate]
  rfl

theorem all_openable_pub (a : Nat) : (List.replicate a Mark.pub).all Mark.openable = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [(List.mem_replicate.mp hx).2]
  rfl

theorem all_openable_pub_slice (a lo k : Nat) : (((List.replicate a Mark.pub).drop lo).take k).all Mark.openable = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [(List.mem_replicate.mp (List.mem_of_mem_drop (List.mem_of_mem_take hx))).2]
  rfl

theorem all_openable_of (l : List Mark) (h : ∀ m ∈ l, m = .pub) : l.all Mark.openable = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [h x hx]
  rfl

/-! ## The parser, the reveal, the handshake -/

/-- **`parserScript` is well formed** (`tls-parser-initial`: one byte in, 11 private bytes out). -/
theorem parserScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (hf : Fresh c n)
    (hsig : sigs parserName = some ⟨8, List.replicate 88 .never⟩) : WF sigs c (parserScript n) := by
  unfold parserScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- **`verifyScript` is well formed** (`tls-verify-finished`: block 60, hash 32, message 36 bytes
in; the acceptance byte public). -/
theorem verifyScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (serverHs : BoolH) (hash message : B8)
    (hf : Fresh c n) (hsn : serverHs.id < n) (hs : c.bool? serverHs = some ⟨List.replicate 480 .never, false⟩)
    (hh : hash.length = 32) (hm : message.length = 36)
    (hsig : sigs verifyName = some ⟨8 * 128, List.replicate 8 .pub⟩) :
    WF sigs c (verifyScript n serverHs hash message) := by
  unfold verifyScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
      (useBools_nil _))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one]; exact all_openable_pub _)]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- Every mark of a slice past a prefix of `a` marks and inside the public part after it is
openable. -/
theorem all_openable_after (m : Mark) (a b lo hi : Nat) (h1 : a ≤ lo) (h2 : hi ≤ a + b) :
    (((List.replicate a m ++ List.replicate b Mark.pub).drop lo).take (hi - lo)).all Mark.openable = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take, List.length_drop, List.length_append, List.length_replicate] at hi'
  rw [List.getElem_take, List.getElem_drop, List.getElem_append_right (by simp; omega), List.getElem_replicate]
  rfl

/-- **`revealScript` is well formed** (`tls-reveal-masked CAP`: the length (2 bytes) and the content
(`CAP` bytes) in; both outputs public). -/
theorem revealScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (length content : BoolH) (cap : Nat)
    (lm cm : List Mark) (hf : Fresh c n) (hln : length.id < n) (hcn : content.id < n)
    (hl : c.bool? length = some ⟨lm, false⟩) (hc : c.bool? content = some ⟨cm, false⟩)
    (hlm : lm.length = 16) (hcm : cm.length = 8 * cap) (hcap : cap ≤ 65536)
    (hsig : sigs (revealName cap) = some ⟨8 * (2 + cap), List.replicate (16 + 8 * cap) .pub⟩) :
    WF sigs c (revealScript n length content cap) := by
  unfold revealScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
      (useBools_nil _))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one]; exact all_openable_pub_slice _ _ _)]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- **`openHandshakeScript` is well formed** (`tls-open-handshake |record|`: block 60, sequence 8,
record in; the gated result public, `om` its marks). -/
theorem openHandshakeScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (serverHs : BoolH) (seq record : B8)
    (om : List Mark) (hf : Fresh c n) (hsn : serverHs.id < n)
    (hs : c.bool? serverHs = some ⟨List.replicate 480 .never, false⟩) (hq : seq.length = 8)
    (hr : record.length ≤ 16645) (hom : ∀ m ∈ om, m = .pub) (hol : om.length ≤ maxWidth)
    (hsig : sigs (openHsName record.length) = some ⟨8 * (68 + record.length), om⟩) :
    WF sigs c (openHandshakeScript n serverHs seq record) := by
  unfold openHandshakeScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
      (useBools_nil _))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one]; exact all_openable_of _ hom)]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- **`finishScript` is well formed** (`tls-finish |certificate|`: main 32, server hash 32, client
block 60, client hash 32, certificate in; two traffic blocks private, the Finished record public). -/
theorem finishScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (main clientHs : BoolH)
    (serverHash clientHash certificate : B8) (hf : Fresh c n) (hmn : main.id < n) (hcn : clientHs.id < n)
    (hm : c.bool? main = some ⟨List.replicate 256 .never, false⟩)
    (hch : c.bool? clientHs = some ⟨List.replicate 480 .never, false⟩)
    (hsh : serverHash.length = 32) (hchl : clientHash.length = 32) (hcert : certificate.length ≤ 16384)
    (hsig : sigs (finishName certificate.length) = some ⟨8 * (156 + certificate.length),
      List.replicate 960 .never ++ List.replicate (8 * finishedLength certificate.length) .pub⟩) :
    WF sigs c (finishScript n main clientHs serverHash clientHash certificate) := by
  unfold finishScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_boolPublic sigs (by fresh_tac) _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
      (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
        (useBools_nil _))))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by simp only [finishedLength] at *; len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl)
    (by simp only [finishedLength] at *; len_tac) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl)
    (by simp only [finishedLength] at *; len_tac) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl)
    (by simp only [finishedLength] at *; len_tac) (by fresh_tac) (by simp only [finishedLength] at *; len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one]; exact all_openable_after _ _ _ _ _ (Nat.le_refl _) (by omega))]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- **`deriveScript` is well formed** (`tls-derive`: the agreement word, 255 bits, and the hello
hash, 32 bytes, in; two traffic blocks and the main secret, all private, out; the agreement freed). -/
theorem deriveScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (agreement : BoolH) (helloHash : B8)
    (hf : Fresh c n) (han : agreement.id < n)
    (ha : c.bool? agreement = some ⟨List.replicate 255 .never, false⟩) (hh : helloHash.length = 32)
    (hsig : sigs deriveName = some ⟨511, List.replicate 1216 .never⟩) :
    WF sigs c (deriveScript n agreement helloHash) := by
  unfold deriveScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
      (useBools_nil _))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- **`agreeScript` is well formed** (public bits only). -/
theorem agreeScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (digest : B8) (valid : Bool)
    (hf : Fresh c n) (hd : digest.length = 32) : WF sigs c (agreeScript n digest valid) := by
  unfold agreeScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  split
  · exact WF.done _ _
  · exact WF.abort _ _

/-! ## The class seal -/

/-- A size fits its class (`RecordClass.capacity n ≥ n`). -/
theorem le_capacity (n : Nat) : n ≤ capacity n := by
  unfold capacity RecordClass.capacity
  split
  · omega
  · simp only
    have hs : 0 < 2 ^ (Nat.log2 (n - 1) - 2) := Nat.two_pow_pos _
    generalize 2 ^ (Nat.log2 (n - 1) - 2) = s at hs ⊢
    have h1 := Nat.div_add_mod (n + s - 1) s
    have h2 := Nat.mod_lt (n + s - 1) hs
    rw [Nat.mul_comm] at h1
    generalize (n + s - 1) / s * s = X at h1 ⊢
    generalize (n + s - 1) % s = r at h1 h2
    omega

/-- **`sealClassScript` is well formed** (`tls-seal-class CAP`, `CAP = capacity size`: block 60,
sequence 8, content `CAP`, length field 2 bytes in; accepted, header and ciphertext public
(`1 + 5 + CAP + 1` bytes), the pad (16 bytes) private). -/
theorem sealClassScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic content : BoolH) (seq : B8)
    (size : Nat) (cm : List Mark) (hf : Fresh c n) (htn : traffic.id < n) (hcn : content.id < n)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hc : c.bool? content = some ⟨cm, false⟩)
    (hcm : cm.length = 8 * size) (hs : seq.length = 8) (hcap : capacity size ≤ 65536)
    (hsig : sigs (sealClassName (capacity size)) = some ⟨8 * (70 + capacity size),
      List.replicate (8 * (1 + 5 + capacity size + 1)) .pub ++ List.replicate 128 .never⟩) :
    WF sigs c (sealClassScript n traffic content seq size) := by
  have hle := le_capacity size
  unfold sealClassScript
  simp only [seqs_cons, seqs_nil]
  generalize capacity size = cap at hle hcap hsig ⊢
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_boolPublic sigs (by fresh_tac) _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
      (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
        (useBools_nil _))))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one]; exact all_openable_slice _ _ _ _ (by omega))]
  intro b _
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  split
  · exact WF.done _ _
  · exact WF.abort _ _

/-! ## The open -/

/-- `check_boolInputBoth` for any two fresh ids `a < b`. -/
theorem check_boolInputBoth2 (sigs : Bytes → Option Sig) {c : Ctx} {a b : Nat} (hf : Fresh c a) (hab : a < b)
    (w : Nat) (once rev : Bool) (hw : w ≤ maxWidth) :
    check sigs c (.boolInputBoth ⟨a⟩ ⟨b⟩ w once rev ()) =
      some (push (push c a ⟨List.replicate w (Mark.ofInput rev), once⟩) b ⟨List.replicate w (Mark.ofInput rev), once⟩,
        .unit) := by
  have h0 := hf a (Nat.le_refl a)
  have h1 := hf b (by omega)
  have hne : b ≠ a := by omega
  simp [check, guard, Ctx.defBool, h0, h1, hne, push, hw, Nat.not_lt.mpr hw]

/-- The marks of `tls-open-typed CAP`'s output: the bit and the event public (3 bytes), the parser
state, length, content (`CAP − 21`) and parse (`CAP − 17`) private. -/
def typedMarks (cap : Nat) : List Mark :=
  List.replicate 24 .pub ++ List.replicate (8 * (13 + (cap - 21) + (cap - 17))) .never

/-- The marks of `tls-frame CAP`'s output: the event public, the rest private. -/
def frameMarks (cap : Nat) : List Mark := List.replicate 16 .pub ++ List.replicate (8 * (13 + (cap - 21))) .never

theorem directRest_wf (sigs : Bytes → Option Sig) (c : Ctx) (n cap : Nat) (hf : Fresh c (n + 10))
    (h8 : c.bool? ⟨n + 8⟩ = some ⟨typedMarks cap, false⟩) (h9 : (c.bool? ⟨n + 9⟩).isSome = true)
    (hcap : cap ≤ 65536) : WF sigs c (directRest n cap) := by
  unfold directRest
  simp only [seqs_cons, seqs_nil, typedMarks] at h8 ⊢
  refine WF_seq sigs c _ _ _ (check_slice sigs (useBool_keep h8 rfl) (by len_tac) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by exact all_openable_slice _ _ _ _ (by omega))]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

theorem frameRest_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (parser : BoolH) (cap : Nat) (pm : List Mark)
    (hf : Fresh c (n + 10)) (hpn : parser.id < n)
    (h8 : c.bool? ⟨n + 8⟩ = some ⟨typedMarks cap, false⟩) (h9 : (c.bool? ⟨n + 9⟩).isSome = true)
    (hp : c.bool? parser = some ⟨pm, false⟩) (hpm : pm.length = 88) (hcap : cap ≤ 65536)
    (hsig : sigs (frameName cap) = some ⟨8 * (11 + (cap - 17)), frameMarks cap⟩) :
    WF sigs c (frameRest n parser cap) := by
  unfold frameRest
  simp only [seqs_cons, seqs_nil, typedMarks] at h8 ⊢
  simp only [frameMarks] at hsig
  refine WF_seq sigs c _ _ _ (check_slice sigs (useBool_keep h8 rfl) (by len_tac) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
      (useBools_nil _))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl) (by len_tac) (by fresh_tac)
    (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one]; exact all_openable_slice _ _ _ _ (by omega))]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)

/-- **`openScript` is well formed**, on every branch (bit 0: the typed kernel's fields; bit 255:
`tls-frame`; any other bit: abort). Inputs: the parser state (88 bits, any marks, not once) and the
server traffic block live, both parties' halves as private `once` inputs (consumed by the tag
check), the record padded to `CAP ≥ 21` bytes and its length field public. Signatures: `gcm-check`
(116 bytes in, the acceptance byte private), `tls-open-typed CAP` (`typedMarks`), `tls-frame CAP`
(`frameMarks`). -/
theorem openScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (parser traffic : BoolH)
    (seq tag recordPadded size : B8) (cap halfSlot : Nat) (pm : List Mark) (hf : Fresh c n)
    (hpn : parser.id < n) (htn : traffic.id < n) (hp : c.bool? parser = some ⟨pm, false⟩) (hpm : pm.length = 88)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hs : seq.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (hcap : cap ≤ 65536)
    (hcheck : sigs checkName = some ⟨8 * 116, List.replicate 8 .never⟩)
    (htyped : sigs (typedName cap) = some ⟨8 * (82 + cap), typedMarks cap⟩)
    (hframe : sigs (frameName cap) = some ⟨8 * (11 + (cap - 17)), frameMarks cap⟩) :
    WF sigs c (openScript n parser traffic seq tag recordPadded size cap halfSlot) := by
  unfold openScript checkBlock typedBlock
  simp only [List.cons_append, List.nil_append, seqs_cons, seqs_nil]
  have htyped' := htyped
  simp only [typedMarks] at htyped'
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_boolInputBoth2 sigs (by fresh_tac) (by omega) 128 true false (by decide)) ?_
  refine WF_seq sigs _ _ _ _ (check_boolPublic sigs (by fresh_tac) _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
      (useBools_cons (useBool_once (by live_tac) rfl) (useBools_cons (useBool_once (by live_tac) rfl)
        (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_nil _)))))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs hcheck Nat.one_pos (useBool_once (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_boolPublic sigs (by fresh_tac) _ (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
      (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_cons (useBool_keep (by live_tac) rfl)
        (useBools_cons (useBool_keep (by live_tac) rfl) (useBools_nil _)))))) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_run sigs htyped Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by len_tac) (by fresh_tac) (by decide) (by simp only [typedMarks]; len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one, typedMarks]; len_tac) (by fresh_tac) (by len_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (by live_tac) rfl)
    (by simp only [flatten_replicate_one, typedMarks]; exact all_openable_slice _ _ _ _ (by omega))]
  intro b _
  unfold afterBit
  split
  · exact directRest_wf sigs _ n cap (by fresh_tac) (by simp only [flatten_replicate_one]; live_tac) (by live_tac) hcap
  · split
    · exact frameRest_wf sigs _ n parser cap pm (by fresh_tac) hpn (by simp only [flatten_replicate_one]; live_tac)
        (by live_tac) (by live_tac) hpm hcap hframe
    · exact WF.abort _ _

end TlsMpc.Node.Flows.Tls

namespace TlsMpc.Node.Flows.Ghash

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Tls (seenB_push seenB_dropBool flatten_replicate_one check_boolInputBoth2)

theorem all_toB (c : Nat) :
    ((List.replicate c (List.replicate 128 Mark.toB)).flatten.all (· == Mark.to .b)) = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [List.mem_flatten, List.mem_replicate] at hx
  obtain ⟨l, ⟨-, rfl⟩, hx⟩ := hx
  rw [(List.mem_replicate.mp hx).2]
  rfl

/-- **`roundScript` is well formed** (one round of the doubling schedule): both parties' `c` left
shares and shares of H, A's `c` masks, all private `once` inputs (consumed by the concat, whose
result the pick consumes, whose result the run consumes: each mask reaches one copy), `gcm-multiply`
with `c` copies (80 bytes in, the masked product to B), opened to B. For `0 < c ≤ 1024` (otherwise
the script aborts, also well formed). -/
theorem roundScript_wf (sigs : Bytes → Option Sig) (ctx : Ctx) (n c leftSlot rightSlot maskSlot dst : Nat)
    (hf : Fresh ctx n) (hsig : sigs multiplyName = some ⟨8 * 80, List.replicate 128 .toB⟩) :
    WF sigs ctx (roundScript n c leftSlot rightSlot maskSlot dst) := by
  unfold roundScript
  split
  · next hc =>
    obtain ⟨hc0, hc1⟩ := hc
    unfold roundBlock
    simp only [seqs_cons, seqs_nil]
    refine WF_seq sigs ctx _ _ _ (check_boolInputBoth2 sigs hf (by omega) (128 * c) true false
      (by rw [maxWidth_eq]; omega)) ?_
    refine WF_seq sigs _ _ _ _ (check_boolInputBoth2 sigs (by fresh_tac) (by omega) 128 true false (by decide)) ?_
    refine WF_seq sigs _ _ _ _ (check_boolInput sigs (by fresh_tac) .a (128 * c) true false
      (by rw [maxWidth_eq]; omega)) ?_
    refine WF_seq sigs _ _ _ _ (check_concat sigs
      (useBools_cons (useBool_once (by live_tac) rfl) (useBools_cons (useBool_once (by live_tac) rfl)
        (useBools_cons (useBool_once (by live_tac) rfl) (useBools_cons (useBool_once (by live_tac) rfl)
          (useBools_cons (useBool_once (by live_tac) rfl) (useBools_nil _)))))) (by fresh_tac) (by len_tac)) ?_
    refine WF_seq sigs _ _ _ _ (check_pick sigs (useBool_once (bool?_push_self _ _ _) rfl)
      (by
        rw [List.all_eq_true]
        intro j hj
        have := layout_bound c j hj
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, decide_eq_true_eq]
        all_goals omega)
      (by fresh_tac) (by rw [length_layout, maxWidth_eq]; omega)) ?_
    refine WF_seq sigs _ _ _ _ (check_run sigs hsig hc0 (useBool_once (bool?_push_self _ _ _) rfl)
      (by rw [List.length_map, length_layout]; try omega) (by fresh_tac) (by rw [maxWidth_eq]; omega)
      (by rw [List.length_replicate, maxWidth_eq]; omega)) ?_
    refine WF_seq sigs _ _ _ _ (TlsBase.check_openBoolTo sigs (by decide) (useBool_keep (by live_tac) rfl)
      (by exact all_toB c)) ?_
    exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by live_tac)) (WF.done _ _)
  · exact WF.abort _ _

end TlsMpc.Node.Flows.Ghash
