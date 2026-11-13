import TlsMpc.Node.Flows.Send
import TlsMpc.Node.Flows.TlsProofs

/-!
# `Send.*`: what the send scripts compute (T4-SEND, T7 through the scripts) and well-formedness

REORGANIZATION_PLAN.md stage S13. No I/O; no emitter imports this module.

THE MODEL CIRCUITS. A seal kernel has `.word` inputs (255-bit field words), which
`Contacts.kernelCircuit` (byte inputs only) does not cover. `shapedCircuit K marks` reads its input
bundle field by field in declaration order (`.bytes k`: `8k` bits, bytes least significant bit
first; `.word`: 255 bits, one variable) and outputs the output fields concatenated: the same trusted
correspondence as `Contacts.Loaded` (T2, a circuit computes its Lean kernel), for kernels with words.

T4-SEND AT THE FUNCTION LEVEL (each kernel's output read through the script's layout; as S12):
  * `seal_out`: `signal-seal-official|built` on the bundle `sealScript` builds (certificate ‖ record,
    the built text, four words) outputs `SealSend.sealValue` of exactly that conversation and text;
    `sealOut_lengths`: its fields have the lengths the script slices with (status 1, conversation
    `cert + 319`, timestamp 8, envelope `sealEnvBytes`); `sealEnvBytes_eq`: that envelope length is
    the kernel's own.
  * `seal_accepted_value`: when the opened status is 255, the opened timestamp ‖ envelope is the
    built text's timestamp and `Reference.sealV1` of the Signal message of the reference send step
    `SpqrSend.canonical` on the stored state, and the new state the script keeps is the advanced
    record (`SealSend.advancedRecord` without the certificate).
  * `requestCtr_value`: `signal-request-ctr` on the bundle `requestCtrScript` builds (traffic ‖
    sequence ‖ conversation ‖ frame ‖ mask) seals the WebSocket frame of the filled request, for the
    frame and offsets `PublicRequest.build` returned: `RequestFrame.signalRequestCtr_built` with its
    hypotheses `hframe`, `hmask` DISCHARGED by the script's layout (the frame and mask are the
    script's own public bits at their positions); `bundleRequestCtr_value` likewise for
    `bundle-request-ctr` (`hframe`, `hmask` discharged; `paired` is the script path's own pairing
    of the offsets, `devicesName_paired`).
  * `request_record`: the record that leaves (header ‖ ciphertext opened by `requestCtrScript`, then
    `Tls.tagScript`'s tag over the pad and both parties' halves of shares that share H¹ … Hⁿ) is
    `TlsRecord.sealCore` of the filled frame: the AES-GCM TLS record (P-GHASH (c) as S12's
    `seal_is_record`).
  * **`send_accepted`** (the headline): op 41 then op 42 then the record seal, on the script path,
    with NO wiring hypothesis (`built`, `hframe`, `hmask` of `SealFrame.serverReceives_accepted` are
    gone: the frame is the one `frameFor` builds from the script's own opened envelope and timestamp,
    and the kernels' inputs are the script's concatenations): on an accepted send, what leaves for the
    server is the TLS record sealing the request frame that carries the reference sealed-sender
    envelope of the reference ratchet step, and the stored state is the advanced one.
  * Refusal: `Send.seal_refused_silent` (nothing after the status is released; the state is kept)
    and `seal_refused_value` (a refused status opens an all-zero envelope slot, never opened).

WF: `requestScript_wf`, `requestCtrScript_wf`, `sealScript_wf` (op 41, from the contact's state and
the account's handles); ops 61 and 62 (device lists): the vectors' batches pass `checkBatch`
(S13_NOTES.md, gap S13-4).
-/

namespace TlsMpc.Node.Flows.Send

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.HybridKernel (Kernel lookup lookupFrom)

/-! ## Model circuits for kernels with word inputs -/

/-- One packed variable per byte. -/
def pack8 (b : BitVec 8) : BVExpr.PackedBitVec := ⟨b⟩

/-- The kernel's variables from its input bundle: bytes fields one 8-bit variable per byte, words
one 255-bit variable. -/
def packs : List (String × HybridKernel.Shape) → Bits → List BVExpr.PackedBitVec
  | [], _ => []
  | (_, .bytes k) :: rest, v => (bytesOf (v.take (8 * k))).map pack8 ++ packs rest (v.drop (8 * k))
  | (_, .word) :: rest, v => ⟨BitVec.ofBoolListLE (v.take 255)⟩ :: packs rest (v.drop 255)

def shapedAssign (inputs : List (String × HybridKernel.Shape)) (v : Bits) : BVExpr.Assignment :=
  chain 0 (packs inputs v)

/-- The kernel's output fields on the input bundle `v`, concatenated. -/
def shapedOut (K : Kernel) (v : Bits) : B8 :=
  (K.outputs.map fun f => f.value.map (BVExpr.eval (shapedAssign K.inputs v))).flatten

/-- The model circuit of a kernel with word inputs. -/
def shapedCircuit (K : Kernel) (marks : List Mark) : Circuit where
  inWidth := (K.inputs.map (·.2.bits)).sum
  outMarks := marks
  eval v := bitsOf (shapedOut K v)

theorem packs_bytes (name : String) (k : Nat) (rest : List (String × HybridKernel.Shape)) (l : B8) (v : Bits)
    (hl : l.length = k) : packs ((name, .bytes k) :: rest) (bitsOf l ++ v) = l.map pack8 ++ packs rest v := by
  have h8 : (bitsOf l).length = 8 * k := by rw [length_bitsOf, hl]
  simp only [packs, List.take_left' h8, List.drop_left' h8, bytesOf_bitsOf]

theorem eval_chain_byte (l : B8) (rest : List BVExpr.PackedBitVec) (j : Nat) (hj : j < l.length) :
    BVExpr.eval (chain 0 (l.map pack8 ++ rest)) (BVExpr.var j : BVExpr 8) = l[j] := by
  rw [BVExpr.eval_var, get_chain _ 0 j (Nat.zero_le j), Nat.sub_zero, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using hj), List.getElem?_map, List.getElem?_eq_getElem hj]
  simp [pack8]

theorem inputBytes_chain (l : B8) (rest : List BVExpr.PackedBitVec) (s c : Nat) (h : s + c ≤ l.length) :
    (ByteCircuit.inputBytes s c).map (BVExpr.eval (chain 0 (l.map pack8 ++ rest))) = (l.drop s).take c := by
  apply List.ext_getElem
  · simp [ByteCircuit.inputBytes]
    omega
  · intro i h1 h2
    simp only [ByteCircuit.inputBytes, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    simp only [ByteCircuit.inputBytes, List.length_map, List.length_range] at h1
    exact eval_chain_byte l rest (s + i) (by omega)

theorem inputBytes_zero (s c : Nat) : (ByteCircuit.inputBytes s c).map (BVExpr.eval zeroA) = List.replicate c 0 := by
  apply List.ext_getElem
  · simp [ByteCircuit.inputBytes]
  · intro i h1 h2
    simp [ByteCircuit.inputBytes, zeroA, BVExpr.Assignment.get, Lean.RArray.get]

/-- Output lengths do not depend on the assignment. -/
theorem values_length (K : Kernel) (a b : BVExpr.Assignment) (i : Nat) :
    ((K.outputs.map fun f => f.value.map (BVExpr.eval a)).getD i []).length =
      ((K.outputs.map fun f => f.value.map (BVExpr.eval b)).getD i []).length := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases K.outputs[i]? <;> simp

/-! ## The seal kernel through the script's layout -/

section Seal

variable (cert cw pw ew iw classes : Nat) (official : Bool)

/-- The seal kernel the script names. -/
abbrev sealK : Kernel := HybridKernel.signalSealFixed cert cw pw ew iw true classes official

def textBytes : Nat :=
  if official then PrivateTextNotification.officialBuiltBytes classes else PrivateTextNotification.builtBytes classes

theorem sealK_inputs : (sealK cert cw pw ew iw classes official).inputs = KernelSpecs.SealFixed.sealInputs cert classes official :=
  rfl

theorem lookup_conv : lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "conversation" =
    ByteCircuit.inputBytes 0 (convBytes cert) := by
  simp [lookup, lookupFrom, KernelSpecs.SealFixed.sealInputs, convBytes, recordBytes, HybridKernel.conversationBytes]

theorem lookup_text : lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "text" =
    ByteCircuit.inputBytes (convBytes cert) (textBytes classes official) := by
  cases official <;>
    simp [lookup, lookupFrom, KernelSpecs.SealFixed.sealInputs, convBytes, recordBytes,
      HybridKernel.conversationBytes, HybridKernel.Shape.variables, textBytes]

/-- The words' bundle: four 255-bit words. -/
def Words (w : Bits) : Prop := w.length = 4 * 255

theorem packs_seal (conv text : B8) (w : Bits) (hc : conv.length = convBytes cert)
    (ht : text.length = textBytes classes official) :
    packs (KernelSpecs.SealFixed.sealInputs cert classes official) (bitsOf conv ++ (bitsOf text ++ w)) =
      (conv ++ text).map pack8 ++ packs [("ephemeralPublic", .word), ("senderPublic", .word),
        ("ephemeralAgreement", .word), ("staticAgreement", .word)] w := by
  have e1 : KernelSpecs.SealFixed.sealInputs cert classes official =
      ("conversation", HybridKernel.Shape.bytes (convBytes cert)) ::
        ("text", HybridKernel.Shape.bytes (textBytes classes official)) ::
        [("ephemeralPublic", .word), ("senderPublic", .word), ("ephemeralAgreement", .word),
          ("staticAgreement", .word)] := by
    cases official <;> rfl
  rw [e1, packs_bytes _ _ _ conv _ hc, packs_bytes _ _ _ text _ ht, List.map_append, List.append_assoc]

/-- The seal kernel's view of the script's bundle: its conversation and text are the script's. -/
theorem seal_get (conv text : B8) (w : Bits) (hc : conv.length = convBytes cert)
    (ht : text.length = textBytes classes official) :
    let a := shapedAssign (sealK cert cw pw ew iw classes official).inputs (bitsOf conv ++ (bitsOf text ++ w))
    (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "conversation").map (BVExpr.eval a) = conv ∧
    (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "text").map (BVExpr.eval a) = text := by
  intro a
  have ha : a = chain 0 ((conv ++ text).map pack8 ++ packs [("ephemeralPublic", .word), ("senderPublic", .word),
      ("ephemeralAgreement", .word), ("staticAgreement", .word)] w) := by
    show chain 0 (packs (sealK cert cw pw ew iw classes official).inputs _) = _
    rw [sealK_inputs, packs_seal cert classes official conv text w hc ht]
  rw [ha, lookup_conv, lookup_text, inputBytes_chain _ _ _ _ (by simp [hc, ht]),
    inputBytes_chain _ _ _ _ (by simp [hc, ht])]
  constructor
  · rw [List.drop_zero, List.take_left' hc]
  · rw [List.drop_left' hc, List.take_of_length_le (Nat.le_of_eq ht)]

/-- The kernel's bound on its public parameters (`SealSend.signalSeal_value`). -/
def SealBound : Prop :=
  cert + KernelSpecs.SealFixed.contentBytes classes official + cw + pw + ew + iw < 2 ^ 31

/-- **The seal kernel on the script's bundle** (`signalSeal_value` read through the layout): its
outputs are `SealSend.sealValue` of the script's conversation (certificate ‖ record) and built text,
and of the four words as the kernel reads them. -/
theorem seal_out (conv text : B8) (w : Bits) (hc : conv.length = convBytes cert)
    (ht : text.length = textBytes classes official) (hb : SealBound cert cw pw ew iw classes official) :
    let a := shapedAssign (sealK cert cw pw ew iw classes official).inputs (bitsOf conv ++ (bitsOf text ++ w))
    let get := fun name => (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) name).map (BVExpr.eval a)
    (sealK cert cw pw ew iw classes official).outputs.map (fun f => f.value.map (BVExpr.eval a)) =
      KernelSpecs.SealSend.sealValue cert cw pw ew iw (KernelSpecs.SealFixed.contentBytes classes official) conv text
        (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement") := by
  intro a get
  have hv := KernelSpecs.SealSend.signalSeal_value cert cw pw ew iw classes official a hb
  obtain ⟨g1, g2⟩ := seal_get cert cw pw ew iw classes official conv text w hc ht
  change (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "conversation").map (BVExpr.eval a) = conv
    at g1
  change (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "text").map (BVExpr.eval a) = text at g2
  simp only at hv
  rw [hv, g1, g2]

theorem zero_conv : (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "conversation").map
    (BVExpr.eval zeroA) = List.replicate (convBytes cert) 0 := by
  rw [lookup_conv, inputBytes_zero]

theorem zero_text : (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "text").map
    (BVExpr.eval zeroA) = List.replicate (textBytes classes official) 0 := by
  rw [lookup_text, inputBytes_zero]

theorem textBytes_eq (hcl : 1 ≤ classes) :
    textBytes classes official = KernelSpecs.SealFixed.contentBytes classes official + 10 ∧
      90 ≤ textBytes classes official + 1 := by
  cases official <;>
    simp [textBytes, KernelSpecs.SealFixed.contentBytes, PrivateTextNotification.officialBuiltBytes,
      PrivateTextNotification.builtBytes, PrivateTextNotification.officialPaddedBytes,
      PrivateTextNotification.paddedBytes] <;> omega

/-- **The seal kernel's output lengths** (status 1, conversation `cert + 319`, timestamp 8, envelope
`sealEnvBytes`), on every assignment: from the kernel's value function on the all-zero inputs. -/
theorem sealOut_lengths (a : BVExpr.Assignment) (hb : SealBound cert cw pw ew iw classes official) (hcl : 1 ≤ classes) :
    let o := (sealK cert cw pw ew iw classes official).outputs.map (fun f => f.value.map (BVExpr.eval a))
    (o.getD 0 []).length = 1 ∧ (o.getD 1 []).length = convBytes cert ∧ (o.getD 2 []).length = 8 ∧
      (o.getD 3 []).length = sealEnvBytes cert classes official cw pw ew iw ∧ o.length = 4 := by
  intro o
  obtain ⟨hT, hT'⟩ := textBytes_eq classes official hcl
  have hz := KernelSpecs.SealSend.signalSeal_value cert cw pw ew iw classes official zeroA hb
  simp only at hz
  have l0 := values_length (sealK cert cw pw ew iw classes official) a zeroA 0
  have l1 := values_length (sealK cert cw pw ew iw classes official) a zeroA 1
  have l2 := values_length (sealK cert cw pw ew iw classes official) a zeroA 2
  have l3 := values_length (sealK cert cw pw ew iw classes official) a zeroA 3
  rw [hz] at l0 l1 l2 l3
  rw [zero_conv, zero_text] at l0 l1 l2
  have hrej : ¬ (SpqrSend.accepted ⟨cw, pw, false⟩ ⟨ew, iw, 1, false⟩
      (KernelSpecs.SealFixed.inputOf 0 (KernelSpecs.SealFixed.stagedOf
        ((List.replicate (convBytes cert) (0 : BitVec 8)).drop cert |>.take (182 + 80))
        (List.replicate (textBytes classes official) 0)) (List.replicate (textBytes classes official) 0)
        (KernelSpecs.SealFixed.contentBytes classes official)) ∧
      KernelSpecs.SealValue.Reference.boundAccepted
        ((lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "ephemeralAgreement").map (BVExpr.eval zeroA))
        ((lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "staticAgreement").map (BVExpr.eval zeroA))
        ((lookup (KernelSpecs.SealFixed.sealInputs cert classes official) "senderPublic").map (BVExpr.eval zeroA))
        (KernelSpecs.SealFixed.inputOf 0 (KernelSpecs.SealFixed.stagedOf
          ((List.replicate (convBytes cert) (0 : BitVec 8)).drop cert |>.take (182 + 80))
          (List.replicate (textBytes classes official) 0)) (List.replicate (textBytes classes official) 0)
          (KernelSpecs.SealFixed.contentBytes classes official)).sender ∧
      (List.replicate (textBytes classes official) (0 : BitVec 8)).getD 0 0 = 255) := by
    intro h
    have h3 := h.2.2
    have h0 : (List.replicate (textBytes classes official) (0 : BitVec 8)).getD 0 0 = 0 := by
      cases textBytes classes official with
      | zero => rfl
      | succ k => rfl
    rw [h0] at h3
    exact absurd h3 (by decide)
  refine ⟨?_, ?_, ?_, ?_, by simp [o, HybridKernel.signalSealFixed]⟩
  · rw [l0]; simp only [KernelSpecs.SealSend.sealValue]; rw [if_neg hrej]; rfl
  · rw [l1]; simp only [KernelSpecs.SealSend.sealValue]; rw [if_neg hrej]
    simp only [List.getD_cons_succ, List.getD_cons_zero, KernelSpecs.SealFixed.stagedOf, List.length_append,
      List.length_take, List.length_drop, List.length_replicate, convBytes, recordBytes]
    omega
  · rw [l2]; simp only [KernelSpecs.SealSend.sealValue]; rw [if_neg hrej]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_take, List.length_drop, List.length_replicate]
    omega
  · rw [l3]; rfl

end Seal

/-! ## Slicing a four-field output -/

theorem flatten4 (l : List B8) (h : l.length = 4) : l.flatten = l.getD 0 [] ++ l.getD 1 [] ++ l.getD 2 [] ++ l.getD 3 [] := by
  match l, h with
  | [x0, x1, x2, x3], _ => simp

/-- The script's three slices of status ‖ conversation ‖ timestamp ‖ envelope, in bytes. -/
theorem slice4 (x0 x1 x2 x3 : B8) (c e : Nat) (h0 : x0.length = 1) (h1 : x1.length = c + recordBytes)
    (h2 : x2.length = 8) (h3 : x3.length = e) :
    (x0 ++ x1 ++ x2 ++ x3).take 1 = x0 ∧ ((x0 ++ x1 ++ x2 ++ x3).drop (1 + c)).take recordBytes = x1.drop c ∧
      ((x0 ++ x1 ++ x2 ++ x3).drop (1 + (c + recordBytes))).take (8 + e) = x2 ++ x3 := by
  have hd : (x1.drop c).length = recordBytes := by simp [h1]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.append_assoc, List.take_left' h0]
  · rw [List.append_assoc, List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega),
      List.nil_append, show 1 + c - x0.length = c by omega, List.drop_append_of_le_length (by omega),
      List.take_left' hd]
  · rw [List.append_assoc, List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega),
      List.nil_append, show 1 + (c + recordBytes) - x0.length = x1.length by omega,
      List.drop_left, List.take_of_length_le (by simp [h2, h3])]

/-- Bytes of a byte-aligned bit slice. -/
theorem bitsOf_drop (l : B8) (k : Nat) : (bitsOf l).drop (8 * k) = bitsOf (l.drop k) := by
  induction l generalizing k with
  | nil => simp
  | cons b l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [bitsOf_cons, List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append,
        show 8 * (k + 1) - (bitsOfByte b).length = 8 * k by simp; omega, ih]
      rfl

theorem bitsOf_take (l : B8) (k : Nat) : (bitsOf l).take (8 * k) = bitsOf (l.take k) := by
  induction l generalizing k with
  | nil => simp
  | cons b l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [bitsOf_cons, List.take_append, List.take_of_length_le (l := bitsOfByte b) (by simp; omega),
        show 8 * (k + 1) - (bitsOfByte b).length = 8 * k by simp; omega, ih]
      simp

/-- **The slice the shell takes is the bytes' slice** (`slice h (8a) (8b)` of a byte bundle). -/
theorem bitsOf_slice (l : B8) (a b : Nat) :
    ((bitsOf l).drop (8 * a)).take (8 * b - 8 * a) = bitsOf ((l.drop a).take (b - a)) := by
  rw [bitsOf_drop, show 8 * b - 8 * a = 8 * (b - a) by omega, bitsOf_take]

section SealAccepted

variable (cert cw pw ew iw classes : Nat) (official : Bool)

/-- **An accepted seal, as the script opens and keeps it** (T4-SEND, T7 (b) through the script).
For the bundle `sealScript` builds (certificate ‖ record, the built text, the four words): when the
opened status byte is 255, the reference Signal send step accepts the stored state; the record the
script keeps (`recordFrom … recordEnd`) is the advanced record without its certificate, and with the
certificate in front it is `SealSend.advancedRecord` (what op 42 then reads); the opened timestamp ‖
envelope (`recordEnd … envelopeEnd`) is the built text's timestamp followed by `Reference.sealV1`
(sealed sender v1) of the Signal message of `SpqrSend.canonical` on the stored state. -/
theorem seal_accepted_value (conv text : B8) (w : Bits) (hc : conv.length = convBytes cert)
    (ht : text.length = textBytes classes official) (hb : SealBound cert cw pw ew iw classes official)
    (hcl : 1 ≤ classes) :
    let v := bitsOf conv ++ (bitsOf text ++ w)
    let a := shapedAssign (sealK cert cw pw ew iw classes official).inputs v
    let get := fun name => (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) name).map (BVExpr.eval a)
    let out := shapedOut (sealK cert cw pw ew iw classes official) v
    out.take 1 = [255] →
    let content := KernelSpecs.SealFixed.contentBytes classes official
    let shape : Serialization.Shape := ⟨cw, pw, false⟩
    let pqShape : SpqrMessage.Shape := ⟨ew, iw, 1, false⟩
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop cert).take (182 + 80)) text
    let i := KernelSpecs.SealFixed.inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    SpqrSend.accepted shape pqShape i ∧
    ((out.drop (1 + cert)).take recordBytes).length = recordBytes ∧
    conv.take cert ++ (out.drop (1 + cert)).take recordBytes = KernelSpecs.SealSend.advancedRecord cert conv staged p ∧
    (out.drop (1 + convBytes cert)).take (8 + sealEnvBytes cert classes official cw pw ew iw) =
      (text.drop (2 + content)).take 8 ++
        KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
          (get "ephemeralAgreement") (get "staticAgreement") (conv.take cert) p.wire := by
  intro v a get out hst content shape pqShape staged i p
  have hso := seal_out cert cw pw ew iw classes official conv text w hc ht hb
  simp only at hso
  obtain ⟨L0, L1, L2, L3, L4⟩ := sealOut_lengths cert cw pw ew iw classes official
    (shapedAssign (sealK cert cw pw ew iw classes official).inputs (bitsOf conv ++ (bitsOf text ++ w))) hb hcl
  rw [hso] at L0 L1 L2 L3 L4
  have hout : out = (KernelSpecs.SealSend.sealValue cert cw pw ew iw content conv text (get "ephemeralPublic")
      (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement")).flatten := by
    show (List.map (fun f => f.value.map (BVExpr.eval a)) (sealK cert cw pw ew iw classes official).outputs).flatten = _
    rw [hso]
  rw [flatten4 _ L4] at hout
  obtain ⟨s0, s1, s2⟩ := slice4 _ _ _ _ cert _ L0 (by rw [L1]; rfl) L2 L3
  rw [← hout] at s0 s1 s2
  rw [hst] at s0
  have facts := KernelSpecs.SealSend.sealValue_accepted cert cw pw ew iw content conv text (get "ephemeralPublic")
    (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement") s0.symm
  simp only at facts
  obtain ⟨hA, -, -, hrec, henv⟩ := facts
  refine ⟨hA, ?_, ?_, ?_⟩
  · rw [s1, List.length_drop, L1]
    simp [convBytes]
  · rw [s1, hrec]
    have hl : (conv.take cert).length = cert := by
      simp only [List.length_take, hc, convBytes, recordBytes]; omega
    simp only [KernelSpecs.SealSend.advancedRecord, List.drop_zero, List.append_assoc]
    rw [List.drop_left' hl]
  · have hts : (KernelSpecs.SealSend.sealValue cert cw pw ew iw content conv text (get "ephemeralPublic")
        (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement")).getD 2 [] =
        (text.drop (2 + content)).take 8 := by
      simp only [KernelSpecs.SealSend.sealValue]
      split <;> rfl
    rw [show convBytes cert = cert + recordBytes from rfl, s2, hts, henv]
    simp only [List.drop_zero]
    rfl

end SealAccepted

/-! ## The request's record (`requestCtrScript` then `Tls.tagScript`) -/

/-- The bundle `requestCtrScript` concatenates: traffic ‖ sequence ‖ conversation ‖ frame ‖ mask. -/
def requestIn (K seqB conv frame mask : B8) : B8 := K ++ (seqB ++ (conv ++ (frame ++ mask)))

/-- The script's concatenation is that bundle's bits. -/
theorem requestIn_bits (K seqB conv frame mask : B8) :
    bitsOf K ++ bitsOf seqB ++ bitsOf conv ++ (bitsOf frame ++ bitsOf mask) = bitsOf (requestIn K seqB conv frame mask) := by
  simp [requestIn, List.append_assoc]

theorem iv' (l : B8) (s c : Nat) (h : s + c ≤ l.length) :
    (ByteCircuit.inputBytes s c).map (BVExpr.eval (assignOf l)) = (l.drop s).take c :=
  inputValue_assignOf l s c h

section Request

variable (cert : Nat)

/-- **`signal-request-ctr`'s view of the script's bundle**: its five inputs are the script's
traffic block, sequence, conversation, frame and mask. -/
theorem request_get (K seqB conv frame mask : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hc : conv.length = convBytes cert) (hm : mask.length = 4) :
    let get := fun name => (lookup (KernelSpecs.signalRequestInputs cert frame.length) name).map
      (BVExpr.eval (assignOf (requestIn K seqB conv frame mask)))
    get "clientApplication" = K ∧ get "sequence" = seqB ∧ get "conversation" = conv ∧ get "frame" = frame ∧
      get "mask" = mask := by
  intro get
  have hC : HybridKernel.conversationBytes cert 80 = convBytes cert := by
    simp [HybridKernel.conversationBytes, convBytes, recordBytes]
  have hlen : (requestIn K seqB conv frame mask).length = 60 + 8 + convBytes cert + frame.length + 4 := by
    simp [requestIn, hK, hs, hc, hm]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (lookup _ "clientApplication").map _ = _
    rw [show lookup (KernelSpecs.signalRequestInputs cert frame.length) "clientApplication" =
      ByteCircuit.inputBytes 0 60 by simp [lookup, lookupFrom, KernelSpecs.signalRequestInputs]]
    rw [iv' _ _ _ (by omega), List.drop_zero, requestIn, List.take_left' hK]
  · show (lookup _ "sequence").map _ = _
    rw [show lookup (KernelSpecs.signalRequestInputs cert frame.length) "sequence" =
      ByteCircuit.inputBytes 60 8 by simp [lookup, lookupFrom, KernelSpecs.signalRequestInputs, HybridKernel.Shape.variables]]
    rw [iv' _ _ _ (by omega), requestIn, List.drop_left' hK, List.take_left' hs]
  · show (lookup _ "conversation").map _ = _
    rw [show lookup (KernelSpecs.signalRequestInputs cert frame.length) "conversation" =
      ByteCircuit.inputBytes 68 (convBytes cert) by
        simp [lookup, lookupFrom, KernelSpecs.signalRequestInputs, HybridKernel.Shape.variables, hC]]
    rw [iv' _ _ _ (by omega), requestIn, ← List.append_assoc, List.drop_left' (by simp [hK, hs]),
      List.take_left' hc]
  · show (lookup _ "frame").map _ = _
    rw [show lookup (KernelSpecs.signalRequestInputs cert frame.length) "frame" =
      ByteCircuit.inputBytes (68 + convBytes cert) frame.length by
        simp [lookup, lookupFrom, KernelSpecs.signalRequestInputs, HybridKernel.Shape.variables, hC]]
    rw [iv' _ _ _ (by omega), requestIn, show K ++ (seqB ++ (conv ++ (frame ++ mask))) = (K ++ seqB ++ conv) ++ (frame ++ mask)
      by simp, List.drop_left' (by simp [hK, hs, hc]; omega), List.take_left' rfl]
  · show (lookup _ "mask").map _ = _
    rw [show lookup (KernelSpecs.signalRequestInputs cert frame.length) "mask" =
      ByteCircuit.inputBytes (68 + convBytes cert + frame.length) 4 by
        simp [lookup, lookupFrom, KernelSpecs.signalRequestInputs, HybridKernel.Shape.variables, hC]]
    rw [iv' _ _ _ (by omega), requestIn, show K ++ (seqB ++ (conv ++ (frame ++ mask))) = (K ++ seqB ++ conv ++ frame) ++ mask
      by simp, List.drop_left' (by simp [hK, hs, hc]; omega), List.take_of_length_le (by omega)]

/-- **`signal-request-ctr` on the script's bundle seals the filled request frame**:
`RequestFrame.signalRequestCtr_built` with `hframe` and `hmask` discharged by the layout (the frame and
mask the kernel reads are the script's own public bits). The frame and offsets are what
`PublicRequest.build` returned for the opened envelope (`frameFor`, the script path's definition). -/
theorem requestCtr_value (env : B8) (ts id : Nat) (mask frame : B8) (official : Bool) (offsets : List Nat)
    (hb : PublicRequest.build env ts id mask official = .ok (frame, offsets))
    (K seqB conv : B8) (hK : K.length = 60) (hs : seqB.length = 8) (hc : conv.length = convBytes cert) :
    let msg := PublicRequest.sendMessage env ts id official
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun f => f.value.map (BVExpr.eval (assignOf (requestIn K seqB conv frame mask)))) =
      KernelSpecs.sealedRequest K seqB
        (KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert conv) msg))
        (KernelSpecs.signalRequestSlots cert 0 0 0 0 conv).1 := by
  intro msg
  obtain ⟨-, -, hm, -⟩ := KernelSpecs.RequestFrame.build_ok env ts id mask frame official offsets hb
  obtain ⟨g1, g2, g3, g4, g5⟩ := request_get cert K seqB conv frame mask hK hs hc hm
  simp only at g1 g2 g3 g4 g5
  have h := KernelSpecs.RequestFrame.signalRequestCtr_built env ts id mask frame official offsets hb cert
    (assignOf (requestIn K seqB conv frame mask)) g4 g5
  simp only at h
  rw [h, g1, g2, g3]

/-- A one-output kernel's `kernelOut` (`Ghash.outputs_one`). -/
theorem tag_kernelOut (pad hA hB : B8) (hp : pad.length = 16) (ha : hA.length = 16) (hb : hB.length = 16) :
    kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes pad hA) hB := by
  obtain ⟨o, ho⟩ := Tls.tag_outputs
  have h1 := TlsMpc.Node.Flows.Ghash.outputs_one _ o ho (pad ++ (hA ++ hB))
  rw [HybridKernel.gcmTag_spec] at h1
  have t1 : HybridKernel.inputValue (assignOf (pad ++ (hA ++ hB))) 0 16 = pad := by
    rw [inputValue_assignOf _ 0 16 (by simp [hp, ha, hb]), List.drop_zero, List.take_left' hp]
  have t2 : HybridKernel.inputValue (assignOf (pad ++ (hA ++ hB))) 16 16 = hA := by
    rw [inputValue_assignOf _ 16 16 (by simp [hp, ha, hb]), List.drop_left' hp, List.take_left' ha]
  have t3 : HybridKernel.inputValue (assignOf (pad ++ (hA ++ hB))) 32 16 = hB := by
    rw [inputValue_assignOf _ 32 16 (by simp [hp, ha, hb]), ← List.append_assoc,
      List.drop_left' (by simp [hp, ha]), List.take_of_length_le (by omega)]
  rw [t1, t2, t3] at h1
  simp only [List.cons.injEq, and_true] at h1
  exact h1.symm

/-- **The request's TLS record** (P-GHASH (c) for the request sealer, as S12's `Tls.seal_is_record`):
for an accepted request (`valid = 255`), the header ‖ ciphertext `requestCtrScript` opens followed by
`gcm-tag`'s tag on its pad and the two parties' halves (`Local.Ghash.half` of shares that share
H¹ … Hⁿ for the traffic key, `n` covering the record) is `TlsRecord.sealCore`: the AES-GCM TLS record of
the plaintext `P` under the traffic block's key and IV and the sequence number. -/
theorem request_record (K seqB P : B8) (hK : K.length = 60) (a b : List Tls.W) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (innerOf P.length) ≤ nPow) :
    let o := KernelSpecs.sealedRequest K seqB P 255
    let hc := o.getD 1 [] ++ o.getD 2 []
    let pad := o.getD 3 []
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB P 23 0 := by
  intro o hc pad hA hB
  have hH := Tls.header_length ((TlsRecord.inner Gcm.concrete P 23 0).length + 16)
  have hI : (TlsRecord.inner Gcm.concrete P 23 0).length = innerOf P.length := by
    rw [Tls.inner_length]; rfl
  have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0)).length = innerOf P.length := by
    rw [HybridKernel.ctrOf_length _ _ _ hK, hI]
  have ehc : hc = TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete P 23 0).length + 16) ++
      HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0) := by
    simp only [hc, o, KernelSpecs.sealedRequest, List.getD_cons_succ, List.getD_cons_zero, ByteAuth.release_accept]
  have epad : pad = HybridKernel.padOf K seqB := by
    simp only [pad, o, KernelSpecs.sealedRequest, List.getD_cons_succ, List.getD_cons_zero]
  have e5 : hc.take 5 = TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete P 23 0).length + 16) := by
    rw [ehc, List.take_left' hH]
  have e5' : hc.drop 5 = HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0) := by
    rw [ehc, List.drop_left' hH]
  have hP := Tls.padOf_length K seqB hK
  have hAl : hA.length = 16 := Local.Ghash.toBytes_length _
  have hBl : hB.length = 16 := Local.Ghash.toBytes_length _
  have hhalves : Aes.addRoundKey Gcm.concrete.aes hA hB = HybridKernel.ghashOf K (hc.take 5) (hc.drop 5) := by
    refine Local.Ghash.halves_xor K _ _ a b nPow hsh ?_
    rw [Tls.blocks_needed, e5, e5', hH, hCT]
    exact hn
  rw [tag_kernelOut pad hA hB (by rw [epad, hP]) hAl hBl, HybridKernel.xor_rotate, hhalves, e5, e5', epad, ehc,
    HybridKernel.sealCore_decompose]

/-- The request kernel's plaintext has the frame's length (`signalRequestCtr_spec`: the slots are
inserted in place). -/
theorem requestPlain_length (env : B8) (ts id : Nat) (mask frame : B8) (official : Bool) (offsets : List Nat)
    (hb : PublicRequest.build env ts id mask official = .ok (frame, offsets))
    (K seqB conv : B8) (hK : K.length = 60) (hs : seqB.length = 8) (hc : conv.length = convBytes cert) :
    let msg := PublicRequest.sendMessage env ts id official
    (KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
      KernelSpecs.RequestFrame.maskFrom mask 0
        (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert conv) msg)).length = frame.length := by
  intro msg
  have h1 := requestCtr_value cert env ts id mask frame official offsets hb K seqB conv hK hs hc
  have h2 := KernelSpecs.signalRequestCtr_spec cert frame.length (offsets.getD 0 0) (offsets.getD 1 0)
    (offsets.getD 2 0) (offsets.getD 3 0) (assignOf (requestIn K seqB conv frame mask))
  obtain ⟨-, -, hm, -⟩ := KernelSpecs.RequestFrame.build_ok env ts id mask frame official offsets hb
  obtain ⟨g1, g2, -, g4, -⟩ := request_get cert K seqB conv frame mask hK hs hc hm
  simp only at h1 h2 g1 g2 g4
  rw [h1, g1, g2, g4] at h2
  have h3 := congrArg (fun l => (l.getD 2 []).length) h2
  simp only [KernelSpecs.sealedRequest, List.getD_cons_succ, List.getD_cons_zero, ByteAuth.release,
    List.length_map, HybridKernel.ctrOf_length _ _ _ hK, Tls.inner_length, Tls.innerLength,
    KernelSpecs.insertSlots, List.length_zipIdx] at h3
  simp only [msg, List.length_append, KernelSpecs.RequestFrame.maskFrom_length] at h3 ⊢
  omega

end Request

/-! ## The headline: an accepted send, on the script path -/

section Headline

variable (cert cw pw ew iw classes : Nat) (official : Bool)

/-- **T4-SEND / T7 on the script path** (op 41, then op 42, then the request's record seal: S12's
`Tls.tagScript` after `requestCtrScript`). Every input below is either a value the scripts compute
or open themselves, or a value of the stored state: certificate ‖ record (the conversation
`sealScript` concatenates), the built text, the four words `sealScript` feeds (ephemeral public key,
sender key, ephemeral and static agreements: S11's, E4), the traffic block and sequence, the
parties' GHASH key-power shares (P-GHASH (a)). The frame is `frameFor` of the script's own opened
envelope and timestamp; the kernels' inputs are the scripts' concatenations. So the worker-wiring
hypotheses of `SealFrame.serverReceives_accepted` (`built`, `hframe`, `hmask`) are NOT hypotheses
here: they hold by the scripts' construction.

When the status the script opened is 255 and the request's accepted byte is 255 (otherwise the
scripts return `none` / abort and nothing is sent): the reference send step accepts the stored
state; the state the script keeps, with its certificate, is `SealSend.advancedRecord` (the advanced
ratchet state); the opened envelope is the reference sealed-sender v1 envelope `sealV1` of the
reference Signal message `SpqrSend.canonical`; and what leaves for the server, header ‖ ciphertext ‖
tag, is `TlsRecord.sealCore` (the AES-GCM TLS record under the traffic key) of the WebSocket frame of
`PublicRequest.sendMessage` carrying that envelope, with the contact's UUID, access key, device and
registration ids (from the advanced record's metadata) in its slots. -/
theorem send_accepted (certB record text : B8) (w : Bits) (hcB : certB.length = cert)
    (hr : record.length = recordBytes) (ht : text.length = textBytes classes official)
    (hb : SealBound cert cw pw ew iw classes official) (hcl : 1 ≤ classes)
    (id : Nat) (mask frame : B8) (offsets : List Nat) (K seqB : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (a b : List Tls.W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) :
    let conv := certB ++ record
    let v := bitsOf conv ++ (bitsOf text ++ w)
    let sa := shapedAssign (sealK cert cw pw ew iw classes official).inputs v
    let get := fun name => (lookup (KernelSpecs.SealFixed.sealInputs cert classes official) name).map (BVExpr.eval sa)
    let out := shapedOut (sealK cert cw pw ew iw classes official) v
    let te := (out.drop (1 + convBytes cert)).take (8 + sealEnvBytes cert classes official cw pw ew iw)
    let newRecord := (out.drop (1 + cert)).take recordBytes
    let ctr := kernelOut (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0)
      (offsets.getD 2 0) (offsets.getD 3 0)) (requestIn K seqB (certB ++ newRecord) frame mask)
    let hc := (ctr.drop 1).take (5 + innerOf frame.length)
    let pad := (ctr.drop (1 + 5 + innerOf frame.length)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    out.take 1 = [255] →
    frameFor (te.drop 8) (te.take 8) id mask official = .ok (frame, offsets) →
    ctr.take 1 = [255] →
    Local.Ghash.needed 5 (innerOf frame.length) ≤ nPow →
    let content := KernelSpecs.SealFixed.contentBytes classes official
    let shape : Serialization.Shape := ⟨cw, pw, false⟩
    let pqShape : SpqrMessage.Shape := ⟨ew, iw, 1, false⟩
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop cert).take (182 + 80)) text
    let i := KernelSpecs.SealFixed.inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    let envelope := KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement") certB p.wire
    let msg := PublicRequest.sendMessage envelope (beNat (te.take 8)) id official
    SpqrSend.accepted shape pqShape i ∧
    certB ++ newRecord = KernelSpecs.SealSend.advancedRecord cert conv staged p ∧
    te.drop 8 = envelope ∧
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB
        (KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert (certB ++ newRecord)) msg))
        23 0 := by
  intro conv v sa get out te newRecord ctr hc pad hA hB hst hframe hacc hn content shape pqShape staged i p envelope msg
  have hconv : conv.length = convBytes cert := by simp [conv, hcB, hr, convBytes]
  have hct : conv.take cert = certB := List.take_left' hcB
  obtain ⟨hA', hlen, hrec, hte⟩ := seal_accepted_value cert cw pw ew iw classes official conv text w hconv ht hb hcl hst
  rw [hct] at hrec hte
  have hts : ((text.drop (2 + content)).take 8).length = 8 := by
    obtain ⟨hT, -⟩ := textBytes_eq classes official hcl
    simp only [List.length_take, List.length_drop, ht, hT]
    omega
  have henv : te.drop 8 = envelope := by
    show ((out.drop (1 + convBytes cert)).take (8 + sealEnvBytes cert classes official cw pw ew iw)).drop 8 = _
    rw [hte, List.drop_left' hts]
  refine ⟨hA', hrec, henv, ?_⟩
  -- the request
  have hb' : PublicRequest.build envelope (beNat (te.take 8)) id mask official = .ok (frame, offsets) := by
    rw [← henv]; exact hframe
  have hlen' : newRecord.length = recordBytes := hlen
  have hc2 : (certB ++ newRecord).length = convBytes cert := by
    simp only [List.length_append, hcB, hlen', convBytes]
  have hval := requestCtr_value cert envelope (beNat (te.take 8)) id mask frame official offsets hb' K seqB
    (certB ++ newRecord) hK hs hc2
  have hPl := requestPlain_length cert envelope (beNat (te.take 8)) id mask frame official offsets hb' K seqB
    (certB ++ newRecord) hK hs hc2
  simp only at hval hPl
  generalize hP : KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
    KernelSpecs.RequestFrame.maskFrom mask 0
      (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert (certB ++ newRecord)) msg) = P
    at hval hPl ⊢
  generalize hV : (KernelSpecs.signalRequestSlots cert 0 0 0 0 (certB ++ newRecord)).1 = valid at hval
  have hctr : ctr = (KernelSpecs.sealedRequest K seqB P valid).flatten := by
    show (List.map _ _).flatten = _
    rw [hval]
  have hH := Tls.header_length ((TlsRecord.inner Gcm.concrete P 23 0).length + 16)
  have hI : (TlsRecord.inner Gcm.concrete P 23 0).length = innerOf frame.length := by
    rw [Tls.inner_length, hPl]; rfl
  have hCT : ∀ m, (ByteAuth.release ByteAuth.concrete m
      (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0))).length = innerOf frame.length := by
    intro m
    simp only [ByteAuth.release, List.length_map, HybridKernel.ctrOf_length _ _ _ hK, hI]
  have hflat : ctr = [valid] ++ (TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete P 23 0).length + 16) ++
      (ByteAuth.release ByteAuth.concrete valid (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0)) ++
        HybridKernel.padOf K seqB)) := by
    rw [hctr]; simp [KernelSpecs.sealedRequest]
  have hv255 : valid = 255 := by
    have := hacc
    rw [hflat] at this
    simpa using this
  subst hv255
  have hP16 := Tls.padOf_length K seqB hK
  have ehc : hc = (KernelSpecs.sealedRequest K seqB P 255).getD 1 [] ++ (KernelSpecs.sealedRequest K seqB P 255).getD 2 [] := by
    show (ctr.drop 1).take (5 + innerOf frame.length) = _
    rw [hflat, List.singleton_append, List.drop_succ_cons, List.drop_zero, ← List.append_assoc,
      List.take_left' (by rw [List.length_append, hH, hCT 255])]
    simp [KernelSpecs.sealedRequest]
  have epad : pad = (KernelSpecs.sealedRequest K seqB P 255).getD 3 [] := by
    show (ctr.drop (1 + 5 + innerOf frame.length)).take 16 = _
    rw [hflat, ← List.append_assoc, ← List.append_assoc,
      List.drop_left' (by rw [List.length_append, List.length_append, hH, hCT 255]; rfl),
      List.take_of_length_le (by omega)]
    simp [KernelSpecs.sealedRequest]
  have hrecord := request_record K seqB P hK a b nPow hsh (by rw [hPl]; exact hn)
  simp only at hrecord
  rw [← ehc, ← epad] at hrecord
  exact hrecord

end Headline

/-! ## Well-formedness -/

/-- **`requestScript` is well formed** (op 42): the certificate and the state live and not once (the
state at least one record wide), the counter fresh. It leaves the request's conversation. -/
theorem requestScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (cert state : BoolH)
    (cm sm : List Mark) (hf : Fresh c n) (hcn : cert.id < n)
    (hc : c.bool? cert = some ⟨cm, false⟩) (hs : c.bool? state = some ⟨sm, false⟩)
    (hsm : 8 * recordBytes ≤ sm.length) (hw : cm.length + 8 * recordBytes ≤ maxWidth) :
    WF sigs c (requestScript n cert state) := by
  unfold requestScript
  simp only [seqs_cons, seqs_nil]
  have c0 : cert.id ≠ n := by omega
  have hwM := maxWidth_eq
  refine WF_seq sigs c _ _ _ (check_slice sigs (useBool_keep hs rfl) ⟨Nat.zero_le _, hsm⟩ hf
    (by simp only [recordBytes] at hw ⊢; omega)) ?_
  have hf1 := hf.push n (Nat.le_refl n) ⟨(sm.drop 0).take (8 * recordBytes - 0), false⟩
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ c0).trans hc) rfl)
      (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl) (useBools_nil _))) hf1
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_take, List.drop_zero, Nat.sub_zero, recordBytes] at hw ⊢; omega)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    rw [bool?_push_of_ne _ _ _ _ (show n ≠ n + 1 by omega), bool?_push_self]; rfl)) (WF.done _ _)

/-- **`requestCtrScript` is well formed** (the request's record, first phase): the traffic block
(480 private bits) and the request's conversation (any marks, `8 · C` bits) live and not once, the
counter fresh, the request kernel's signature (inputs 68 + C + |frame| + 4 bytes; accepted, header,
ciphertext public, the pad private). -/
theorem requestCtrScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic conv : BoolH)
    (seq frame mask : B8) (name : Bytes) (C : Nat) (cm : List Mark) (hf : Fresh c n) (htn : traffic.id < n)
    (hcn : conv.id < n)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hc : c.bool? conv = some ⟨cm, false⟩)
    (hcm : cm.length = 8 * C) (hs : seq.length = 8) (hm : mask.length = 4) (hsize : C + frame.length ≤ 65536)
    (hsig : sigs name = some ⟨8 * (68 + C + frame.length + 4),
      List.replicate (8 * (1 + 5 + innerOf frame.length)) .pub ++ List.replicate 128 .never⟩) :
    WF sigs c (requestCtrScript n traffic conv seq frame mask name) := by
  unfold requestCtrScript
  simp only [seqs_cons, seqs_nil, innerOf] at hsig ⊢
  have t0 : traffic.id ≠ n := by omega
  have t1 : traffic.id ≠ n + 1 := by omega
  have k0 : conv.id ≠ n := by omega
  have k1 : conv.id ≠ n + 1 := by omega
  have hwM := maxWidth_eq
  generalize hH : 8 * (1 + 5 + (frame.length + 1)) = H at hsig ⊢
  have hHv : H = 8 * (7 + frame.length) := by rw [← hH]; omega
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp [hs, hwM])) ?_
  have hf1 := hf.push n (Nat.le_refl n) ⟨List.replicate (bitsOf seq).length .pub, false⟩
  refine WF_seq sigs _ _ _ _ (check_boolPublic sigs hf1 _ (by simp [hm, hwM]; omega)) ?_
  have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨List.replicate (bitsOf frame ++ bitsOf mask).length .pub, false⟩
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ t1).trans ((bool?_push_of_ne _ _ _ _ t0).trans ht)) rfl)
      (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (show n ≠ n + 1 by omega)).trans
          (bool?_push_self _ _ _)) rfl)
        (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ k1).trans ((bool?_push_of_ne _ _ _ _ k0).trans hc)) rfl)
          (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl) (useBools_nil _))))) hf2
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, length_bitsOf, hs, hm, hcm, hwM]; omega)) ?_
  have hf3 := hf2.push (n + 2) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨List.replicate 480 Mark.never, false⟩,
    ⟨List.replicate (bitsOf seq).length .pub, false⟩, ⟨cm, false⟩,
    ⟨List.replicate (bitsOf frame ++ bitsOf mask).length .pub, false⟩]).flatten, false⟩
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, length_bitsOf, hs, hm, hcm]; omega) hf3 (by decide)
    (by simp only [List.length_append, List.length_replicate, hwM]; omega)) ?_
  have hL : (List.replicate 1 (List.replicate H Mark.pub ++ List.replicate 128 Mark.never)).flatten =
      List.replicate H Mark.pub ++ List.replicate 128 Mark.never := by simp
  have hf4 := hf3.push (n + 3) (Nat.le_refl _) ⟨(List.replicate 1 (List.replicate H Mark.pub ++
    List.replicate 128 Mark.never)).flatten, false⟩
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (bool?_push_self _ _ _) rfl)
    (by simp only [hL, List.length_append, List.length_replicate]; omega) hf4 (by rw [hwM]; omega)) ?_
  have hf5 := hf4.push (n + 4) (Nat.le_refl _) ⟨(((List.replicate 1 (List.replicate H Mark.pub ++
    List.replicate 128 Mark.never)).flatten).drop H).take (H + 128 - H), false⟩
  refine WF_seq sigs _ _ _ _ (check_slice sigs
    (useBool_keep ((bool?_push_of_ne _ _ _ _ (show n + 3 ≠ n + 4 by omega)).trans (bool?_push_self _ _ _)) rfl)
    (by simp only [hL, List.length_append, List.length_replicate]; omega) hf5 (by rw [hwM]; omega)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_push, show n ≠ n + 5 by omega, show n ≠ n + 4 by omega, show n ≠ n + 3 by omega,
      show n ≠ n + 2 by omega, show n ≠ n + 1 by omega, if_false, if_true]; rfl)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_drop, bool?_push, show n + 1 ≠ n by omega, show n + 1 ≠ n + 5 by omega,
      show n + 1 ≠ n + 4 by omega, show n + 1 ≠ n + 3 by omega, show n + 1 ≠ n + 2 by omega, if_false, if_true]
    rfl)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_drop, bool?_push, show n + 2 ≠ n by omega, show n + 2 ≠ n + 1 by omega,
      show n + 2 ≠ n + 5 by omega, show n + 2 ≠ n + 4 by omega, show n + 2 ≠ n + 3 by omega, if_false, if_true]
    rfl)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_drop, bool?_push, show n + 3 ≠ n by omega, show n + 3 ≠ n + 1 by omega,
      show n + 3 ≠ n + 2 by omega, show n + 3 ≠ n + 5 by omega, show n + 3 ≠ n + 4 by omega, if_false, if_true]
    rfl)) ?_
  have kk : conv.id ≠ n + 2 := by omega
  have kk3 : conv.id ≠ n + 3 := by omega
  have kk4 : conv.id ≠ n + 4 := by omega
  have kk5 : conv.id ≠ n + 5 := by omega
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_drop, bool?_push, k0, k1, kk, kk3, kk4, kk5, if_false, hc]; rfl)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  have p5 : n + 5 ≠ n := by omega
  have p51 : n + 5 ≠ n + 1 := by omega
  have p52 : n + 5 ≠ n + 2 := by omega
  have p53 : n + 5 ≠ n + 3 := by omega
  have p5c : n + 5 ≠ conv.id := by omega
  rw [check_openBool sigs (by decide) (useBool_keep (by
      simp only [bool?_drop, bool?_push, p5, p51, p52, p53, p5c, if_false, if_true]; rfl) rfl) (by
    rw [List.all_eq_true]
    intro x hx
    simp only [hL, List.drop_zero, Nat.sub_zero] at hx
    rw [List.take_left' (by simp)] at hx
    rw [(List.mem_replicate.mp hx).2]
    rfl)]
  intro bits _
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_drop, bool?_push, p5, p51, p52, p53, p5c, if_false, if_true]; rfl)) ?_
  split
  · exact WF.done _ _
  · exact WF.abort _ _

end TlsMpc.Node.Flows.Send
