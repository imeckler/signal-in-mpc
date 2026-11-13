import TlsMpc.Node.Engine
import TlsMpc.Node.Types

/-!
# The release labels: one registry for every flow, derived from `RevealKind`

REORGANIZATION_PLAN.md 5.4 (the open rule), stage S9, reconciled with stage S6. Every release
instruction (`openBool`, `openBoolTo`, `openField`, `exchange`) carries a `Label`, and the label is
part of the agreed skeleton (Engine.lean decision D7). The labels ARE the reveal kinds of the reveal
list (`RevealKind`, TlsMpc/Node/Types.lean; the list itself, per kind, in TlsMpc/Node/Reveal.lean):
`Label.ofKind k` is the label whose code is `RevealKind.code k`. This file is the bridge: Engine.lean
stays independent of Types.lean (the instruction set and the shell's `check` know only numbers), and
every flow takes its labels from here.

Rules: a flow never writes a literal `⟨n⟩` label; every named label below is `ofKind` of a kind
and listed in `all` (= `kinds.map ofKind`); `all_distinct` (no two labels share a code) and
`all_nonzero` (code 0 is refused by `check`) follow from `RevealKind.codes_distinct` and
`RevealKind.code_ne_zero`. `ofKind_inj`: a label names its kind. Engine/Reveal.lean states, per
script, which kinds its releases carry (`Reveals`), and proves that the views contain nothing else.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Engine.Label

open TlsMpc.Node (RevealKind)

/-- **The label of a reveal kind**: its fixed code (`RevealKind.code`). -/
def ofKind (k : RevealKind) : Label := ⟨k.code⟩

@[simp] theorem code_ofKind (k : RevealKind) : (ofKind k).code = k.code := rfl

/-- No kind's code is 0 (`RevealKind.code_ne_zero`); in the form `simp` uses on `check`'s guard. -/
@[simp] theorem kind_code_ne_zero (k : RevealKind) : k.code ≠ 0 := RevealKind.code_ne_zero k

/-- **Every kind's label is a label** (`check` refuses code 0). -/
theorem ofKind_ne_zero (k : RevealKind) : (ofKind k).code ≠ 0 := RevealKind.code_ne_zero k

/-- Every kind's code fits the pipe's u64 (`Wire.Bounded`); in the form `simp` uses. -/
@[simp] theorem kind_code_lt (k : RevealKind) : k.code < B64 := by
  cases k <;> decide

/-- Every kind's label fits the pipe's u64 (`Wire.Bounded`). -/
theorem ofKind_code_lt (k : RevealKind) : (ofKind k).code < B64 := kind_code_lt k

/-- A function whose image of a list is duplicate free is injective on the list. -/
theorem inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd ⟨y, hy, hxy.symm⟩ h.1
    · exact absurd ⟨x, hx, hxy⟩ h.1
    · exact inj_of_nodup_map f h.2 x hx y hy hxy

/-- **A code names its kind** (`RevealKind.codes_distinct`, `RevealKind.mem_all`). -/
theorem code_inj {a b : RevealKind} (h : a.code = b.code) : a = b :=
  inj_of_nodup_map RevealKind.code RevealKind.codes_distinct a (RevealKind.mem_all a) b (RevealKind.mem_all b) h

/-- **A label names its kind.** -/
@[simp] theorem ofKind_inj {a b : RevealKind} : ofKind a = ofKind b ↔ a = b :=
  ⟨fun h => code_inj (congrArg Label.code h), fun h => h ▸ rfl⟩

/-- `Random.joint` (op 33): this party's commitment. Kind `commitment` (code 100). -/
def jointRandomCommitment : Label := ofKind .commitment
/-- `Random.joint` (op 33): the commitment's opening (nonce, value). Kind `commitOpening` (code 101). -/
def jointRandomOpening : Label := ofKind .commitOpening
/-- The `accepted` byte of `contact-open` (ops 37, 55, 63). Kind `blobAccepted` (code 30). -/
def blobAccepted : Label := ofKind .blobAccepted
/-- Ciphertext and check value of `contact-seal` (ops 38, 54, 64). Kind `sealedBlob` (code 31). -/
def sealedBlob : Label := ofKind .sealedBlob

/-! Conversions and masks (stage S10, kinds 80–87; masked inversion, kind 90). -/

/-- Bits to field (P-B2F): the opened `x ⊕ ρ`. Kind `maskedBit` (code 80). -/
def maskedBit : Label := ofKind .maskedBit
/-- Word to field (P-W2F): the opened `(u mod p + r) mod p` and its re-comparison. Kind `maskedWord` (81). -/
def maskedWord : Label := ofKind .maskedWord
/-- Field to word (P-F2W): the opened `v − f` and its re-comparison. Kind `maskedFieldValue` (82). -/
def maskedFieldValue : Label := ofKind .maskedFieldValue
/-- Mask generation (P-CUT): the opened cut candidates, both engines. Kind `cutCandidates` (83). -/
def cutCandidates : Label := ofKind .cutCandidates
/-- Mask generation: per bucket member the two sums. Kind `bucketSums` (84). -/
def bucketSums : Label := ofKind .bucketSums
/-- Mask generation: one flag bit per kept reference. Kind `referenceFlags` (85). -/
def referenceFlags : Label := ofKind .referenceFlags
/-- Mask generation, bit blocks: the recomposition and bit checks. Kind `bitBlockChecks` (86). -/
def bitBlockChecks : Label := ofKind .bitBlockChecks
/-- Shared scalars as field bits (P-BITS): the bit checks. Kind `scalarBitChecks` (87). -/
def scalarBitChecks : Label := ofKind .scalarBitChecks
/-- Masked inversion (P-INV): the openings `b·m` of the `D`/`Z` rows and the zero flag. Kind
`maskedDenominator` (90). -/
def maskedDenominator : Label := ofKind .maskedDenominator

/-! The curve flows (stage S11, kinds 91–95 and 102; `Flows/Curve.lean`). -/

/-- Check values that must open to zero: curve checks of input points (split ECDH, the lift's mask
points), the scalar-bit and curve checks of `edwards-prepare`; also the (empty) release of a
program without `D`/`Z` rows in a curve flow. Kind `curveChecks` (91). -/
def curveChecks : Label := ofKind .curveChecks
/-- The lift's opened `w = q·r²·2^b`. Kind `liftW` (92). -/
def liftW : Label := ofKind .liftW
/-- The lift's opened masked point `Z = P + M_A + M_B`. Kind `liftZ` (93). -/
def liftZ : Label := ofKind .liftZ
/-- The lift's validity bit, opened only by contact preparation (op 66). Kind `pointValid` (94). -/
def pointValid : Label := ofKind .pointValid
/-- The masked links of hinted tables, with the scalar-bit checks of `edwards-prepare-hinted`
(opened together, all must be zero). Kind `linkChecks` (95). -/
def linkChecks : Label := ofKind .linkChecks
/-- This party's public point of its own scalar (the split-ECDH share k·B, the K₀ half), opened
after its commitment (`commitment`). Kind `ownPublicPoint` (102). -/
def ownPublicPoint : Label := ofKind .ownPublicPoint

/-! TLS and GHASH shares (stage S12, kinds 2-9). -/

/-- `tls-open-handshake`'s gated result (type 21/22 and plaintext only). Kind `handshakeRecord` (2). -/
def handshakeRecord : Label := ofKind .handshakeRecord
/-- `tls-verify-finished`'s acceptance byte. Kind `finishedAccepted` (3). -/
def finishedAccepted : Label := ofKind .finishedAccepted
/-- `tls-finish`'s sealed client Finished record. Kind `clientFinished` (4). -/
def clientFinished : Label := ofKind .clientFinished
/-- `tls-open-typed`'s one bit "authenticated handshake record". Kind `recordKindBit` (5). -/
def recordKindBit : Label := ofKind .recordKindBit
/-- A received record's event bytes (`tls-open-typed` or `tls-frame`). Kind `recordEvent` (6). -/
def recordEvent : Label := ofKind .recordEvent
/-- A sealed record's header and ciphertext (`tls-seal-*`), its tag (`gcm-tag`), and a class
kernel's `accepted` byte. Kind `sealedRecord` (7). -/
def sealedRecord : Label := ofKind .sealedRecord
/-- An authenticated record's length and revealed bytes (`tls-reveal-masked`). Kind `serverBytes` (8). -/
def serverBytes : Label := ofKind .serverBytes
/-- A GHASH key power (or product) masked by A's fresh mask, opened to B only (`gcm-key-share`,
`gcm-multiply`). Kind `ghashMaskedPower` (9). -/
def ghashMaskedPower : Label := ofKind .ghashMaskedPower

/-! Send (stage S13, kinds 40-41). -/

/-- `signal-widths`'s width flags of a send's counters (ops 41, 61). Kind `counterWidths` (40). -/
def counterWidths : Label := ofKind .counterWidths
/-- A seal kernel's gated status (`signal-seal-official` / `-built`, `bundle-seal`), and after an
accepted status its timestamp and envelope (ops 41, 61). Kind `sealedEnvelope` (41). -/
def sealedEnvelope : Label := ofKind .sealedEnvelope

/-! Receive a first message (stage S14, kinds 50-57). -/

/-- `receive-unseal-message`'s opened certificate length prefix (two bytes, zero unless the
sealed-sender layer verified). Kind `certificateLength` (50). -/
def certificateLength : Label := ofKind .certificateLength
/-- `receive-content-shape`'s four bytes (plain / hinted, phone number and its length). Kind
`contentShape` (51). -/
def contentShape : Label := ofKind .contentShape
/-- `receive-prekey-shape`'s 21 width flags. Kind `prekeyShape` (52). -/
def prekeyShape : Label := ofKind .prekeyShape
/-- `receive-prekey-open`'s prekey ids and Kyber ciphertext (one opening). Kind `prekeyIds` (53). -/
def prekeyIds : Label := ofKind .prekeyIds
/-- `receive-signal-shape`'s 13 bytes (counter widths, ciphertext length, addresses). Kind
`signalShape` (54). -/
def signalShape : Label := ofKind .signalShape
/-- The status byte of `receive-session` and of `receive-text`. Kind `sessionStatus` (55). -/
def sessionStatus : Label := ofKind .sessionStatus
/-- `receive-text`'s length, body and layout flags (one opening, after its status). Kind
`receivedText` (56). -/
def receivedText : Label := ofKind .receivedText
/-- `receive-access-key`'s status byte. Kind `accessKeyStatus` (57). -/
def accessKeyStatus : Label := ofKind .accessKeyStatus

/-! Device refresh (stage S15, kinds 60-62). -/

/-- `bundle-shape`'s one flag per body byte (JSON punctuation or not). Kind `bundleShape` (60). -/
def bundleShape : Label := ofKind .bundleShape
/-- `bundle-rebind`'s `changed` byte (the bundle's identity key is a new one), first device only.
Kind `identityChanged` (61). -/
def identityChanged : Label := ofKind .identityChanged
/-- `establish-session`'s `status` byte, one per device. Kind `deviceStatus` (62). -/
def deviceStatus : Label := ofKind .deviceStatus

/-- The kinds the script flows release under, in the order of `all`. -/
def kinds : List RevealKind :=
  [.commitment, .commitOpening, .blobAccepted, .sealedBlob,
   .maskedBit, .maskedWord, .maskedFieldValue, .cutCandidates, .bucketSums, .referenceFlags,
   .bitBlockChecks, .scalarBitChecks, .maskedDenominator,
   .curveChecks, .liftW, .liftZ, .pointValid, .linkChecks, .ownPublicPoint,
   .handshakeRecord, .finishedAccepted, .clientFinished, .recordKindBit, .recordEvent, .sealedRecord,
   .serverBytes, .ghashMaskedPower, .counterWidths, .sealedEnvelope,
   .certificateLength, .contentShape, .prekeyShape, .prekeyIds, .signalShape, .sessionStatus,
   .receivedText, .accessKeyStatus,
   .bundleShape, .identityChanged, .deviceStatus]

/-- Every label a flow uses. -/
def all : List Label :=
  [jointRandomCommitment, jointRandomOpening, blobAccepted, sealedBlob,
   maskedBit, maskedWord, maskedFieldValue, cutCandidates, bucketSums, referenceFlags,
   bitBlockChecks, scalarBitChecks, maskedDenominator,
   curveChecks, liftW, liftZ, pointValid, linkChecks, ownPublicPoint,
   handshakeRecord, finishedAccepted, clientFinished, recordKindBit, recordEvent, sealedRecord,
   serverBytes, ghashMaskedPower, counterWidths, sealedEnvelope,
   certificateLength, contentShape, prekeyShape, prekeyIds, signalShape, sessionStatus,
   receivedText, accessKeyStatus,
   bundleShape, identityChanged, deviceStatus]

/-- **The registry is the kinds' labels**: every label of `all` is `ofKind` of a kind. -/
theorem all_eq : all = kinds.map ofKind := rfl

theorem mem_all_iff (l : Label) : l ∈ all ↔ ∃ k ∈ kinds, l = ofKind k := by
  rw [all_eq, List.mem_map]
  exact ⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩⟩

theorem kinds_nodup : kinds.Nodup := by decide

/-- **The labels are pairwise distinct**, so a release's label names its kind: from
`RevealKind.codes_distinct` (through `code_inj`) and the kinds being distinct. -/
theorem all_distinct : (all.map (·.code)).Nodup := by
  rw [all_eq, List.map_map]
  show (kinds.map RevealKind.code).Nodup
  refine List.Pairwise.map _ (fun a b hab e => hab (code_inj e)) kinds_nodup

/-- **Every label is a label** (`check` refuses code 0): from `RevealKind.code_ne_zero`. -/
theorem all_nonzero : ∀ l ∈ all, l.code ≠ 0 := by
  intro l hl
  obtain ⟨k, -, rfl⟩ := (mem_all_iff l).mp hl
  exact ofKind_ne_zero k

/-- The codes, for the record (the Rust test vectors carry them). -/
theorem all_codes : all.map (·.code) =
    [100, 101, 30, 31, 80, 81, 82, 83, 84, 85, 86, 87, 90, 91, 92, 93, 94, 95, 102,
     2, 3, 4, 5, 6, 7, 8, 9, 40, 41, 50, 51, 52, 53, 54, 55, 56, 57, 60, 61, 62] := rfl

end TlsMpc.Node.Engine.Label
