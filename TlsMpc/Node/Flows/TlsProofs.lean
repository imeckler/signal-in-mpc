import TlsMpc.Node.Flows.Tls

/-!
# T4-TLS for the open, the reveal and the handshake; well-formedness of the TLS scripts

REORGANIZATION_PLAN.md stage S12 (T3/T4-TLS, function level, composed with the kernel
theorems). The seal's composition is `Tls.seal_is_record`. Each statement here is about the bytes
a script feeds a kernel (its input bundle, `bytesOf` of the concatenated bits) and what the
script opens or keeps from the output (`kernelOut`, the output fields concatenated): the
kernel's theorem read through the script's layout.

  Open: `check_accepts` (`gcmCheck_spec` + P-GHASH (c): the private acceptance byte is 255
    exactly when the received tag is the AES-GCM tag of the received header and ciphertext under
    the server key, `ghashOf ⊕ padOf`, for the two parties' honest halves), `open_event_refines`
    (`typed_pair_refines`, `class_fields`: the bit is 0 or 255; on 0 the typed kernel's event,
    parser, length and content are the single class kernel's; on 255 `tls-frame`'s are; and those
    are `fields (classSpec …)`, the post-handshake parser on the record's parse),
    `open_rejected` (`tlsOpenTyped_gated`: with the acceptance byte 0, the opened fields are the
    bit 0 and the event [0, 0], whatever the record).
  Reveal: `reveal_value` (`tlsRevealMasked_value`: the length, and the content below the length,
    zeros above; all zeros past the capacity).
  Handshake: `openHandshake_value` (`tlsOpenHandshake_spec`), `verify_value`
    (`tlsVerifyFinished_spec`), `finish_value` (`tlsFinish_spec`).
  WF: `sealCtrScript_wf`, `tagScript_wf`, `updateScript_wf`, `publicScript_wf`, `rangeScript_wf`,
    `dropScript_wf`.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open Std.Tactic.BVDecide
open TlsMpc.HybridKernel (lookup lookupFrom inputValue)

theorem iv (l : B8) (s c : Nat) (h : s + c ≤ l.length) : inputValue (assignOf l) s c = (l.drop s).take c :=
  inputValue_assignOf l s c h

/-! ## Open -/

/-- **T4-TLS, the tag check** (`gcm-check` in `openScript`, P-GHASH (c)). With the server traffic
block `K`, the sequence, this party's and the peer's halves over the received header `hdr` and
ciphertext `ct` (from shares that share H¹ … Hⁿ of `H = hashKeyOf K`, `n` covering the blocks) and
the received tag: the kernel's private acceptance byte is 255 exactly when the tag is GCM's tag
`GHASH ⊕ pad` of that header and ciphertext (the tag `TlsRecord.sealCore` puts there:
`sealCore_decompose`), and 0 otherwise. -/
theorem check_accepts (K seqB hdr ct tag : B8) (hK : K.length = 60) (hs : seqB.length = 8) (ht : tag.length = 16)
    (a b : List W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow) :
    kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes (Local.Ghash.half a hdr ct) ++
        (Local.Ghash.toBytes (Local.Ghash.half b hdr ct) ++ tag)))) =
      [if Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) = tag
        then 255 else 0] := by
  have hhalves := Local.Ghash.halves_xor K hdr ct a b nPow hsh hn
  have hA := Local.Ghash.toBytes_length (Local.Ghash.half a hdr ct)
  have hB := Local.Ghash.toBytes_length (Local.Ghash.half b hdr ct)
  generalize Local.Ghash.toBytes (Local.Ghash.half a hdr ct) = xa at hA hhalves ⊢
  generalize Local.Ghash.toBytes (Local.Ghash.half b hdr ct) = xb at hB hhalves ⊢
  have e1 : inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 0 60 = K := by
    rw [iv _ _ _ (by simp; omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid [] K (seqB ++ (xa ++ (xb ++ tag))) 0 rfl
    rw [hK] at this
    simpa using this
  have e2 : inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 60 8 = seqB := by
    rw [iv _ _ _ (by simp; omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid K seqB (xa ++ (xb ++ tag)) 60 hK
    rw [hs] at this
    exact this
  have e3 : inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 68 16 = xa := by
    rw [iv _ _ _ (by simp; omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid (K ++ seqB) xa (xb ++ tag) 68 (by simp; omega)
    rw [hA] at this
    simpa [List.append_assoc] using this
  have e4 : inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 84 16 = xb := by
    rw [iv _ _ _ (by simp; omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid (K ++ seqB ++ xa) xb tag 84 (by simp; omega)
    rw [hB] at this
    simpa [List.append_assoc] using this
  have e5 : inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 100 16 = tag := by
    rw [iv _ _ _ (by simp; omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid (K ++ seqB ++ xa ++ xb) tag [] 100 (by simp; omega)
    rw [ht] at this
    simpa [List.append_assoc] using this
  obtain ⟨o, ho⟩ : ∃ o, HybridKernel.gcmCheck.outputs = [o] := ⟨_, rfl⟩
  have hk := TlsMpc.Node.Flows.Ghash.outputs_one _ o ho (K ++ (seqB ++ (xa ++ (xb ++ tag))))
  rw [HybridKernel.gcmCheck_spec, e1, e2, e3, e4, e5] at hk
  simp only [List.cons.injEq, and_true] at hk
  rw [← hk, HybridKernel.xor_rotate, hhalves]

/-- **A forged record is refused by the check**: if the received tag is not GCM's tag of the
header and ciphertext under the server key, the acceptance byte is 0 (so `tls-open-typed` gates
everything it opens: `open_rejected`). -/
theorem check_rejects (K seqB hdr ct tag : B8) (hK : K.length = 60) (hs : seqB.length = 8) (ht : tag.length = 16)
    (a b : List W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow)
    (hforged : Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) ≠ tag) :
    kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes (Local.Ghash.half a hdr ct) ++
        (Local.Ghash.toBytes (Local.Ghash.half b hdr ct) ++ tag)))) = [0] := by
  rw [check_accepts K seqB hdr ct tag hK hs ht a b nPow hsh hn, if_neg hforged]

open TlsMpc.TypedOpenKernel in
/-- **T4-TLS, the typed open** (`typed_pair_refines`, `class_fields`). What `openScript` opens and
keeps is what the single class kernel `tls-open-application-class` computes, and that is the
post-handshake parser on the record's parse (`fields (classSpec …)`): the opened bit (field 0 of
`tls-open-typed`) is 0 or 255; on 0 the script opens the typed kernel's event and keeps its parser,
length and content (fields 1-4); on 255 it runs `tls-frame` on the same parser state and the
private parse (hypotheses `hp`, `hq`: the script's concat binds exactly those) and opens and keeps
its four fields. -/
theorem open_event_refines (cap : Nat) (typed frame : BVExpr.Assignment)
    (hp : (lookup (frameInputs cap) "parser").map (BVExpr.eval frame) =
      (lookup (typedInputs cap) "parser").map (BVExpr.eval typed))
    (hq : (lookup (frameInputs cap) "parsed").map (BVExpr.eval frame) = (typedParsed cap).map (BVExpr.eval typed)) :
    ((fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [0] ∨ (fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [255]) ∧
    ((fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [0] →
      ((fieldValues (tlsOpenTyped cap) typed).drop 1).take 4 = fields (classSpec cap typed)) ∧
    ((fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [255] →
      fieldValues (tlsFrame cap) frame = fields (classSpec cap typed)) := by
  obtain ⟨h1, h2, h3⟩ := typed_pair_refines cap typed frame
  have hc := class_fields cap typed
  have hbit : (fieldValues (tlsOpenTyped cap) typed).getD 0 [] =
      [BVExpr.eval typed (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed cap))] := rfl
  have hlen : (fieldValues (RecordClassKernel.tlsOpenApplicationClass cap) typed).length = 4 := by
    simp only [fieldValues, List.length_map]
    rfl
  rw [hbit]
  refine ⟨?_, fun h => ?_, fun _ => by rw [h3 hp hq, hc]⟩
  · rcases h1 with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · have h0 : BVExpr.eval typed (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed cap)) = 0 := by
      simpa using h
    rw [h2 h0, ← hc]
    simp only [List.singleton_append, List.drop_succ_cons, List.drop_zero]
    exact List.take_left' hlen

open TlsMpc.TypedOpenKernel in
/-- **A rejected record opens nothing** (`tlsOpenTyped_gated`): when the acceptance byte bound to
`tls-open-typed` is 0, the two fields the script may open are the bit 0 and the event [0, 0],
whatever the record, the keys and the parser state. -/
theorem open_rejected (cap : Nat) (assign : BVExpr.Assignment)
    (h : BVExpr.eval assign (HybridService.at' (lookup (typedInputs cap) "accepted") 0) = 0) :
    ((tlsOpenTyped cap).outputs.filter (·.opened)).map (fun field => field.value.map (BVExpr.eval assign)) =
      [[0], [0, 0]] :=
  tlsOpenTyped_gated cap assign h

/-! ## Reveal -/

theorem keepBelow_eq : ∀ (c : B8) (o n : Nat),
    KernelSpecs.Reveal.keepBelow o n c = c.take (n - o) ++ List.replicate (c.length - (n - o)) 0
  | [], o, n => by simp [KernelSpecs.Reveal.keepBelow]
  | x :: xs, o, n => by
    simp only [KernelSpecs.Reveal.keepBelow]
    rw [keepBelow_eq xs (o + 1) n]
    by_cases h : o < n
    · rw [if_pos h]
      have e : n - o = (n - (o + 1)) + 1 := by omega
      rw [e, List.take_succ_cons, List.length_cons,
        show xs.length + 1 - (n - (o + 1) + 1) = xs.length - (n - (o + 1)) by omega]
      simp
    · rw [if_neg h]
      have e1 : n - o = 0 := by omega
      have e2 : n - (o + 1) = 0 := by omega
      rw [e1, e2]
      simp [List.replicate_succ]

/-- **What the reveal kernel opens** (`tlsRevealMasked_value`), on the bytes `revealScript` feeds
it: the two length bytes, then the content below the length `lengthOf len` and zeros above it (all
zeros when the length exceeds the capacity). -/
theorem reveal_value (cap : Nat) (hcap : cap < 65536) (len content : B8) (hl : len.length = 2)
    (hc : content.length = cap) :
    kernelOut (HybridKernel.tlsRevealMasked cap) (len ++ content) =
      len ++ (if lengthOf len ≤ cap then content.take (lengthOf len) ++ List.replicate (cap - lengthOf len) 0
        else List.replicate cap 0) := by
  have hv := KernelSpecs.Reveal.tlsRevealMasked_value cap hcap (assignOf (len ++ content))
  have g1 : (lookup (KernelSpecs.Reveal.revealInputs cap) "length").map (BVExpr.eval (assignOf (len ++ content))) = len := by
    have : lookup (KernelSpecs.Reveal.revealInputs cap) "length" = ByteCircuit.inputBytes 0 2 := by
      simp [lookup, lookupFrom, KernelSpecs.Reveal.revealInputs]
    rw [this]
    show inputValue _ 0 2 = _
    rw [iv _ _ _ (by simp; omega), List.drop_zero, List.take_left' hl]
  have g2 : (lookup (KernelSpecs.Reveal.revealInputs cap) "content").map (BVExpr.eval (assignOf (len ++ content))) = content := by
    have : lookup (KernelSpecs.Reveal.revealInputs cap) "content" = ByteCircuit.inputBytes 2 cap := by
      simp [lookup, lookupFrom, KernelSpecs.Reveal.revealInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 2 cap = _
    rw [iv _ _ _ (by simp; omega), List.drop_left' hl, List.take_of_length_le (by omega)]
  simp only [g1, g2] at hv
  have hlv : TlsPrivateSeal.lengthValue (len.getD 0 0) (len.getD 1 0) = lengthOf len := rfl
  rw [hlv, keepBelow_eq, Nat.sub_zero, hc] at hv
  simp only [kernelOut, hv, List.flatten_cons, List.flatten_nil, List.append_nil]
  try (split <;> rfl)

/-- **A range below the length is the content itself**: what `rangeScript` opens from the masked
bytes, for `lo ≤ hi ≤ length ≤ capacity`, is the server's bytes `[lo, hi)`. -/
theorem range_value (content : B8) (n lo hi : Nat) (hhi : hi ≤ n) (hn : n ≤ content.length) :
    (((content.take n ++ List.replicate (content.length - n) 0).drop lo).take (hi - lo)) =
      (content.drop lo).take (hi - lo) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_append_left, List.length_take]
  by_cases hi' : i < hi - lo
  · simp only [hi', if_true]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
    simp only [show lo + i < n by omega, if_true]
  · simp [hi']

/-! ## Handshake -/

open TlsMpc.KernelSpecs.TlsHandshake in
/-- **What `openHandshakeScript` opens** (`tlsOpenHandshake_spec`): the public-handshake gate of the
RFC 8446 record opening of the record under the server handshake key and IV (bytes 32-47 and
48-59 of the block), with the sequence bytes. -/
theorem openHandshake_value (size : Nat) (S seqB record : B8) (hS : S.length = 60) (hs : seqB.length = 8)
    (hr : record.length = size) :
    kernelOut (HybridKernel.tlsOpenHandshake size) (S ++ (seqB ++ record)) =
      TlsPublicHandshake.gate ByteAuth.concrete
        (TlsReceive.spec ((S.drop 32).take 16) ((S.drop 48).take 12) seqB record) := by
  have hv := tlsOpenHandshake_spec size (assignOf (S ++ (seqB ++ record)))
  have g1 : (lookup (openInputs size) "serverHandshake").map (BVExpr.eval (assignOf (S ++ (seqB ++ record)))) = S := by
    have : lookup (openInputs size) "serverHandshake" = ByteCircuit.inputBytes 0 60 := by
      simp [lookup, lookupFrom, openInputs]
    rw [this]
    show inputValue _ 0 60 = _
    rw [iv _ _ _ (by simp; omega), List.drop_zero, List.take_left' hS]
  have g2 : (lookup (openInputs size) "sequence").map (BVExpr.eval (assignOf (S ++ (seqB ++ record)))) = seqB := by
    have : lookup (openInputs size) "sequence" = ByteCircuit.inputBytes 60 8 := by
      simp [lookup, lookupFrom, openInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 60 8 = _
    rw [iv _ _ _ (by simp; omega), List.drop_left' hS, List.take_left' hs]
  have g3 : (lookup (openInputs size) "record").map (BVExpr.eval (assignOf (S ++ (seqB ++ record)))) = record := by
    have : lookup (openInputs size) "record" = ByteCircuit.inputBytes 68 size := by
      simp [lookup, lookupFrom, openInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 68 size = _
    rw [iv _ _ _ (by simp; omega), ← List.append_assoc, List.drop_left' (by simp; omega),
      List.take_of_length_le (by omega)]
  simp only [g1, g2, g3] at hv
  simp only [kernelOut, hv, List.flatten_cons, List.flatten_nil, List.append_nil]

open TlsMpc.KernelSpecs.TlsHandshake in
/-- **What `verifyScript` opens** (`tlsVerifyFinished_spec`): 255 exactly when the message is the
server Finished message (`TlsHandshake.finishedMessage`) under the server handshake secret (the
block's first 32 bytes) and the transcript hash, else 0. -/
theorem verify_value (S hash message : B8) (hS : S.length = 60) (hh : hash.length = 32) (hm : message.length = 36) :
    kernelOut HybridKernel.tlsVerifyFinished (S ++ (hash ++ message)) =
      [if TlsHandshake.finishedMessage Sha256.concrete (S.take 32) hash = message then 255 else 0] := by
  have hv := tlsVerifyFinished_spec (assignOf (S ++ (hash ++ message)))
  have g1 : (lookup verifyInputs "serverHandshake").map (BVExpr.eval (assignOf (S ++ (hash ++ message)))) = S := by
    have : lookup verifyInputs "serverHandshake" = ByteCircuit.inputBytes 0 60 := by
      simp [lookup, lookupFrom, verifyInputs]
    rw [this]
    show inputValue _ 0 60 = _
    rw [iv _ _ _ (by simp; omega), List.drop_zero, List.take_left' hS]
  have g2 : (lookup verifyInputs "transcriptHash").map (BVExpr.eval (assignOf (S ++ (hash ++ message)))) = hash := by
    have : lookup verifyInputs "transcriptHash" = ByteCircuit.inputBytes 60 32 := by
      simp [lookup, lookupFrom, verifyInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 60 32 = _
    rw [iv _ _ _ (by simp; omega), List.drop_left' hS, List.take_left' hh]
  have g3 : (lookup verifyInputs "message").map (BVExpr.eval (assignOf (S ++ (hash ++ message)))) = message := by
    have : lookup verifyInputs "message" = ByteCircuit.inputBytes 92 36 := by
      simp [lookup, lookupFrom, verifyInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 92 36 = _
    rw [iv _ _ _ (by simp; omega), ← List.append_assoc, List.drop_left' (by simp; omega),
      List.take_of_length_le (by omega)]
  simp only [g1, g2, g3] at hv
  simp only [kernelOut, hv, List.flatten_cons, List.flatten_nil, List.append_nil]

open TlsMpc.KernelSpecs.TlsHandshake in
/-- **What `finishScript` keeps and opens** (`tlsFinish_spec`): the two application traffic blocks
of the RFC 8446 schedule from the main secret and the server-Finished hash (kept), then the client
Finished record, the certificate and the Finished message sealed under the client handshake key
and IV at sequence 0 (opened). -/
theorem finish_value (cert : Nat) (M sh C ch certificate : B8) (hM : M.length = 32) (hsh : sh.length = 32)
    (hC : C.length = 60) (hch : ch.length = 32) (hc : certificate.length = cert) :
    kernelOut (HybridKernel.tlsFinish cert) (M ++ (sh ++ (C ++ (ch ++ certificate)))) =
      trafficBlockValue (TlsKdf.applicationSecrets Sha256.concrete M sh).1 ++
        trafficBlockValue (TlsKdf.applicationSecrets Sha256.concrete M sh).2 ++
        TlsRecord.sealCore Gcm.concrete ((C.drop 32).take 16) ((C.drop 48).take 12) (List.replicate 8 0)
          (certificate ++ [20, 0, 0, 32] ++ TlsKdf.finished Sha256.concrete (C.take 32) ch) 22 0 := by
  have hv := tlsFinish_spec cert (assignOf (M ++ (sh ++ (C ++ (ch ++ certificate)))))
  have hl : (M ++ (sh ++ (C ++ (ch ++ certificate)))).length = 156 + cert := by simp; omega
  have g1 : (lookup (finishInputs cert) "mainSecret").map
      (BVExpr.eval (assignOf (M ++ (sh ++ (C ++ (ch ++ certificate)))))) = M := by
    have : lookup (finishInputs cert) "mainSecret" = ByteCircuit.inputBytes 0 32 := by
      simp [lookup, lookupFrom, finishInputs]
    rw [this]
    show inputValue _ 0 32 = _
    rw [iv _ _ _ (by omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid [] M (sh ++ (C ++ (ch ++ certificate))) 0 rfl
    rw [hM] at this
    simpa using this
  have g2 : (lookup (finishInputs cert) "serverHash").map
      (BVExpr.eval (assignOf (M ++ (sh ++ (C ++ (ch ++ certificate)))))) = sh := by
    have : lookup (finishInputs cert) "serverHash" = ByteCircuit.inputBytes 32 32 := by
      simp [lookup, lookupFrom, finishInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 32 32 = _
    rw [iv _ _ _ (by omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid M sh (C ++ (ch ++ certificate)) 32 hM
    rw [hsh] at this
    exact this
  have g3 : (lookup (finishInputs cert) "clientHandshake").map
      (BVExpr.eval (assignOf (M ++ (sh ++ (C ++ (ch ++ certificate)))))) = C := by
    have : lookup (finishInputs cert) "clientHandshake" = ByteCircuit.inputBytes 64 60 := by
      simp [lookup, lookupFrom, finishInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 64 60 = _
    rw [iv _ _ _ (by omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid (M ++ sh) C (ch ++ certificate) 64 (by simp; omega)
    rw [hC] at this
    simpa [List.append_assoc] using this
  have g4 : (lookup (finishInputs cert) "clientHash").map
      (BVExpr.eval (assignOf (M ++ (sh ++ (C ++ (ch ++ certificate)))))) = ch := by
    have : lookup (finishInputs cert) "clientHash" = ByteCircuit.inputBytes 124 32 := by
      simp [lookup, lookupFrom, finishInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 124 32 = _
    rw [iv _ _ _ (by omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid (M ++ sh ++ C) ch certificate 124 (by simp; omega)
    rw [hch] at this
    simpa [List.append_assoc] using this
  have g5 : (lookup (finishInputs cert) "certificate").map
      (BVExpr.eval (assignOf (M ++ (sh ++ (C ++ (ch ++ certificate)))))) = certificate := by
    have : lookup (finishInputs cert) "certificate" = ByteCircuit.inputBytes 156 cert := by
      simp [lookup, lookupFrom, finishInputs, HybridKernel.Shape.variables]
    rw [this]
    show inputValue _ 156 cert = _
    rw [iv _ _ _ (by omega)]
    have := TlsMpc.Node.Flows.Ghash.drop_take_mid (M ++ sh ++ C ++ ch) certificate [] 156 (by simp; omega)
    rw [hc] at this
    simpa [List.append_assoc] using this
  simp only [g1, g2, g3, g4, g5] at hv
  simp only [kernelOut, hv, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-! ## Well-formedness -/

/-- **`tagScript` is well formed**: from any context with the counter fresh and the pad live (128
private bits, not once), given `gcm-tag`'s signature (inputs 48 bytes, the tag public). -/
theorem tagScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (pad : BoolH) (halfSlot : Nat)
    (hf : Fresh c n) (hpn : pad.id < n) (hp : c.bool? pad = some ⟨List.replicate 128 .never, false⟩)
    (hsig : sigs tagName = some ⟨8 * 48, List.replicate 128 .pub⟩) :
    WF sigs c (tagScript n pad halfSlot) := by
  unfold tagScript
  simp only [seqs_cons, seqs_nil]
  have hf1 := (hf.push n (Nat.le_refl n) ⟨List.replicate 128 (Mark.ofInput false), true⟩).push (n + 1)
    (Nat.le_refl _) ⟨List.replicate 128 (Mark.ofInput false), true⟩
  refine WF_seq sigs c _ _ _ (check_boolInputBoth sigs hf 128 true false (by decide)) ?_
  have hf2 := (hf1.drop n).drop (n + 1)
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans
        ((bool?_push_of_ne _ _ _ _ (by omega)).trans hp)) rfl)
      (useBools_cons (useBool_once ((bool?_push_of_ne _ _ _ _ (by simp)).trans (bool?_push_self _ _ _)) rfl)
        (useBools_cons (useBool_once ((bool?_drop_of_ne _ _ _ (by simp)).trans (bool?_push_self _ _ _)) rfl)
          (useBools_nil _)))) hf2
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, maxWidth_eq]; omega)) ?_
  have hf3 := (hf2.push (n + 2) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨List.replicate 128 Mark.never, false⟩,
    ⟨List.replicate 128 (Mark.ofInput false), true⟩, ⟨List.replicate 128 (Mark.ofInput false), true⟩]).flatten,
    true⟩).drop (n + 2)
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_once (bool?_push_self _ _ _) rfl)
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate]) hf3 (by decide)
    (by simp only [List.length_replicate, maxWidth_eq]; omega)) ?_
  have p0 : pad.id ≠ n := by omega
  have p1 : pad.id ≠ n + 1 := by omega
  have p2 : pad.id ≠ n + 2 := by omega
  have p3 : pad.id ≠ n + 3 := by omega
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_push, bool?_drop, p0, p1, p2, p3, if_false, hp]
    rfl)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  have p3' : n + 3 ≠ pad.id := by omega
  rw [check_openBool sigs (by decide) (useBool_keep ((bool?_drop_of_ne _ _ _ (by show n + 3 ≠ pad.id; omega)).trans
      (bool?_push_self _ _ _)) rfl)
    (by
      rw [List.all_eq_true]
      intro x hx
      simp only [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_replicate] at hx
      rw [hx.2]
      rfl)]
  intro b _
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by
    simp only [bool?_push, bool?_drop, p3', if_false, if_true]
    rfl)) (WF.done _ _)

/-- **`updateScript` is well formed** (a 480-bit traffic block live, not once; `tls-update`'s
signature: 60 bytes in, 60 private bytes out). -/
theorem updateScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic : BoolH)
    (hf : Fresh c n) (htn : traffic.id < n) (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩)
    (hsig : sigs updateName = some ⟨8 * 60, List.replicate 480 .never⟩) :
    WF sigs c (updateScript n traffic) := by
  unfold updateScript
  simp only [seqs_cons, seqs_nil]
  have t0 : traffic.id ≠ n := by omega
  refine WF_seq sigs c _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep ht rfl)
    (by rw [List.length_replicate]; rfl) hf (by decide)
    (by rw [List.length_replicate, maxWidth_eq]; omega)) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp only [bool?_push, t0, if_false, ht]; rfl)) (WF.done _ _)

/-- **`publicScript` is well formed** (the counter fresh, at most `2²⁶` bits). -/
theorem publicScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (bytes : B8) (hf : Fresh c n)
    (hb : 8 * bytes.length ≤ maxWidth) : WF sigs c (publicScript n bytes) := by
  unfold publicScript
  simp only [seqs_cons, seqs_nil]
  exact WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp [hb])) (WF.done _ _)

/-- **`rangeScript` is well formed** on a buffer's revealed bytes (public marks), for a range
inside them. -/
theorem rangeScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (bytes : BoolH) (k lo hi : Nat)
    (hf : Fresh c n) (hbn : bytes.id < n) (hb : c.bool? bytes = some ⟨List.replicate k .pub, false⟩)
    (hlo : lo ≤ hi) (hhi : 8 * hi ≤ k) (hk : k ≤ maxWidth) : WF sigs c (rangeScript n bytes lo hi) := by
  unfold rangeScript
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs c _ _ _ (check_slice sigs (useBool_keep hb rfl) (by simp; omega) hf
    (by rw [maxWidth_eq] at hk ⊢; omega)) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep (bool?_push_self _ _ _) rfl) (by
    rw [List.all_eq_true]
    intro x hx
    have := List.mem_of_mem_drop (List.mem_of_mem_take hx)
    rw [List.mem_replicate] at this
    rw [this.2]
    rfl)]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool' sigs (by rw [bool?_push_self]; rfl)) (WF.done _ _)

/-- **`sealCtrScript` is well formed** (the seal's first phase): the traffic block (480 private bits)
and the content (`8 · size` bits, any marks) live and not once, the counter fresh, `tls-seal-ctr`'s
signature (inputs 68 + size bytes; header and ciphertext public, the pad private). -/
theorem sealCtrScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic content : BoolH) (seq : B8)
    (kind size padding : Nat) (cm : List Mark) (hf : Fresh c n) (htn : traffic.id < n) (hcn : content.id < n)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hc : c.bool? content = some ⟨cm, false⟩)
    (hcm : cm.length = 8 * size) (hs : seq.length = 8) (hsize : size + 1 + padding ≤ 16385)
    (hsig : sigs (sealCtrName kind size padding) =
      some ⟨8 * (68 + size), List.replicate (8 * (5 + innerLength size padding)) .pub ++ List.replicate 128 .never⟩) :
    WF sigs c (sealCtrScript n traffic content seq kind size padding) := by
  unfold sealCtrScript
  simp only [seqs_cons, seqs_nil]
  have t0 : traffic.id ≠ n := by omega
  have c0 : content.id ≠ n := by omega
  have hwM := maxWidth_eq
  refine WF_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp [hs, hwM])) ?_
  have hf1 := hf.push n (Nat.le_refl n) ⟨List.replicate (bitsOf seq).length .pub, false⟩
  refine WF_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ t0).trans ht) rfl)
      (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
        (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ c0).trans hc) rfl) (useBools_nil _)))) hf1
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, length_bitsOf, hs, hcm, hwM]; omega)) ?_
  have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨List.replicate 480 Mark.never, false⟩,
    ⟨List.replicate (bitsOf seq).length .pub, false⟩, ⟨cm, false⟩]).flatten, false⟩
  refine WF_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, length_bitsOf, hs, hcm]; omega) hf2 (by decide)
    (by simp only [List.length_append, List.length_replicate, innerLength, hwM]; omega)) ?_
  have hL : (List.replicate 1 (List.replicate (8 * (5 + innerLength size padding)) Mark.pub ++
      List.replicate 128 Mark.never)).flatten =
      List.replicate (8 * (5 + innerLength size padding)) Mark.pub ++ List.replicate 128 Mark.never := by simp
  have hf3 := hf2.push (n + 2) (Nat.le_refl _) ⟨(List.replicate 1 (List.replicate (8 * (5 + innerLength size padding))
    Mark.pub ++ List.replicate 128 Mark.never)).flatten, false⟩
  refine WF_seq sigs _ _ _ _ (check_slice sigs (useBool_keep (bool?_push_self _ _ _) rfl)
    (by simp only [hL, List.length_append, List.length_replicate]; omega) hf3 (by rw [hwM]; omega)) ?_
  have hf4 := hf3.push (n + 3) (Nat.le_refl _) ⟨((List.replicate 1 (List.replicate (8 * (5 + innerLength size padding))
    Mark.pub ++ List.replicate 128 Mark.never)).flatten.drop (8 * (5 + innerLength size padding))).take
      (8 * (5 + innerLength size padding + 16) - 8 * (5 + innerLength size padding)), false⟩
  refine WF_seq sigs _ _ _ _ (check_slice sigs
    (useBool_keep ((bool?_push_of_ne _ _ _ _ (show n + 2 ≠ n + 3 by omega)).trans (bool?_push_self _ _ _)) rfl)
    (by simp only [hL, List.length_append, List.length_replicate]; omega) hf4
    (by rw [hwM]; simp only [innerLength]; omega)) ?_
  have a1 : n ≠ n + 1 := by omega
  have a2 : n ≠ n + 2 := by omega
  have a3 : n ≠ n + 3 := by omega
  have a4 : n ≠ n + 4 := by omega
  have b0 : n + 1 ≠ n := by omega
  have b2 : n + 1 ≠ n + 2 := by omega
  have b3 : n + 1 ≠ n + 3 := by omega
  have b4 : n + 1 ≠ n + 4 := by omega
  have c0 : n + 2 ≠ n := by omega
  have c1 : n + 2 ≠ n + 1 := by omega
  have c3 : n + 2 ≠ n + 3 := by omega
  have c4 : n + 2 ≠ n + 4 := by omega
  have d0 : n + 4 ≠ n := by omega
  have d1 : n + 4 ≠ n + 1 := by omega
  have d2 : n + 4 ≠ n + 2 := by omega
  refine WF_seq sigs _ _ _ _ (check_freeBool sigs ((bool?_push_of_ne _ _ _ ⟨n⟩ a4).trans
    ((bool?_push_of_ne _ _ _ ⟨n⟩ a3).trans ((bool?_push_of_ne _ _ _ ⟨n⟩ a2).trans
      ((bool?_push_of_ne _ _ _ ⟨n⟩ a1).trans (bool?_push_self _ _ _)))))) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool sigs ((bool?_drop_of_ne _ _ ⟨n + 1⟩ b0).trans
    ((bool?_push_of_ne _ _ _ ⟨n + 1⟩ b4).trans ((bool?_push_of_ne _ _ _ ⟨n + 1⟩ b3).trans
      ((bool?_push_of_ne _ _ _ ⟨n + 1⟩ b2).trans (bool?_push_self _ _ _)))))) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool sigs ((bool?_drop_of_ne _ _ ⟨n + 2⟩ c1).trans
    ((bool?_drop_of_ne _ _ ⟨n + 2⟩ c0).trans ((bool?_push_of_ne _ _ _ ⟨n + 2⟩ c4).trans
      ((bool?_push_of_ne _ _ _ ⟨n + 2⟩ c3).trans (bool?_push_self _ _ _)))))) ?_
  refine WF_openThen sigs _ _ _ _ ?_
  rw [check_openBool sigs (by decide) (useBool_keep ((bool?_drop_of_ne _ _ ⟨n + 4⟩ d2).trans
      ((bool?_drop_of_ne _ _ ⟨n + 4⟩ d1).trans ((bool?_drop_of_ne _ _ ⟨n + 4⟩ d0).trans
        (bool?_push_self _ _ _)))) rfl) (by
    rw [List.all_eq_true]
    intro x hx
    simp only [hL, List.drop_zero, Nat.sub_zero] at hx
    rw [List.take_left' (by simp)] at hx
    rw [(List.mem_replicate.mp hx).2]
    rfl)]
  intro b _
  exact WF_seq sigs _ _ _ _ (check_freeBool sigs ((bool?_drop_of_ne _ _ ⟨n + 4⟩ d2).trans
      ((bool?_drop_of_ne _ _ ⟨n + 4⟩ d1).trans ((bool?_drop_of_ne _ _ ⟨n + 4⟩ d0).trans
        (bool?_push_self _ _ _))))) (WF.done _ _)

/-- **`dropScript` is well formed** for distinct live handles. -/
theorem dropScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (hs : List BoolH) (hn : (hs.map (·.id)).Nodup)
    (hl : ∀ h ∈ hs, (c.bool? h).isSome = true) : WF sigs c (dropScript hs) :=
  (frees_wfp sigs (Q := fun _ _ => True) (.done ()) hs c hn hl (fun c' _ _ => WFP.done _ _ trivial)).wf

end TlsMpc.Node.Flows.Tls
