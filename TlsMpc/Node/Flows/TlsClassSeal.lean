import TlsMpc.Node.Flows.TlsRun

/-!
# The class seal's composition through the script (gap F16)

REORGANIZATION_PLAN.md stage S12. `sealClassScript` feeds `tls-seal-class CAP` (`CAP = capacity
size`) the client traffic block, the sequence, the content followed by zeros up to the capacity, and
the record header's length field `size + 17`; it opens accepted ‖ header ‖ ciphertext, aborts unless
accepted is 255, and keeps header ‖ the first `size + 1` ciphertext bytes and the pad's handle.

  * `sealClass_kernelOut`: on those bytes the kernel's output is `255`, the exact-size record header,
    the CTR ciphertext of the TLSInnerPlaintext of the content alone (type 23, no padding) followed by
    zeros, and the pad: from `tlsSealClass`'s definition through `sealCiphertext_refines` and
    `RecordClass.sealCiphertext_padded` (kernel level, `recordClass_sealCiphertext_padded`).
  * **`sealClass_is_record`**: what the class script opens is accepted (`[255]`, so it does not
    abort), and the header ‖ ciphertext it keeps, followed by `gcm-tag` on its pad and the two parties'
    halves `Local.Ghash.half` of shares of H¹ … Hⁿ, is EXACTLY `TlsRecord.sealCore` of the key and IV,
    the sequence and the content with kind 23 and no padding: byte for byte the exact-size record
    (`seal_is_record` for `tls-seal-ctr 23 size 0`). The class only hides which size class the
    circuit was built for; the record on the wire is the exact-size one.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open Std.Tactic.BVDecide
open TlsMpc.HybridKernel (lookup lookupFrom inputValue)

/-- The record header's length field the class script makes public (`size + 17`, big-endian). -/
def sizeBytes (size : Nat) : B8 := [BitVec.ofNat 8 ((size + 17) / 256), BitVec.ofNat 8 (size + 17)]

theorem bitsOf_zeros (k : Nat) : bitsOf (List.replicate k (0 : BitVec 8)) = List.replicate (8 * k) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, bitsOf_cons, ih, show 8 * (k + 1) = 8 + 8 * k by omega,
      ← List.replicate_append_replicate]
    rfl

/-- The public bits `sealClassScript` writes after the content: zeros up to the capacity, then the
length field. -/
theorem sealClass_pad_bits (cap size : Nat) :
    List.replicate (8 * (cap - size)) false ++
        bitsOf [BitVec.ofNat 8 ((size + 17) / 256), BitVec.ofNat 8 (size + 17)] =
      bitsOf (List.replicate (cap - size) 0 ++ sizeBytes size) := by
  rw [bitsOf_append, bitsOf_zeros]
  rfl

theorem lengthValue_sizeBytes (size : Nat) (h : size + 17 < 65536) :
    TlsPrivateSeal.lengthValue ((sizeBytes size).getD 0 0) ((sizeBytes size).getD 1 0) = size + 17 := by
  simp only [sizeBytes, List.getD_cons_zero, List.getD_cons_succ, TlsPrivateSeal.lengthValue, BitVec.toNat_ofNat]
  have := Nat.div_add_mod (size + 17) 256
  omega

theorem header_sizeBytes (size : Nat) :
    TlsRecord.header Gcm.concrete (size + 17) = [23, 3, 3] ++ sizeBytes size := by
  simp only [TlsRecord.header, Gcm.encodeNat, sizeBytes, show List.range 2 = [0, 1] from rfl]
  simp [Gcm.concrete, Aes.concrete]

/-- **`tls-seal-class CAP` on the bytes `sealClassScript` feeds it.** -/
theorem sealClass_kernelOut (cap size : Nat) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (hcap : size ≤ cap) (hb : cap + 17 < 65536) :
    kernelOut (RecordClassKernel.tlsSealClass cap) (K ++ (seqB ++ (C ++ (List.replicate (cap - size) 0 ++ sizeBytes size)))) =
      [255] ++ (TlsRecord.header Gcm.concrete (size + 17) ++
        (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C 23 0) ++ List.replicate (cap - size) 0)) ++
        HybridKernel.padOf K seqB := by
  have hz : (List.replicate (cap - size) (0 : BitVec 8) ++ sizeBytes size).length = cap - size + 2 := by
    simp [sizeBytes]
  have hx : (K ++ (seqB ++ (C ++ (List.replicate (cap - size) 0 ++ sizeBytes size)))).length = 70 + cap := by
    simp only [List.length_append, hK, hs, hC, hz]
    omega
  generalize hA : assignOf (K ++ (seqB ++ (C ++ (List.replicate (cap - size) 0 ++ sizeBytes size)))) = A
  have v1 : (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
      ("size", .bytes 2)] "clientApplication").map (BVExpr.eval A) = K := by
    have : lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
        ("size", .bytes 2)] "clientApplication" = ByteCircuit.inputBytes 0 60 := by simp [lookup, lookupFrom]
    rw [this, ← hA]
    show inputValue _ 0 60 = _
    rw [inputValue_assignOf _ _ _ (by omega), List.drop_zero, List.take_left' hK]
  have v2 : (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
      ("size", .bytes 2)] "sequence").map (BVExpr.eval A) = seqB := by
    have : lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
        ("size", .bytes 2)] "sequence" = ByteCircuit.inputBytes 60 8 := by
      simp [lookup, lookupFrom, HybridKernel.Shape.variables]
    rw [this, ← hA]
    show inputValue _ 60 8 = _
    rw [inputValue_assignOf _ _ _ (by omega), List.drop_left' hK, List.take_left' hs]
  have v3 : (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
      ("size", .bytes 2)] "content").map (BVExpr.eval A) = C ++ List.replicate (cap - size) 0 := by
    have : lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
        ("size", .bytes 2)] "content" = ByteCircuit.inputBytes 68 cap := by
      simp [lookup, lookupFrom, HybridKernel.Shape.variables]
    rw [this, ← hA]
    show inputValue _ 68 cap = _
    rw [inputValue_assignOf _ _ _ (by omega),
      show K ++ (seqB ++ (C ++ (List.replicate (cap - size) 0 ++ sizeBytes size))) =
        (K ++ seqB) ++ ((C ++ List.replicate (cap - size) 0) ++ sizeBytes size) by simp,
      List.drop_left' (by simp; omega), List.take_left' (by simp; omega)]
  have v4 : (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
      ("size", .bytes 2)] "size").map (BVExpr.eval A) = sizeBytes size := by
    have : lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
        ("size", .bytes 2)] "size" = ByteCircuit.inputBytes (68 + cap) 2 := by
      simp [lookup, lookupFrom, HybridKernel.Shape.variables]
      all_goals omega
    rw [this, ← hA]
    show inputValue _ (68 + cap) 2 = _
    rw [inputValue_assignOf _ _ _ (by omega),
      show K ++ (seqB ++ (C ++ (List.replicate (cap - size) 0 ++ sizeBytes size))) =
        (K ++ seqB ++ C ++ List.replicate (cap - size) 0) ++ sizeBytes size by simp,
      List.drop_left' (by simp; omega), List.take_of_length_le (by simp [sizeBytes])]
  -- the two length bytes, as the kernel reads them
  have hgetD : ∀ (l : List (BVExpr 8)) (i : Nat), BVExpr.eval A (HybridService.at' l i) =
      (l.map (BVExpr.eval A)).getD i 0 := by
    intro l i
    simp only [HybridService.at', List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[i]? <;> rfl
  -- the ciphertext half of the kernel, on values
  have hsc := RecordClass.sealCiphertext_refines
    (HybridKernel.gcmExpanded (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8),
      ("content", .bytes cap), ("size", .bytes 2)] "clientApplication"))
    (TlsRecord.nonce Gcm.symbolic (HybridKernel.blockIv (lookup [("clientApplication", HybridKernel.Shape.bytes 60),
      ("sequence", .bytes 8), ("content", .bytes cap), ("size", .bytes 2)] "clientApplication"))
      (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
        ("size", .bytes 2)] "sequence"))
    (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes cap),
      ("size", .bytes 2)] "content")
    (HybridService.at' (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8),
      ("content", .bytes cap), ("size", .bytes 2)] "size") 0)
    (HybridService.at' (lookup [("clientApplication", HybridKernel.Shape.bytes 60), ("sequence", .bytes 8),
      ("content", .bytes cap), ("size", .bytes 2)] "size") 1) A
  rw [HybridKernel.gcmExpanded_eval, TlsRecord.nonce_map (Gcm.evaluationHom A), HybridKernel.blockIv,
    HybridKernel.sl, List.map_take, List.map_drop, v1, v2, v3, hgetD, hgetD, v4,
    RecordClass.sealCiphertext_padded _ _ C _ _ _ (HybridKernel.expandedOf_length K hK)
      (by simp only [List.length_replicate, hC]; omega)
      (by rw [lengthValue_sizeBytes size (by omega), hC])] at hsc
  simp only [Prod.mk.injEq] at hsc
  obtain ⟨hacc, hct⟩ := hsc
  show ((RecordClassKernel.tlsSealClass cap).outputs.map (fun field => field.value.map
    (BVExpr.eval (assignOf (K ++ (seqB ++ (C ++ (List.replicate (cap - size) 0 ++ sizeBytes size)))))))).flatten = _
  rw [hA]
  simp only [RecordClassKernel.tlsSealClass, HybridKernel.pub, HybridKernel.priv, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, HybridKernel.blockIv, HybridKernel.sl,
    ByteAuth.release_map (ByteAuth.evaluationHom A), hacc, hct, ByteAuth.release_accept,
    HybridKernel.gcmPad_eval, v1, v2, v4, header_sizeBytes, List.length_replicate]
  simp [HybridKernel.const, HybridKernel.ctrOf, List.append_assoc]

/-- **The class seal's composition** (gap F16): through `sealClassScript`'s layout, the opened
acceptance byte is 255 (the script does not abort) and the kept header ‖ ciphertext, followed by
`gcm-tag` on the kept pad and the two parties' halves of shares of H¹ … Hⁿ (`n` covering the record),
is EXACTLY the exact-size record `TlsRecord.sealCore … C 23 0`. -/
theorem sealClass_is_record (size : Nat) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (hb : capacity size + 17 < 65536) (a b : List W) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) (hn : Local.Ghash.needed 5 (size + 1) ≤ nPow) :
    let out := kernelOut (RecordClassKernel.tlsSealClass (capacity size))
      (K ++ (seqB ++ (C ++ (List.replicate (capacity size - size) 0 ++ sizeBytes size))))
    let opened := out.take (1 + 5 + capacity size + 1)
    let hc := (opened.drop 1).take (5 + size + 1)
    let pad := (out.drop (1 + 5 + capacity size + 1)).take 16
    opened.take 1 = [255] ∧
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5)) ++
        Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5)))) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C 23 0 := by
  have hle := le_capacity size
  have hrec := seal_is_record 23 size 0 K seqB C hK hs hC a b nPow hsh (by simpa [innerLength] using hn)
  dsimp only at hrec ⊢
  rw [sealClass_kernelOut (capacity size) size K seqB C hK hs hC hle hb]
  obtain ⟨hout, -⟩ := sealCtr_kernelOut 23 size 0 K seqB C hK hs hC
  rw [hout] at hrec
  have hH := header_length (size + 17)
  have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C 23 0)).length = size + 1 := by
    rw [HybridKernel.ctrOf_length _ _ _ hK, inner_length, hC]
    rfl
  have hP := padOf_length K seqB hK
  have hi : innerLength size 0 + 16 = size + 17 := by simp [innerLength]
  rw [hi] at hrec
  generalize TlsRecord.header Gcm.concrete (size + 17) = H at hH hrec ⊢
  generalize HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C 23 0) = CT at hCT hrec ⊢
  generalize HybridKernel.padOf K seqB = P at hP hrec ⊢
  have e1 : ([255] ++ (H ++ (CT ++ List.replicate (capacity size - size) 0)) ++ P).take (1 + 5 + capacity size + 1) =
      [255] ++ ((H ++ CT) ++ List.replicate (capacity size - size) 0) := by
    rw [List.take_append_of_le_length (by simp [hH, hCT]; omega), List.take_of_length_le (by simp [hH, hCT]; omega)]
    simp
  have e2 : ([255] ++ (H ++ (CT ++ List.replicate (capacity size - size) 0)) ++ P).drop (1 + 5 + capacity size + 1) = P := by
    rw [List.drop_left' (by simp [hH, hCT]; omega)]
  have e3 : (H ++ CT ++ P).take (5 + innerLength size 0) = H ++ CT := by
    rw [List.take_left' (by simp [hH, hCT, innerLength])]
  have e4 : (([255] ++ ((H ++ CT) ++ List.replicate (capacity size - size) 0)).drop 1).take (5 + size + 1) = H ++ CT := by
    rw [List.singleton_append, List.drop_one, List.tail_cons, List.take_left' (by simp [hH, hCT]; omega)]
  rw [e3] at hrec
  have e5 : ((H ++ CT ++ P).drop (5 + innerLength size 0)).take 16 = P := by
    rw [List.drop_left' (by simp [hH, hCT, innerLength]), List.take_of_length_le (by omega)]
  rw [e5] at hrec
  rw [e1, e2, e4, List.take_of_length_le (l := P) (by omega)]
  exact ⟨by simp, hrec⟩

end TlsMpc.Node.Flows.Tls
