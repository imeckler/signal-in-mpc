import TlsMpc.ByteAuth

/-!
TLSInnerPlaintext parsing, RFC 9846 section 5.4. The last nonzero byte is
the content type; preceding bytes are content and following zeros are padding.
The supported types are alert (21), handshake (22), and application data (23).
Only application data may have empty content. All output fields stay secret:
acceptance (255/0), type, two-byte network-order content length, and a fixed
buffer as long as the input. Rejection zeros every output byte.
-/

namespace TlsMpc.TlsInner
open Std.Tactic.BVDecide

def select (o : ByteAuth.Ops B) (mask yes no : B) : B :=
  o.xor (o.and mask (o.xor yes no)) no

structure Scan (B : Type) where
  found : B
  kind : B
  high : B
  low : B
  nonempty : B
  content : List B

def Scan.map (f : B → B') (r : Scan B) : Scan B' :=
  ⟨f r.found, f r.kind, f r.high, f r.low, f r.nonempty, r.content.map f⟩

def emptyScan (o : ByteAuth.Ops B) : Scan B :=
  ⟨o.const 0, o.const 0, o.const 0, o.const 0, o.const 0, []⟩

def scanStep (o : ByteAuth.Ops B) (offset : Nat) (byte : B) (rest : Scan B) : Scan B :=
  let nz := o.not (ByteAuth.zeroMask o byte)
  ⟨select o rest.found rest.found nz,
   select o rest.found rest.kind (o.and nz byte),
   select o rest.found rest.high (o.and nz (o.const (offset / 256))),
   select o rest.found rest.low (o.and nz (o.const offset)),
   select o rest.found rest.nonempty (o.and nz (o.const (if offset = 0 then 0 else 255))),
   o.and rest.found byte :: rest.content⟩

def scan (o : ByteAuth.Ops B) : Nat → List B → Scan B
  | _, [] => emptyScan o
  | offset, byte :: rest => scanStep o offset byte (scan o (offset + 1) rest)

/-- Direct, branching reference: locate the rightmost nonzero byte. -/
def splitSpec : List (BitVec 8) → Option (List (BitVec 8) × BitVec 8)
  | [] => none
  | byte :: rest =>
      match splitSpec rest with
      | some (content, kind) => some (byte :: content, kind)
      | none => if byte = 0 then none else some ([], byte)

def encodeScan (offset size : Nat) : Option (List (BitVec 8) × BitVec 8) → Scan (BitVec 8)
  | none => ⟨0, 0, 0, 0, 0, List.replicate size 0⟩
  | some (content, kind) =>
      let length := offset + content.length
      ⟨255, kind, BitVec.ofNat 8 (length / 256), BitVec.ofNat 8 length,
        if length = 0 then 0 else 255, content ++ List.replicate (size - content.length) 0⟩

def permitted (kind : BitVec 8) (nonempty : Bool) : Prop :=
  kind = 23 ∨ ((kind = 21 ∨ kind = 22) ∧ nonempty = true)

instance (kind : BitVec 8) (nonempty : Bool) : Decidable (permitted kind nonempty) :=
  inferInstanceAs (Decidable (_ ∨ ((_ ∨ _) ∧ _)))

def allowedMask (o : ByteAuth.Ops B) (kind nonempty : B) : B :=
  o.xor (ByteAuth.eqMask o kind (o.const 23))
    (o.and nonempty (o.xor (ByteAuth.eqMask o kind (o.const 21)) (ByteAuth.eqMask o kind (o.const 22))))

def finish (o : ByteAuth.Ops B) (r : Scan B) : List B :=
  let accepted := allowedMask o r.kind r.nonempty
  accepted :: ByteAuth.release o accepted (r.kind :: r.high :: r.low :: r.content)

def decode (o : ByteAuth.Ops B) (bytes : List B) : List B := finish o (scan o 0 bytes)

def decodeChecked (o : ByteAuth.Ops B) (bytes : List B) : Option (List B) :=
  if 0 < bytes.length ∧ bytes.length ≤ 16385 then some (decode o bytes) else none

def spec (bytes : List (BitVec 8)) : List (BitVec 8) :=
  match splitSpec bytes with
  | none => List.replicate (bytes.length + 4) 0
  | some (content, kind) =>
      if permitted kind (!content.isEmpty) then
        [255, kind, BitVec.ofNat 8 (content.length / 256), BitVec.ofNat 8 content.length] ++
          content ++ List.replicate (bytes.length - content.length) 0
      else List.replicate (bytes.length + 4) 0

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem select_map (mask yes no : B) : f (select a mask yes no) = select b (f mask) (f yes) (f no) := by
  simp only [select, h.xor, h.and]

theorem scanStep_map (offset : Nat) (byte : B) (rest : Scan B) :
    (scanStep a offset byte rest).map f = scanStep b offset (f byte) (rest.map f) := by
  simp [scanStep, Scan.map, select_map h, ByteAuth.zeroMask_map h, h.not, h.and, h.const]

theorem scan_map (offset : Nat) (bytes : List B) :
    (scan a offset bytes).map f = scan b offset (bytes.map f) := by
  induction bytes generalizing offset with
  | nil => simp [scan, emptyScan, Scan.map, h.const]
  | cons byte rest ih => simp only [scan, List.map_cons, scanStep_map h, ih]

theorem allowedMask_map (kind nonempty : B) :
    f (allowedMask a kind nonempty) = allowedMask b (f kind) (f nonempty) := by
  simp only [allowedMask, h.xor, h.and, ByteAuth.eqMask_map h, h.const]

theorem finish_map (r : Scan B) : (finish a r).map f = finish b (r.map f) := by
  simp [finish, ByteAuth.release_map h, allowedMask_map h, Scan.map]

theorem decode_map (bytes : List B) : (decode a bytes).map f = decode b (bytes.map f) := by
  simp only [decode, finish_map h, scan_map h]

theorem decodeChecked_map (bytes : List B) :
    (decodeChecked a bytes).map (List.map f) = decodeChecked b (bytes.map f) := by
  simp only [decodeChecked, List.length_map]
  split <;> simp_all [decode_map h]

end Refinement

private theorem and_accept (x : BitVec 8) : (255 : BitVec 8) &&& x = x := BitVec.allOnes_and
private theorem and_reject (x : BitVec 8) : (0 : BitVec 8) &&& x = 0 := BitVec.zero_and

theorem select_accept (yes no : BitVec 8) : select ByteAuth.concrete 255 yes no = yes := by
  change ((255 : BitVec 8) &&& (yes ^^^ no)) ^^^ no = yes
  rw [and_accept, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem select_reject (yes no : BitVec 8) : select ByteAuth.concrete 0 yes no = no := by
  change ((0 : BitVec 8) &&& (yes ^^^ no)) ^^^ no = no
  rw [and_reject]
  exact BitVec.zero_xor

theorem scan_content_length (o : ByteAuth.Ops B) (offset : Nat) (bytes : List B) :
    (scan o offset bytes).content.length = bytes.length := by
  induction bytes generalizing offset with
  | nil => rfl
  | cons byte rest ih => simp [scan, scanStep, ih]

theorem decode_length (o : ByteAuth.Ops B) (bytes : List B) :
    (decode o bytes).length = bytes.length + 4 := by
  simp [decode, finish, ByteAuth.release, scan_content_length]

theorem splitSpec_length (bytes content : List (BitVec 8)) (kind : BitVec 8)
    (hs : splitSpec bytes = some (content, kind)) : content.length < bytes.length := by
  induction bytes generalizing content kind with
  | nil => simp [splitSpec] at hs
  | cons byte rest ih =>
      cases ht : splitSpec rest with
      | none =>
          simp only [splitSpec, ht] at hs
          split at hs
          · contradiction
          · cases hs; simp
      | some pair =>
          obtain ⟨tail, tag⟩ := pair
          have hl := ih tail tag ht
          simp only [splitSpec, ht, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          simpa using hl

theorem scanStep_concrete (offset : Nat) (byte : BitVec 8) (rest : Scan (BitVec 8)) :
    scanStep ByteAuth.concrete offset byte rest =
      let nz : BitVec 8 := if byte = 0 then 0 else 255
      ⟨select ByteAuth.concrete rest.found rest.found nz,
       select ByteAuth.concrete rest.found rest.kind (nz &&& byte),
       select ByteAuth.concrete rest.found rest.high (nz &&& BitVec.ofNat 8 (offset / 256)),
       select ByteAuth.concrete rest.found rest.low (nz &&& BitVec.ofNat 8 offset),
       select ByteAuth.concrete rest.found rest.nonempty
         (nz &&& BitVec.ofNat 8 (if offset = 0 then 0 else 255)),
       (rest.found &&& byte) :: rest.content⟩ := by
  unfold scanStep
  rw [ByteAuth.zeroMask_value]
  split <;> rfl

theorem scan_correct (offset : Nat) (bytes : List (BitVec 8)) :
    scan ByteAuth.concrete offset bytes = encodeScan offset bytes.length (splitSpec bytes) := by
  induction bytes generalizing offset with
  | nil => rfl
  | cons byte rest ih =>
      rw [scan, ih]
      cases hs : splitSpec rest with
      | none =>
          by_cases hb : byte = 0
          · subst byte
            simp only [splitSpec, hs, ↓reduceIte, List.length_cons, encodeScan,
              scanStep_concrete, select_reject, and_reject, List.replicate_succ]
          · simp only [splitSpec, hs, hb, ↓reduceIte, encodeScan, scanStep_concrete,
              select_reject, and_accept, and_reject, List.length_nil, Nat.add_zero,
              List.nil_append, Nat.sub_zero, List.length_cons, List.replicate_succ]
            by_cases ho : offset = 0 <;> simp only [ho, ↓reduceIte] <;> rfl
      | some pair =>
          obtain ⟨content, kind⟩ := pair
          simp only [splitSpec, hs, encodeScan, scanStep_concrete, select_accept,
            and_accept, List.length_cons, Nat.add_assoc, List.cons_append, Nat.add_sub_add_right]
          rw [Nat.add_comm 1 content.length]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allowedMask_value (kind : BitVec 8) (nonempty : Bool) :
    allowedMask ByteAuth.concrete kind (if nonempty then 255 else 0) =
      if permitted kind nonempty then 255 else 0 := by
  have all : ∀ (kind : BitVec 8) (nonempty : Bool),
      allowedMask ByteAuth.concrete kind (if nonempty then 255 else 0) =
        if permitted kind nonempty then 255 else 0 := by decide +kernel
  exact all kind nonempty

theorem decode_correct (bytes : List (BitVec 8)) : decode ByteAuth.concrete bytes = spec bytes := by
  rw [decode, scan_correct]
  cases hs : splitSpec bytes with
  | none =>
      have ha : allowedMask ByteAuth.concrete 0 0 = 0 := by decide +kernel
      simp only [finish, encodeScan, ha, ByteAuth.release_reject, spec, hs,
        List.length_cons, List.length_replicate]
      rfl
  | some pair =>
      obtain ⟨content, kind⟩ := pair
      have hl := splitSpec_length bytes content kind hs
      have hm : (if content.length = 0 then (0 : BitVec 8) else 255) =
          (if !content.isEmpty then 255 else 0) := by cases content <;> simp
      simp only [finish, encodeScan, Nat.zero_add, hm, allowedMask_value, spec, hs]
      split
      · rw [ByteAuth.release_accept]; rfl
      · rw [ByteAuth.release_reject]
        simp only [List.length_cons, List.length_append, List.length_replicate]
        rw [show content.length + (bytes.length - content.length) + 1 + 1 + 1 = bytes.length + 3 by omega]
        rfl

theorem reject_missing_type (bytes : List (BitVec 8)) (missing : splitSpec bytes = none) :
    decode ByteAuth.concrete bytes = List.replicate (bytes.length + 4) 0 := by
  rw [decode_correct]
  simp only [spec, missing]

theorem reject_disallowed_type (bytes content : List (BitVec 8)) (kind : BitVec 8)
    (parsed : splitSpec bytes = some (content, kind)) (bad : ¬permitted kind (!content.isEmpty)) :
    decode ByteAuth.concrete bytes = List.replicate (bytes.length + 4) 0 := by
  rw [decode_correct]
  simp only [spec, parsed, if_neg bad]

theorem compiled_decode_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (decode ByteAuth.symbolic bytes).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (decode ByteAuth.symbolic bytes))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (decode ByteAuth.symbolic bytes))).vec.get index hi)) =
      (ByteCircuit.joinValue (spec (bytes.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, decode_map (ByteAuth.evaluationHom assign), decode_correct]

end TlsMpc.TlsInner
