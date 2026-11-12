import TlsMpc.TlsWire

/-!
# The TLS record-layer parser against RFC 8446 section 5.1

New file; it changes no definition and no emitter imports it.

`TlsWire.records` splits the bytes the transport returned into TLS records. It is what
`TlsClient.receiveRecord` (handshake records) and `TlsApplication.receive` (every protected record,
whose plaintext the controller later reveals) run on the wire bytes, followed there by checks on its
result: exactly one record and no bytes left over (`records 2 wire = .ok ([r], [])`), and, for
application records, type 23, legacy version 0x0303, total length 22–16406.

## The reference

RFC 8446 section 5.1:

```
struct {
    ContentType type;                       -- 1 byte
    ProtocolVersion legacy_record_version;  -- 2 bytes
    uint16 length;                          -- 2 bytes, network byte order
    opaque fragment[TLSPlaintext.length];
} TLSPlaintext;
```

"The length MUST NOT exceed 2^14 + 256 bytes" (TLSCiphertext; a longer record MUST be answered with
a "record_overflow" alert). `encode` is that layout, written here; `WellFormed` the field ranges and
that length bound (2^14 + 256 = 16640). A byte string is `Incomplete` when it holds no whole record
yet: fewer than 5 bytes, or a header (with an allowed length) whose fragment has not fully arrived.

## What is proved (standard axioms only; no `sorry`, `native_decide`, `bv_decide`)

* `records_complete`: for any well-formed records `rs` followed by an incomplete tail, with enough
  fuel, `records fuel (rs.flatMap encode ++ tail) = .ok (rs, tail)`;
* `records_sound`: whatever `records` returns as `.ok (rs, pending)`, the input is exactly
  `rs.flatMap encode ++ pending`, every record is well-formed and `pending` is incomplete;
* `records_overflow`: a header announcing more than 2^14 + 256 bytes is an error, as soon as the
  header is there (before its fragment arrives);
* `receive_one`: what the callers' check accepts, `records 2 wire = .ok ([r], [])`, is exactly a
  wire that is one RFC 8446 record: `WellFormed r ∧ wire = encode r`.

Note: the 2^14 + 256 bound applies to every record here, plaintext handshake records included;
RFC 8446 bounds a TLSPlaintext by 2^14, which `TlsClient.receiveHello` checks itself
(`record.body.length ≤ 16384`). The application path's own bound, wire ≤ 16406 (a fragment of at
most 2^14 + 1 + 16, AES-128-GCM's largest), is stricter than 2^14 + 256.
-/

namespace TlsMpc.KernelSpecs.ParseTlsRecord
open TlsMpc.TlsWire

/-- RFC 8446 section 5.1: type, legacy_record_version (big-endian), length (big-endian), fragment. -/
def encode (r : Record) : Bytes :=
  [UInt8.ofNat r.kind, UInt8.ofNat (r.version / 256), UInt8.ofNat (r.version % 256),
   UInt8.ofNat (r.body.length / 256), UInt8.ofNat (r.body.length % 256)] ++ r.body

/-- One-byte type, two-byte version, fragment of at most 2^14 + 256 bytes. -/
def WellFormed (r : Record) : Prop := r.kind < 256 ∧ r.version < 65536 ∧ r.body.length ≤ 16640

/-- The length announced by a record header (bytes 3 and 4, big-endian). -/
def announced (b : Bytes) : Nat := 256 * (b.getD 3 0).toNat + (b.getD 4 0).toNat

/-- No whole record yet: fewer than 5 bytes, or an allowed length whose fragment is not all there. -/
def Incomplete (b : Bytes) : Prop := b.length < 5 ∨ (announced b ≤ 16640 ∧ b.length < 5 + announced b)

/-! ### `records`, one step at a time -/

theorem number_two (x y : UInt8) : number [x, y] = 256 * x.toNat + y.toNat := by
  simp [number]

theorem ofNat_toNat (x : UInt8) : UInt8.ofNat x.toNat = x := by
  apply UInt8.toNat_inj.mp
  simp

theorem toNat_ofNat_lt (n : Nat) (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp; omega

def recOf (b0 b1 b2 : UInt8) (body : Bytes) : Record := ⟨b0.toNat, 256 * b1.toNat + b2.toNat, body⟩

theorem records_short (f : Nat) (b : Bytes) (h : b.length < 5) : records (f + 1) b = .ok ([], b) := by
  simp [records, h]; rfl

theorem records_step (f : Nat) (b0 b1 b2 b3 b4 : UInt8) (rest : Bytes) :
    records (f + 1) (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      if 16640 < 256 * b3.toNat + b4.toNat then .error "TLS record overflow"
      else if rest.length < 256 * b3.toNat + b4.toNat then .ok ([], b0 :: b1 :: b2 :: b3 :: b4 :: rest)
      else match records f (rest.drop (256 * b3.toNat + b4.toNat)) with
        | .ok (t, p) => .ok (recOf b0 b1 b2 (rest.take (256 * b3.toNat + b4.toNat)) :: t, p)
        | .error e => .error e := by
  conv => lhs; unfold records
  simp only [List.length_cons, number_two, List.drop, List.take, List.getElem!_cons_zero]
  generalize 256 * b3.toNat + b4.toNat = n
  have h3 : ¬ rest.length + 1 + 1 + 1 + 1 + 1 < 5 := by omega
  have hd : List.drop (5 + n) (b0 :: b1 :: b2 :: b3 :: b4 :: rest) = rest.drop n := by
    rw [Nat.add_comm]; rfl
  by_cases h1 : 16640 < n
  · simp [h1]; rfl
  · by_cases h2 : rest.length < n
    · have h4 : rest.length + 1 + 1 + 1 + 1 + 1 < 5 + n := by omega
      simp [h1, h2, h3, h4]; rfl
    · have h4 : ¬ rest.length + 1 + 1 + 1 + 1 + 1 < 5 + n := by omega
      simp only [h1, h2, h3, h4, if_false, hd]
      cases records f (rest.drop n) <;> rfl

/-! ### Against the reference -/

/-- **`records_complete`.** Well-formed records followed by an incomplete tail are split into
exactly those records and that tail. -/
theorem records_complete : ∀ (rs : List Record) (tail : Bytes) (fuel : Nat),
    (∀ r ∈ rs, WellFormed r) → Incomplete tail → rs.length < fuel →
    records fuel (rs.flatMap encode ++ tail) = .ok (rs, tail)
  | [], tail, fuel, _, hi, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      simp only [List.flatMap_nil, List.nil_append]
      rcases hi with h5 | ⟨hle, hlt⟩
      · exact records_short f tail h5
      · match tail, hle, hlt with
        | b0 :: b1 :: b2 :: b3 :: b4 :: rest, hle, hlt =>
          simp only [announced, List.getD_cons_succ, List.getD_cons_zero, List.length_cons] at hle hlt
          rw [records_step, if_neg (by omega), if_pos (by omega)]
        | [], _, hlt | [_], _, hlt | [_, _], _, hlt | [_, _, _], _, hlt | [_, _, _, _], _, hlt =>
          exact records_short f _ (by simp)
  | r :: rs, tail, fuel, hw, hi, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      obtain ⟨hk, hv, hb⟩ := hw r (by simp)
      have ih := records_complete rs tail f (fun q hq => hw q (by simp [hq])) hi (by simp at hf; omega)
      have e3 : (UInt8.ofNat (r.body.length / 256)).toNat = r.body.length / 256 := toNat_ofNat_lt _ (by omega)
      have e4 : (UInt8.ofNat (r.body.length % 256)).toNat = r.body.length % 256 := toNat_ofNat_lt _ (by omega)
      have en : 256 * (r.body.length / 256) + r.body.length % 256 = r.body.length := by omega
      simp only [List.flatMap_cons, List.append_assoc, encode, List.cons_append, List.nil_append]
      rw [records_step, e3, e4, en, if_neg (by omega), if_neg (by simp), List.drop_left, List.take_left, ih]
      simp only [recOf, toNat_ofNat_lt _ hk, toNat_ofNat_lt _ (show r.version / 256 < 256 by omega),
        toNat_ofNat_lt _ (show r.version % 256 < 256 by omega)]
      congr
      omega

/-- **`records_sound`.** Whatever `records` returns, the input is those records, RFC-encoded, then
the pending bytes; every record is well-formed and the pending bytes hold no whole record. -/
theorem records_sound : ∀ (fuel : Nat) (b : Bytes) (rs : List Record) (p : Bytes),
    records fuel b = .ok (rs, p) →
    b = rs.flatMap encode ++ p ∧ (∀ r ∈ rs, WellFormed r) ∧ Incomplete p
  | 0, b, rs, p, h => by
      unfold records at h
      split at h
      · next he =>
        cases h
        simp at he
        subst he
        exact ⟨rfl, by simp, Or.inl (by simp)⟩
      · cases h
  | f + 1, b, rs, p, h => by
      by_cases h5 : b.length < 5
      · rw [records_short f b h5] at h
        cases h
        exact ⟨rfl, by simp, Or.inl h5⟩
      · match b, h5, h with
        | b0 :: b1 :: b2 :: b3 :: b4 :: rest, _, h =>
          rw [records_step] at h
          split at h
          · cases h
          · split at h
            · next hlt hrl =>
              cases h
              refine ⟨rfl, by simp, Or.inr ⟨?_, ?_⟩⟩
              · simp only [announced, List.getD_cons_succ, List.getD_cons_zero]; omega
              · simp only [announced, List.getD_cons_succ, List.getD_cons_zero, List.length_cons]; omega
            · next hlt hrl =>
              split at h
              · next t p' hr =>
                cases h
                obtain ⟨hb, hw, hi⟩ := records_sound f _ t p hr
                have hn : (rest.take (256 * b3.toNat + b4.toNat)).length = 256 * b3.toNat + b4.toNat := by
                  simp; omega
                have hb3 := b3.toNat_lt
                have hb4 := b4.toNat_lt
                have hb1 := b1.toNat_lt
                have hb2 := b2.toNat_lt
                refine ⟨?_, ?_, hi⟩
                · simp only [List.flatMap_cons, encode, recOf, hn, List.append_assoc, ← hb,
                    List.take_append_drop, List.cons_append, List.nil_append]
                  rw [show (256 * b1.toNat + b2.toNat) / 256 = b1.toNat by omega,
                    show (256 * b1.toNat + b2.toNat) % 256 = b2.toNat by omega,
                    show (256 * b3.toNat + b4.toNat) / 256 = b3.toNat by omega,
                    show (256 * b3.toNat + b4.toNat) % 256 = b4.toNat by omega,
                    ofNat_toNat, ofNat_toNat, ofNat_toNat, ofNat_toNat, ofNat_toNat]
                · intro r hr'
                  simp only [List.mem_cons] at hr'
                  rcases hr' with rfl | hr'
                  · exact ⟨by simp only [recOf]; exact b0.toNat_lt, by simp only [recOf]; omega,
                      by simp only [recOf]; rw [hn]; omega⟩
                  · exact hw r hr'
              · cases h
        | [], h5, _ | [_], h5, _ | [_, _], h5, _ | [_, _, _], h5, _ | [_, _, _, _], h5, _ =>
          exact absurd (by simp) h5

/-- **`records_overflow`.** A header announcing more than 2^14 + 256 bytes is an error, whatever
follows it. -/
theorem records_overflow (f : Nat) (b : Bytes) (h5 : 5 ≤ b.length) (h : 16640 < announced b) :
    records (f + 1) b = .error "TLS record overflow" := by
  match b, h5, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest, _, h =>
    simp only [announced, List.getD_cons_succ, List.getD_cons_zero] at h
    rw [records_step, if_pos h]
  | [], h5, _ | [_], h5, _ | [_, _], h5, _ | [_, _, _], h5, _ | [_, _, _, _], h5, _ =>
    exact absurd h5 (by simp)

/-- **`receive_one`.** The callers' check (`records 2 wire` is exactly one record and nothing left)
accepts exactly the wires that are one RFC 8446 record. -/
theorem receive_one (wire : Bytes) (r : Record) :
    records 2 wire = .ok ([r], []) ↔ WellFormed r ∧ wire = encode r := by
  constructor
  · intro h
    obtain ⟨hb, hw, -⟩ := records_sound 2 wire [r] [] h
    exact ⟨hw r (by simp), by simpa using hb⟩
  · rintro ⟨hw, rfl⟩
    have := records_complete [r] [] 2 (by simpa using hw) (Or.inl (by simp)) (by simp)
    simpa using this

end TlsMpc.KernelSpecs.ParseTlsRecord
