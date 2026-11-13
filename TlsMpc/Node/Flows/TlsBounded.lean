import TlsMpc.Node.Flows.Registry
import TlsMpc.Node.Flows.TlsWF

/-!
# The S12 scripts' wires fit the pipe (gap F18)

REORGANIZATION_PLAN.md stage S12, as `Flows/Registry.lean` does for the S9 flows: every instruction
of every S12 script, on every branch, is `Instr.Bounded` (every handle id, width, count, index,
label code, name length and public length below 2^64), so the Lean sender emits only
`Wire.Bounded` wires (Engine/Reveal.lean `nextBatch_bounded`) and the batch encoding round-trips
(`decodeBatch_encodeBatch`). Hypotheses: the handle block `[n, n + k)` below 2^64 (the session
counter), the operand handles' ids below 2^64, and the public sizes (record, content, capacity,
certificate, kernel name parameters) below 2^32. The deployed sizes are below 2^15.

  `Ghash.keyShare_bounded`, `Ghash.round_bounded`, `Tls.sealCtr_bounded`, `Tls.sealClass_bounded`,
  `Tls.tag_bounded`, `Tls.open_bounded`, `Tls.parser_bounded`, `Tls.update_bounded`,
  `Tls.reveal_bounded`, `Tls.range_bounded`, `Tls.public_bounded`, `Tls.drop_bounded`,
  `Tls.derive_bounded`, `Tls.openHandshake_bounded`, `Tls.verify_bounded`, `Tls.finish_bounded`,
  `Tls.agree_bounded`.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.TlsBase

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Registry (length_ascii length_toString big_lt_B64)

theorem length_name0 (s : String) : (name0 s).length = s.length := length_ascii s

theorem length_name1 (s : String) (a : Nat) : (name1 s a).length ≤ s.length + a + 2 := by
  have := length_toString a
  simp only [name1, length_ascii, String.length_append]
  have : " ".length = 1 := by decide
  omega

theorem length_name3 (s : String) (a b c : Nat) : (name3 s a b c).length ≤ s.length + a + b + c + 6 := by
  have := length_toString a
  have := length_toString b
  have := length_toString c
  simp only [name3, length_ascii, String.length_append]
  have : " ".length = 1 := by decide
  omega

theorem name0_lt (s : String) (hs : s.length ≤ 64) : (name0 s).length < B64 := by
  have := big_lt_B64
  rw [length_name0]
  omega

theorem name1_lt (s : String) (a : Nat) (hs : s.length ≤ 64) (ha : a < 4294967296) : (name1 s a).length < B64 := by
  have := big_lt_B64
  have := length_name1 s a
  have : (4294967296 : Nat) * 4 < B64 := by decide
  omega

theorem name3_lt (s : String) (a b c : Nat) (hs : s.length ≤ 64) (ha : a < 4294967296) (hb : b < 4294967296)
    (hc : c < 4294967296) : (name3 s a b c).length < B64 := by
  have := length_name3 s a b c
  have : (4294967296 : Nat) * 4 < B64 := by decide
  omega

end TlsMpc.Node.Flows.TlsBase

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Registry (big_lt_B64 frees_bounded)

/-- Every instruction of an explicit block is bounded: split the membership, then evaluate. -/
macro "bnd_each" : tactic => `(tactic| (
  intro i hi
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  repeat' (rcases hi with rfl | hi)
  all_goals simp (config := { contextual := true }) [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map,
    InstrP.blank, Label.sealedRecord,
    Label.recordKindBit, Label.recordEvent, Label.serverBytes, Label.handshakeRecord, Label.finishedAccepted,
    Label.clientFinished, Ghash.masked, Label.ghashMaskedPower, length_bitsOf, *] <;> omega))

/-- An `openBool` with a registry label is bounded. -/
macro "bnd_one" : tactic => `(tactic| (
  simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Label.sealedRecord,
    Label.recordKindBit, Label.recordEvent, Label.serverBytes, Label.handshakeRecord, Label.finishedAccepted,
    Label.clientFinished, *] <;> omega))

theorem sealCtr_bounded (n : Nat) (traffic content : BoolH) (seq : B8) (kind size padding : Nat)
    (hn : n + 4 < B64) (ht : traffic.id < B64) (hc : content.id < B64) (hs : seq.length = 8)
    (hk : kind < 4294967296) (hz : size < 4294967296) (hp : padding < 4294967296) :
    Every Instr.Bounded (sealCtrScript n traffic content seq kind size padding) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : (sealCtrName kind size padding).length < B64 := name3_lt _ _ _ _ (by decide) hk hz hp
  have hw : 8 * (5 + innerLength size padding + 16) < B64 := by
    simp only [innerLength]
    have : (4294967296 : Nat) * 64 < B64 := by decide
    omega
  unfold sealCtrScript
  refine every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem sealClass_bounded (n : Nat) (traffic content : BoolH) (seq : B8) (size : Nat)
    (hn : n + 5 < B64) (ht : traffic.id < B64) (hc : content.id < B64) (hs : seq.length = 8)
    (hcap : capacity size < 4294967296) :
    Every Instr.Bounded (sealClassScript n traffic content seq size) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : (sealClassName (capacity size)).length < B64 := name1_lt _ _ (by decide) hcap
  have hw : 8 * (1 + 5 + capacity size + 1 + 16) < B64 := by
    have : (4294967296 : Nat) * 64 < B64 := by decide
    omega
  unfold sealClassScript
  generalize capacity size = cap at hname hw hcap ⊢
  refine every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs ?_ _ (by bnd_each))) _ (by bnd_each)
  split
  · exact Every.done _
  · exact Every.abort _

theorem tag_bounded (n : Nat) (pad : BoolH) (halfSlot : Nat) (hn : n + 3 < B64) (hp : pad.id < B64) :
    Every Instr.Bounded (tagScript n pad halfSlot) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : tagName.length < B64 := name0_lt _ (by decide)
  unfold tagScript
  refine every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem open_bounded (n : Nat) (parser traffic : BoolH) (seq tag recordPadded size : B8) (cap halfSlot : Nat)
    (hn : n + 16 < B64) (hp : parser.id < B64) (ht : traffic.id < B64) (hs : seq.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length < 4294967296) (hz : size.length = 2)
    (hcap : cap < 4294967296) :
    Every Instr.Bounded (openScript n parser traffic seq tag recordPadded size cap halfSlot) := by
  have hB : 18446744073709551615 < B64 := by decide
  have h1 : checkName.length < B64 := name0_lt _ (by decide)
  have h2 : (typedName cap).length < B64 := name1_lt _ _ (by decide) hcap
  have h3 : (frameName cap).length < B64 := name1_lt _ _ (by decide) hcap
  have hw : 128 + 8 * (cap - 21) + 8 * (cap - 17) < B64 := by
    have : (4294967296 : Nat) * 64 < B64 := by decide
    omega
  unfold openScript checkBlock typedBlock
  refine every_seqs (every_openThen (by bnd_one) (fun bit => ?_)) _ (by bnd_each)
  unfold afterBit
  split
  · unfold directRest
    exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
      (by bnd_each)
  · split
    · unfold frameRest
      exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
        (by bnd_each)
    · exact Every.abort _

theorem parser_bounded (n : Nat) (hn : n + 1 < B64) : Every Instr.Bounded (parserScript n) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : parserName.length < B64 := name0_lt _ (by decide)
  unfold parserScript
  exact every_seqs (Every.done _) _ (by bnd_each)

theorem update_bounded (n : Nat) (traffic : BoolH) (hn : n < B64) (ht : traffic.id < B64) :
    Every Instr.Bounded (updateScript n traffic) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : updateName.length < B64 := name0_lt _ (by decide)
  unfold updateScript
  exact every_seqs (Every.done _) _ (by bnd_each)

theorem reveal_bounded (n : Nat) (length content : BoolH) (cap : Nat) (hn : n + 3 < B64)
    (hl : length.id < B64) (hc : content.id < B64) (hcap : cap < 4294967296) :
    Every Instr.Bounded (revealScript n length content cap) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : (revealName cap).length < B64 := name1_lt _ _ (by decide) hcap
  have hw : 16 + 8 * cap < B64 := by
    have : (4294967296 : Nat) * 64 < B64 := by decide
    omega
  unfold revealScript
  exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem range_bounded (n : Nat) (bytes : BoolH) (lo hi : Nat) (hn : n < B64) (hb : bytes.id < B64)
    (hhi : hi < 4294967296) (hlo : lo ≤ hi) : Every Instr.Bounded (rangeScript n bytes lo hi) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hw : 8 * hi < B64 := by
    have : (4294967296 : Nat) * 64 < B64 := by decide
    omega
  unfold rangeScript
  exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem public_bounded (n : Nat) (bytes : B8) (hn : n < B64) (hb : bytes.length < 4294967296) :
    Every Instr.Bounded (publicScript n bytes) := by
  have hB : 18446744073709551615 < B64 := by decide
  unfold publicScript
  exact every_seqs (Every.done _) _ (by bnd_each)

theorem drop_bounded (hs : List BoolH) (h : ∀ g ∈ hs, g.id < B64) : Every Instr.Bounded (dropScript hs) :=
  every_seqs (Every.done _) _ (frees_bounded hs h)

theorem derive_bounded (n : Nat) (agreement : BoolH) (helloHash : B8) (hn : n + 5 < B64)
    (ha : agreement.id < B64) (hh : helloHash.length = 32) :
    Every Instr.Bounded (deriveScript n agreement helloHash) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : deriveName.length < B64 := name0_lt _ (by decide)
  unfold deriveScript
  exact every_seqs (Every.done _) _ (by bnd_each)

theorem openHandshake_bounded (n : Nat) (serverHs : BoolH) (seq record : B8) (hn : n + 2 < B64)
    (hs : serverHs.id < B64) (hq : seq.length = 8) (hr : record.length < 4294967296) :
    Every Instr.Bounded (openHandshakeScript n serverHs seq record) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : (openHsName record.length).length < B64 := name1_lt _ _ (by decide) hr
  unfold openHandshakeScript
  exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem verify_bounded (n : Nat) (serverHs : BoolH) (hash message : B8) (hn : n + 2 < B64)
    (hs : serverHs.id < B64) (hh : hash.length = 32) (hm : message.length = 36) :
    Every Instr.Bounded (verifyScript n serverHs hash message) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : verifyName.length < B64 := name0_lt _ (by decide)
  unfold verifyScript
  exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem finish_bounded (n : Nat) (main clientHs : BoolH) (serverHash clientHash certificate : B8)
    (hn : n + 6 < B64) (hm : main.id < B64) (hc : clientHs.id < B64) (hsh : serverHash.length = 32)
    (hch : clientHash.length = 32) (hcert : certificate.length < 4294967296) :
    Every Instr.Bounded (finishScript n main clientHs serverHash clientHash certificate) := by
  have hw : 960 + 8 * finishedLength certificate.length < B64 := by
    have h1 : 960 + 8 * (certificate.length + 58) < 4294967296 * 64 := by omega
    have h2 : (4294967296 : Nat) * 64 < B64 := by decide
    exact Nat.lt_trans h1 h2
  have hB : 18446744073709551615 < B64 := by decide
  have hname : (finishName certificate.length).length < B64 := name1_lt _ _ (by decide) hcert
  unfold finishScript
  exact every_seqs (every_openThen (by bnd_one) (fun _ => every_seqs (Every.done _) _ (by bnd_each))) _
    (by bnd_each)

theorem agree_bounded (n : Nat) (digest : B8) (valid : Bool) (hn : n < B64) (hd : digest.length = 32) :
    Every Instr.Bounded (agreeScript n digest valid) := by
  have hB : 18446744073709551615 < B64 := by decide
  unfold agreeScript
  refine every_seqs ?_ _ (by bnd_each)
  split
  · exact Every.done _
  · exact Every.abort _

end TlsMpc.Node.Flows.Tls

namespace TlsMpc.Node.Flows.Ghash

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Registry (big_lt_B64)

theorem keyShare_bounded (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) (hn : n + 2 < B64)
    (ht : traffic.id < B64) : Every Instr.Bounded (keyShareScript n traffic maskSlot dst) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : keyShareName.length < B64 := name0_lt _ (by decide)
  unfold keyShareScript keyShareBlock
  exact every_seqs (Every.done _) _ (by bnd_each)

theorem round_bounded (n c leftSlot rightSlot maskSlot dst : Nat) (hn : n + 7 < B64) :
    Every Instr.Bounded (roundScript n c leftSlot rightSlot maskSlot dst) := by
  have hB : 18446744073709551615 < B64 := by decide
  have hname : multiplyName.length < B64 := name0_lt _ (by decide)
  unfold roundScript roundBlock
  split
  · next hc =>
    have hl : (layout c).length < B64 := by rw [length_layout]; omega
    have hj : ∀ j ∈ layout c, j < B64 := fun j hj => by have := layout_bound c j hj; omega
    exact every_seqs (Every.done _) _ (by bnd_each)
  · exact Every.abort _

end TlsMpc.Node.Flows.Ghash
