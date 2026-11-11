import TlsMpc.TlsPostHandshake
import TlsMpc.Signal.Word64Mux

/-! The post-handshake framing of `TlsPostHandshake`, as a smaller circuit.

`TlsPostHandshake.scan` runs `choose active (step s byte) s` on every content
byte: `step` computes all six cases of the state machine as whole states and
five nested `choose`s pick one, then a sixth keeps the old state when the byte
is inactive. Each `choose` selects every field, among them the 64-bit counter,
so one byte costs six 64-bit selects and thirty byte selects.

`gatedStep` computes the same next state field by field: the case masks are
combined with `active` once, and each field goes through only the selects that
can change it (three for the counter, one for the message kind, ...). On values
it equals `choose active (step s byte) s` whenever `active` is 0 or 255
(`gatedStep_eq`), which is what `scan` passes. `core` built on it is therefore
the same function as `TlsPostHandshake.core` (`core_eq`), and a circuit compiled
from it refines `TlsPostHandshake.core` on values (`core_refines`). -/
namespace TlsMpc.TlsPostHandshake.Fast
open Std.Tactic.BVDecide
open Signal.Word64
open TlsMpc.TlsPostHandshake

def gatedStep (o : Ops B W) (a : ByteAuth.Ops B) (active : B) (s : Scan B W) (byte : B) : Scan B W :=
  let p := s.state.phase
  let e0 := a.and active (ByteAuth.eqMask a p (a.const 0))
  let e1 := a.and active (ByteAuth.eqMask a p (a.const 1))
  let e2 := a.and active (ByteAuth.eqMask a p (a.const 2))
  let e3 := a.and active (ByteAuth.eqMask a p (a.const 3))
  let e4 := a.and active (ByteAuth.eqMask a p (a.const 4))
  let other := a.and active (a.not (bor a e0 (bor a e1 (bor a e2 (bor a e3 e4)))))
  let ku := ByteAuth.eqMask a s.state.kind (a.const 24)
  let length := appendByte o s.state.remaining byte
  let badStart := a.not (bor a (ByteAuth.eqMask a byte (a.const 4)) (ByteAuth.eqMask a byte (a.const 24)))
  let badLast := a.and ku (a.not (eq o a length (o.const 1)))
  let badBody := bor a (eq o a s.state.remaining (o.const 0))
    (a.and ku (a.not (bor a (ByteAuth.eqMask a byte (a.const 0)) (ByteAuth.eqMask a byte (a.const 1)))))
  ⟨⟨TlsInner.select a e0 (a.const 1) (TlsInner.select a e1 (a.const 2) (TlsInner.select a e2 (a.const 3)
      (TlsInner.select a e3 (TlsInner.select a (eq o a length (o.const 0)) (a.const 0) (a.const 4))
        (TlsInner.select a e4 (TlsInner.select a (eq o a s.state.remaining (o.const 1)) (a.const 0) (a.const 4)) p)))),
    TlsInner.select a e0 byte s.state.kind,
    o.select e0 (o.const 0) (o.select (bor a e1 (bor a e2 e3)) length
      (o.select e4 (o.sub s.state.remaining (o.const 1)) s.state.remaining)),
    bor a (bor a s.state.bad (a.and active s.update))
      (bor a (a.and e0 badStart) (bor a (a.and e3 badLast) (bor a (a.and e4 badBody) other)))⟩,
    bor a s.update (a.and e4 ku),
    TlsInner.select a (a.and e4 ku) (ByteAuth.eqMask a byte (a.const 1)) s.request⟩

def scan (o : Ops B W) (a : ByteAuth.Ops B) (enabled : B) (length : W) :
    Nat → List B → Scan B W → Scan B W
  | _, [], state => state
  | index, byte :: rest, state =>
      let active := a.and enabled (o.ule (o.const (index+1)) length)
      scan o a enabled length (index+1) rest (gatedStep o a active state byte)

def process (o : Ops B W) (a : ByteAuth.Ops B) (s : State B W) (parsed : List B) : List B :=
  let length := o.pack (List.replicate 6 (a.const 0) ++ [get a parsed 2,get a parsed 3])
  let hs := ByteAuth.eqMask a (get a parsed 1) (a.const 22)
  finish o a s parsed (scan o a hs length 0 (parsed.drop 4) ⟨s,a.const 0,a.const 0⟩)

def core (o : Ops B W) (a : ByteAuth.Ops B) (state parsed : List B) : List B :=
  process o a (decodeState o a state) parsed

section Refinement
variable {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include ho ha

theorem gatedStep_map (active : B) (s : Scan B W) (byte : B) :
    (gatedStep o a active s byte).map f fw = gatedStep o' a' (f active) (s.map f fw) (f byte) := by
  simp only [gatedStep,Scan.map,State.map,appendByte_map ho,
    TlsInner.select_map ha,bor_map ha,ByteAuth.eqMask_map ha,eq_map ho ha,
    ha.const,ha.and,ha.not,ho.const,ho.sub,ho.select]

theorem scan_map (enabled : B) (length : W) (index : Nat) (content : List B) (s : Scan B W) :
    (scan o a enabled length index content s).map f fw =
      scan o' a' (f enabled) (fw length) index (content.map f) (s.map f fw) := by
  induction content generalizing index s with
  | nil => rfl
  | cons b rest ih =>
      simp only [scan,List.map_cons,ih,gatedStep_map ho ha,ha.and,ho.ule,ho.const]

theorem process_map (s : State B W) (parsed : List B) :
    (process o a s parsed).map f = process o' a' (s.map f fw) (parsed.map f) := by
  unfold process
  rw [finish_map ho ha,scan_map ho ha]
  simp only [ByteAuth.eqMask_map ha,get_map ha,
    ho.pack,List.map_append,List.map_cons,List.map_nil,List.map_replicate,ha.const,
    List.map_drop,Scan.map]

theorem core_map (state parsed : List B) :
    (core o a state parsed).map f = core o' a' (state.map f) (parsed.map f) := by
  simp only [core,process_map ho ha,decodeState_map ho ha]

end Refinement

/-! ### On values, the same function -/

private theorem and_on (x : BitVec 8) : 255#8 &&& x = x := BitVec.allOnes_and
private theorem and_off (x : BitVec 8) : 0#8 &&& x = 0#8 := BitVec.zero_and
private theorem bor_or (x y : BitVec 8) : bor ByteAuth.concrete x y = x ||| y := by
  have all : ∀ x y : BitVec 8, (x ^^^ y) ^^^ (x &&& y) = x ||| y := by
    intro x y
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  exact all x y
private theorem or_on (x : BitVec 8) : x ||| 255#8 = 255#8 := by
  have all : ∀ x : BitVec 8, x ||| 255#8 = 255#8 := by decide
  exact all x
private theorem on_or (x : BitVec 8) : 255#8 ||| x = 255#8 := by
  have all : ∀ x : BitVec 8, 255#8 ||| x = 255#8 := by decide
  exact all x
private theorem c_and (x y : BitVec 8) : ByteAuth.concrete.and x y = x &&& y := rfl
private theorem c_not (x : BitVec 8) : ByteAuth.concrete.not x = ~~~x := rfl
private theorem c_const (n : Nat) : ByteAuth.concrete.const n = BitVec.ofNat 8 n := rfl
private theorem sel_on (yes no : BitVec 8) : TlsInner.select ByteAuth.concrete (255#8) yes no = yes :=
  TlsInner.select_accept yes no
private theorem sel_off (yes no : BitVec 8) : TlsInner.select ByteAuth.concrete (0#8) yes no = no :=
  TlsInner.select_reject yes no
private theorem wsel_on (x y : BitVec 64) : concrete.select (255#8) x y = x := select_accept x y
private theorem wsel_off (x y : BitVec 64) : concrete.select (0#8) x y = y := select_reject x y
private theorem or_swap (x y z : BitVec 8) : x ||| (y ||| z) = y ||| (x ||| z) := by
  rw [← BitVec.or_assoc, BitVec.or_comm x y, BitVec.or_assoc]

local macro "cases_simp" : tactic =>
  `(tactic| (simp [gatedStep, choose, step, c_and, c_not, c_const, and_on, and_off, bor_or, or_on, on_or,
      ByteAuth.eqMask_value, sel_on, sel_off, wsel_on, wsel_off] <;> ac_rfl))

theorem gatedStep_eq (active : BitVec 8) (h : active = 0 ∨ active = 255)
    (s : Scan (BitVec 8) (BitVec 64)) (byte : BitVec 8) :
    gatedStep concrete ByteAuth.concrete active s byte =
      choose concrete ByteAuth.concrete active (step concrete ByteAuth.concrete s byte) s := by
  obtain ⟨⟨p, kind, remaining, bad⟩, update, request⟩ := s
  rcases h with rfl | rfl
  · cases_simp
  · by_cases h0 : p = 0#8
    · subst h0
      cases_simp
    · by_cases h1 : p = 1#8
      · subst h1
        cases_simp
      · by_cases h2 : p = 2#8
        · subst h2
          cases_simp
        · by_cases h3 : p = 3#8
          · subst h3
            cases_simp
          · by_cases h4 : p = 4#8
            · subst h4
              cases_simp
            · simp [gatedStep, choose, step, c_and, c_not, c_const, and_on, bor_or, or_on, on_or,
                ByteAuth.eqMask_value, sel_on, sel_off, wsel_on, wsel_off, h0, h1, h2, h3, h4]
theorem scan_eq (enabled : BitVec 8) (h : enabled = 0 ∨ enabled = 255) (length : BitVec 64)
    (index : Nat) (content : List (BitVec 8)) (s : Scan (BitVec 8) (BitVec 64)) :
    scan concrete ByteAuth.concrete enabled length index content s =
      TlsPostHandshake.scan concrete ByteAuth.concrete enabled length index content s := by
  induction content generalizing index s with
  | nil => rfl
  | cons b rest ih =>
      have hactive : ByteAuth.concrete.and enabled (concrete.ule (concrete.const (index+1)) length) = 0 ∨
          ByteAuth.concrete.and enabled (concrete.ule (concrete.const (index+1)) length) = 255 := by
        rw [ule_value]
        rcases h with rfl | rfl <;> split <;> simp [ByteAuth.concrete]
      simp only [scan, TlsPostHandshake.scan, gatedStep_eq _ hactive, ih]

theorem core_eq (state parsed : List (BitVec 8)) :
    core concrete ByteAuth.concrete state parsed =
      TlsPostHandshake.core concrete ByteAuth.concrete state parsed := by
  have hs : ∀ x : BitVec 8, ByteAuth.eqMask ByteAuth.concrete x (ByteAuth.concrete.const 22) = 0 ∨
      ByteAuth.eqMask ByteAuth.concrete x (ByteAuth.concrete.const 22) = 255 := by
    intro x
    rw [ByteAuth.eqMask_value]
    split <;> simp
  simp only [core, process, TlsPostHandshake.core, TlsPostHandshake.process, scan_eq _ (hs _)]

/-- A circuit compiled from `core` with any refinement of the value operations
(in particular `Word64.symbolicMux`) computes `TlsPostHandshake.core`. -/
theorem core_refines {o : Ops B W} {a : ByteAuth.Ops B} {f : B → BitVec 8} {fw : W → BitVec 64}
    (ho : Hom o concrete f fw) (ha : ByteAuth.Hom a ByteAuth.concrete f) (state parsed : List B) :
    (core o a state parsed).map f =
      TlsPostHandshake.core concrete ByteAuth.concrete (state.map f) (parsed.map f) := by
  rw [core_map ho ha, core_eq]

end TlsMpc.TlsPostHandshake.Fast
