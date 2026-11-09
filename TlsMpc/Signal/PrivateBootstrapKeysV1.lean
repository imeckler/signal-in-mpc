import TlsMpc.Signal.Pqxdh
import TlsMpc.Signal.DhRatchet

/-! Internal fresh-session key composition for the one-time-prekey profile.
The native adapter must supply its ACTUAL computed DH/KEM results and validation
status, never caller-asserted agreements or trust/signature flags. This module
neither authorizes a bundle nor implements SPQR negotiation or message release.
It binds all-zero rejection, retained identity and KEM status before exposing a
candidate initial DR state. No old established state is overwritten on failure. -/
namespace TlsMpc.Signal.PrivateBootstrapKeysV1
open Std.Tactic.BVDecide

def part (xs : List B) (offset count : Nat) : List B := (xs.drop offset).take count

def acceptance (a : ByteAuth.Ops B) (validated : B) (identity dh kem : List B) : B :=
  let flags := [ByteAuth.eqMask a validated (a.const 255),
    ByteAuth.eqMask a (OpenResult.get a kem 0) (a.const 255),
    ByteAuth.eqMask a (OpenResult.get a kem 1) (a.const 8),
    ByteAuth.equalMask a identity (part dh 96 32)] ++
    (List.range 5).map (fun i => DhRatchet.agreementMask a (part dh (128+32*i) 32))
  flags.foldl a.and (a.const 255)

/-- Input exact native DH288, tagged KEM result1602, normalized signed prekey32
and retained own identity public32, plus actual validation result mask. Output
valid1||basePublic32||senderState136||five receiver slots345||initialPQR32.
Initial receiver is last; other four are canonical absent. -/
def prepareKeys (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (validated : B)
    (identity signed dh kem : List B) : List B :=
  let shape := if identity.length=32 ∧ signed.length=32 ∧ dh.length=288 ∧ kem.length=1602
    then a.const 255 else a.const 0
  let ok := a.and shape (acceptance a validated identity dh kem)
  let initial := Pqxdh.deriveCore s (part dh 128 32) (part dh 160 32)
    (part dh 192 32) (part dh 224 32) (part kem 1570 32)
  let ratchet := DhRatchet.materialFast s (initial.take 32) (part dh 256 32)
  let sender := ratchet.take 32 ++ part dh 32 64 ++ ratchet.drop 32 ++ List.replicate 8 (a.const 0)
  let receivers := List.replicate (4*69) (a.const 0) ++
    [a.const 255] ++ signed ++ part initial 32 32 ++ List.replicate 4 (a.const 0)
  ok :: ByteAuth.release a ok (part dh 0 32 ++ sender ++ receivers ++ initial.drop 64)

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem part_map (xs : List B) (offset count : Nat) :
    (part xs offset count).map f = part (xs.map f) offset count := by
  simp only [part,List.map_take,List.map_drop]

include ha in
theorem acceptance_map (validated : B) (identity dh kem : List B) :
    f (acceptance a validated identity dh kem) =
    acceptance a' (f validated) (identity.map f) (dh.map f) (kem.map f) := by
  unfold acceptance
  generalize hflags : [ByteAuth.eqMask a validated (a.const 255),
    ByteAuth.eqMask a (OpenResult.get a kem 0) (a.const 255),
    ByteAuth.eqMask a (OpenResult.get a kem 1) (a.const 8),
    ByteAuth.equalMask a identity (part dh 96 32)] ++
    (List.range 5).map (fun i => DhRatchet.agreementMask a (part dh (128+32*i) 32)) = flags
  have fold (xs : List B) (z : B) : f (xs.foldl a.and z) = (xs.map f).foldl a'.and (f z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons x xs ih => simpa only [List.foldl_cons,List.map_cons,ha.and] using ih (a.and z x)
  rw [fold,ha.const,←hflags]
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,OpenResult.get_map ha,part_map,
    DhRatchet.agreementMask_map ha,ha.const]

include hs ha in
theorem prepareKeys_map (validated : B) (identity signed dh kem : List B) :
    (prepareKeys s a validated identity signed dh kem).map f =
    prepareKeys s' a' (f validated) (identity.map f) (signed.map f) (dh.map f) (kem.map f) := by
  simp only [prepareKeys,List.length_map]
  split <;> simp only [List.map_cons,List.map_nil,ByteAuth.release_map ha,
    List.map_append,List.map_take,List.map_drop,List.map_replicate,ha.and,ha.const,
    acceptance_map ha,part_map,Pqxdh.deriveCore_map hs,DhRatchet.materialFast_map hs]

end Refinement

theorem compiled_prepareKeys_correct (validated : BVExpr 8)
    (identity signed dh kem : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(prepareKeys Sha256.symbolic ByteAuth.symbolic validated identity signed dh kem).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (prepareKeys Sha256.symbolic ByteAuth.symbolic validated identity signed dh kem))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (prepareKeys Sha256.symbolic ByteAuth.symbolic validated identity signed dh kem))).vec.get index hi)) =
      (ByteCircuit.joinValue (prepareKeys Sha256.concrete ByteAuth.concrete (BVExpr.eval assign validated)
        (identity.map (BVExpr.eval assign)) (signed.map (BVExpr.eval assign))
        (dh.map (BVExpr.eval assign)) (kem.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,prepareKeys_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivateBootstrapKeysV1
