import CtrReferenceV1Work.Generated.CurrentModelViewsV1.Funs
namespace LibSignalReference.Candidate.CtrCurrent
open Aeneas Aeneas.Std
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
abbrev Nonce := _root_.CtrCurrentV1.ctr.flavors.ctr32.CtrNonce32.specialized_Type_3ee6fc9be5d086565369300f5484c0aadceddd5bc39b6c8dc5174325eddd6d23
abbrev Block := _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda
abbrev RangeState := _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9
def zeroNonce (counter : U32) : Nonce := {ctr:=counter,nonce:=⟨List.replicate 4 (0#u32),by decide⟩}
def zeroBlock : Block := ⟨List.replicate 16 (0#u8),by decide⟩
def expected (counter : U32) : Block := ⟨List.replicate 12 (0#u8) ++ (Aeneas.Std.core.num.U32.to_be_bytes counter).val,by simp [(Aeneas.Std.core.num.U32.to_be_bytes counter).property]⟩
theorem chunk_size : _root_.CtrCurrentV1.ctr.flavors.ctr32.CS = .ok (4#usize) := by
  simp only [_root_.CtrCurrentV1.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE, _root_.CtrCurrentV1.typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8, _root_.CtrCurrentV1.typenum.uint.UInt.specialized_Type_d5e40f45dd19e3147d03e3b3ce9d0488cc916aa6e0ad54296d30a480bff33996.Insts.TypenumMarker_traitsUnsigned.USIZE, _root_.CtrCurrentV1.typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8, _root_.CtrCurrentV1.typenum.uint.UInt.specialized_Type_54db470ce4d00d971b243ace6dd3f1a90def4ce728e2899e97a83677edac70bb.Insts.TypenumMarker_traitsUnsigned.USIZE, _root_.CtrCurrentV1.typenum.uint.UInt.specialized_Type_1c799a54915353735fd0f1745a60f0a2845f401a2d27317e4978deeff45684ec.Insts.TypenumMarker_traitsUnsigned.USIZE, _root_.CtrCurrentV1.ctr.flavors.ctr32.CS]
  have hs (x : Usize) (y : I32) : (x <<< y) = UScalar.shiftLeft_IScalar x y := rfl
  have ho (x y : Usize) : (x ||| y) = UScalar.or x y := rfl
  simp only [hs, ho]
  rcases System.Platform.numBits_eq with h | h <;>
    simp [lift, UScalar.cast,UScalar.shiftLeft_IScalar,UScalar.shiftLeft,UScalar.or,h, -BitVec.shiftLeft_eq] <;>
    apply Usize.bv_eq_imp_eq <;>
    simp only [UScalar.ofNatCore] <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_or, h]

theorem body_done (i : Usize) (cn : Nonce) (block : Block) :
  _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body i cn {start:=4#usize, «end»:=4#usize} block = .ok (.done block) := by
  simp [_root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsIteratorIterator.next, Aeneas.Std.core.iter.range.IteratorRange.next,
    Aeneas.Std.core.iter.range.UScalarStep, Aeneas.Std.core.cmp.PartialOrdUsize, Aeneas.Std.core.cmp.impls.PartialOrdUsize.lt]
end LibSignalReference.Candidate.CtrCurrent
