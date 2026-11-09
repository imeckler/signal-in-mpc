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
theorem body_step0 (counter : U32) :
  _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body (4#usize) (zeroNonce counter) {start:=0#usize, «end»:=4#usize} zeroBlock =
    .ok (.cont ({start:=1#usize, «end»:=4#usize},zeroBlock)) := by
  have hmax : 0 < UScalar.max .Usize := by scalar_tac
  obtain ⟨difference,hd,hv⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=4#usize) (y:=1#usize) (by scalar_tac))
  have difference_eq : difference = 3#usize := by scalar_tac
  have sub4 : (4#usize - 1#usize : Result Usize) = .ok (3#usize) := by simpa [difference_eq] using hd
  obtain ⟨product,hp,hpv⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=4#usize) (y:=0#usize) (by scalar_tac))
  have product_eq : product = 0#usize := by scalar_tac
  have mul0 : (4#usize * 0#usize : Result Usize) = .ok (0#usize) := by simpa [product_eq] using hp
  simp [sub4, mul0, lift, core.num.U32.to_le_bytes, Slice.len, Array.from_slice, Array.to_slice, Array.to_slice_mut, Slice.index_usize,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut, core.slice.Slice.copy_from_slice,
    hmax, zeroNonce, zeroBlock, chunk_size, _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsIteratorIterator.next, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsCollectIntoIterator.into_iter, _root_.CtrCurrentV1.core.num.U32.to_ne_bytes, _root_.CtrCurrentV1.SliceU32.Insts.CoreOpsIndexIndexUsize.index, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index_mut, _root_.CtrCurrentV1.core.slice.SliceU8.copy_from_slice.specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3, _root_.CtrCurrentV1.hybrid_array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.as_mut_slice.specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2, _root_.CtrCurrentV1.hybrid_array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.as_slice.specialized_Fun_648776846989cc15177b8cf3575dc69c0c5fc05e0c0afc965455e2b1633792c0, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.Insts.CoreOpsIndexIndexUsize.index,
    Aeneas.Std.core.iter.range.IteratorRange.next, Aeneas.Std.core.iter.range.UScalarStep,
    Aeneas.Std.core.iter.range.UScalarStep.forward_checked, Aeneas.Std.core.cmp.PartialOrdUsize,
    Aeneas.Std.core.cmp.impls.PartialOrdUsize.lt]
  simp [List.setSlice!, BitVec.toLEBytes, UScalar.ofNatCore]
theorem body_step1 (counter : U32) :
  _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body (4#usize) (zeroNonce counter) {start:=1#usize, «end»:=4#usize} zeroBlock =
    .ok (.cont ({start:=2#usize, «end»:=4#usize},zeroBlock)) := by
  have hmax : 1 < UScalar.max .Usize := by scalar_tac
  obtain ⟨difference,hd,hv⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=4#usize) (y:=1#usize) (by scalar_tac))
  have difference_eq : difference = 3#usize := by scalar_tac
  have sub4 : (4#usize - 1#usize : Result Usize) = .ok (3#usize) := by simpa [difference_eq] using hd
  obtain ⟨product,hp,hpv⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=4#usize) (y:=1#usize) (by scalar_tac))
  have product_eq : product = 4#usize := by scalar_tac
  have mul0 : (4#usize * 1#usize : Result Usize) = .ok (4#usize) := by simpa [product_eq] using hp
  simp [sub4, mul0, lift, core.num.U32.to_le_bytes, Slice.len, Array.from_slice, Array.to_slice, Array.to_slice_mut, Slice.index_usize,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut, core.slice.Slice.copy_from_slice,
    hmax, zeroNonce, zeroBlock, chunk_size, _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsIteratorIterator.next, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsCollectIntoIterator.into_iter, _root_.CtrCurrentV1.core.num.U32.to_ne_bytes, _root_.CtrCurrentV1.SliceU32.Insts.CoreOpsIndexIndexUsize.index, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index_mut, _root_.CtrCurrentV1.core.slice.SliceU8.copy_from_slice.specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3, _root_.CtrCurrentV1.hybrid_array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.as_mut_slice.specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2, _root_.CtrCurrentV1.hybrid_array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.as_slice.specialized_Fun_648776846989cc15177b8cf3575dc69c0c5fc05e0c0afc965455e2b1633792c0, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.Insts.CoreOpsIndexIndexUsize.index,
    Aeneas.Std.core.iter.range.IteratorRange.next, Aeneas.Std.core.iter.range.UScalarStep,
    Aeneas.Std.core.iter.range.UScalarStep.forward_checked, Aeneas.Std.core.cmp.PartialOrdUsize,
    Aeneas.Std.core.cmp.impls.PartialOrdUsize.lt]
  simp [List.setSlice!, BitVec.toLEBytes, UScalar.ofNatCore]
theorem body_step2 (counter : U32) :
  _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body (4#usize) (zeroNonce counter) {start:=2#usize, «end»:=4#usize} zeroBlock =
    .ok (.cont ({start:=3#usize, «end»:=4#usize},zeroBlock)) := by
  have hmax : 2 < UScalar.max .Usize := by scalar_tac
  obtain ⟨difference,hd,hv⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=4#usize) (y:=1#usize) (by scalar_tac))
  have difference_eq : difference = 3#usize := by scalar_tac
  have sub4 : (4#usize - 1#usize : Result Usize) = .ok (3#usize) := by simpa [difference_eq] using hd
  obtain ⟨product,hp,hpv⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=4#usize) (y:=2#usize) (by scalar_tac))
  have product_eq : product = 8#usize := by scalar_tac
  have mul0 : (4#usize * 2#usize : Result Usize) = .ok (8#usize) := by simpa [product_eq] using hp
  simp [sub4, mul0, lift, core.num.U32.to_le_bytes, Slice.len, Array.from_slice, Array.to_slice, Array.to_slice_mut, Slice.index_usize,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut, core.slice.Slice.copy_from_slice,
    hmax, zeroNonce, zeroBlock, chunk_size, _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsIteratorIterator.next, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsCollectIntoIterator.into_iter, _root_.CtrCurrentV1.core.num.U32.to_ne_bytes, _root_.CtrCurrentV1.SliceU32.Insts.CoreOpsIndexIndexUsize.index, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index_mut, _root_.CtrCurrentV1.core.slice.SliceU8.copy_from_slice.specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3, _root_.CtrCurrentV1.hybrid_array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.as_mut_slice.specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2, _root_.CtrCurrentV1.hybrid_array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.as_slice.specialized_Fun_648776846989cc15177b8cf3575dc69c0c5fc05e0c0afc965455e2b1633792c0, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.Insts.CoreOpsIndexIndexUsize.index,
    Aeneas.Std.core.iter.range.IteratorRange.next, Aeneas.Std.core.iter.range.UScalarStep,
    Aeneas.Std.core.iter.range.UScalarStep.forward_checked, Aeneas.Std.core.cmp.PartialOrdUsize,
    Aeneas.Std.core.cmp.impls.PartialOrdUsize.lt]
  simp [List.setSlice!, BitVec.toLEBytes, UScalar.ofNatCore]
theorem body_step3 (counter : U32) :
  _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body (4#usize) (zeroNonce counter) {start:=3#usize, «end»:=4#usize} zeroBlock =
    .ok (.cont ({start:=4#usize, «end»:=4#usize},expected counter)) := by
  have wrap0 : UScalar.wrapping_add counter (0#u32) = counter := by
    apply U32.bv_eq_imp_eq
    change counter.bv + 0#32 = counter.bv
    exact BitVec.add_zero _
  have hlen : (core.num.U32.to_be_bytes counter).val.length = 4 := by
    simpa using (core.num.U32.to_be_bytes counter).property
  have htake : List.take 4 (core.num.U32.to_be_bytes counter).val = (core.num.U32.to_be_bytes counter).val := by
    exact List.take_of_length_le (by omega)
  have hmax : 3 < UScalar.max .Usize := by scalar_tac
  obtain ⟨difference,hd,hv⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=4#usize) (y:=1#usize) (by scalar_tac))
  have difference_eq : difference = 3#usize := by scalar_tac
  have sub4 : (4#usize - 1#usize : Result Usize) = .ok (3#usize) := by simpa [difference_eq] using hd
  obtain ⟨product,hp,hpv⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=4#usize) (y:=3#usize) (by scalar_tac))
  have product_eq : product = 12#usize := by scalar_tac
  have mul0 : (4#usize * 3#usize : Result Usize) = .ok (12#usize) := by simpa [product_eq] using hp
  simp [sub4, mul0, expected, wrap0, core.num.U32.wrapping_add, lift, core.num.U32.to_le_bytes, Slice.len, Array.from_slice, Array.to_slice, Array.to_slice_mut, Slice.index_usize,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut, core.slice.Slice.copy_from_slice,
    hmax, zeroNonce, zeroBlock, chunk_size, _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop.body, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsIteratorIterator.next, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsCollectIntoIterator.into_iter, _root_.CtrCurrentV1.core.num.U32.to_ne_bytes, _root_.CtrCurrentV1.SliceU32.Insts.CoreOpsIndexIndexUsize.index, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index_mut, _root_.CtrCurrentV1.core.slice.SliceU8.copy_from_slice.specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3, _root_.CtrCurrentV1.hybrid_array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.as_mut_slice.specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2, _root_.CtrCurrentV1.hybrid_array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.as_slice.specialized_Fun_648776846989cc15177b8cf3575dc69c0c5fc05e0c0afc965455e2b1633792c0, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut, _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.Insts.CoreOpsIndexIndexUsize.index,
    Aeneas.Std.core.iter.range.IteratorRange.next, Aeneas.Std.core.iter.range.UScalarStep,
    Aeneas.Std.core.iter.range.UScalarStep.forward_checked, Aeneas.Std.core.cmp.PartialOrdUsize,
    Aeneas.Std.core.cmp.impls.PartialOrdUsize.lt]
  simp [List.setSlice!, wrap0, htake]
theorem actual_current_zero_nonce (counter : U32) :
  _root_.CtrCurrentV1.current (zeroNonce counter) = .ok (expected counter) := by
  have hdefault : _root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default = .ok zeroBlock := by
    simp [_root_.CtrCurrentV1.hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default, core.default.DefaultArray.default, core.default.DefaultU8, core.default.DefaultU8.default, Array.repeat, zeroBlock, UScalar.ofNatCore]
    simp only [UScalar.val]
    rfl
  have hsize : _root_.CtrCurrentV1.typenum.uint.UInt.specialized_Type_1c799a54915353735fd0f1745a60f0a2845f401a2d27317e4978deeff45684ec.Insts.TypenumMarker_traitsUnsigned.USIZE = .ok (4#usize) := by simpa only [_root_.CtrCurrentV1.ctr.flavors.ctr32.CS] using chunk_size
  simp only [_root_.CtrCurrentV1.current, _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block, hdefault, hsize, bind_tc_ok, _root_.CtrCurrentV1.core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsCollectIntoIterator.into_iter, _root_.CtrCurrentV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.current_block_loop]
  rw [loop.eq_1, body_step0]
  dsimp only
  rw [loop.eq_1, body_step1]
  dsimp only
  rw [loop.eq_1, body_step2]
  dsimp only
  rw [loop.eq_1, body_step3]
  dsimp only
  rw [loop.eq_1, body_done]
end LibSignalReference.Candidate.CtrCurrent
