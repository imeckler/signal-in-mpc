import CtrReferenceV1Work.FixedGeneratorV1Work.GeneratedDirect.Funs
import AesCtrBlockWork.FixedDispatchV1Work.WrapperReference
namespace LibSignalReference.Candidate.FixedCtr
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def zeroNonce (counter : U32) : FixedCtrGenerator.Nonce :=
 {ctr:=counter,nonce:=⟨List.replicate 4 (0#u32),by decide⟩}

theorem nonce_roundtrip (state : FixedCtrGenerator.Nonce) :
 FixedCtrGenerator.fromActual (FixedCtrGenerator.toActual state) = state := rfl

theorem actual_next (counter : U32) :
 FixedCtrGenerator.next_block (zeroNonce counter) =
 .ok (CtrState.expected counter, zeroNonce (core.num.U32.wrapping_add counter (1#u32))) := by
 simp only [FixedCtrGenerator.next_block, zeroNonce, FixedCtrGenerator.toActual]
 change (do let (block,next) ← CtrStateV1.next (CtrState.zeroNonce counter)
            .ok (block,FixedCtrGenerator.fromActual next)) = _
 rw [CtrState.actual_next_zero_nonce]
 rfl

theorem single_actual (keys : Nat → Words (BitVec 64))
 (input : Nat → BitVec 8) (old : Array U8 16#usize) :
 FixedCtrGenerator.Backend.encrypt_block ⟨AesKeyRanges.keyArray keys⟩
  ⟨blockOf input, old⟩ =
 .ok ⟨blockOf input, blockOf (encrypted keys (embed input) 0)⟩ := by
 simp only [FixedCtrGenerator.Backend.encrypt_block, default_batch,
  FixedCtrGenerator.InOut.clone_in, FixedCtrGenerator.InOut.get_out,
  core.convert.IntoFrom.into, core.convert.FromSame.from, bind_tc_ok]
 rw [update_batch]
 simp only [bind_tc_ok, FixedCtrGenerator.aes256_encrypt]
 rw [actual_model]
 simp only [bind_tc_ok, batch_index_zero]
 rfl

def blockBytes (block : Array U8 16#usize) (index : Nat) : BitVec 8 :=
 (block.val[index]?.getD (0#u8)).bv

theorem block_bytes_roundtrip (block : Array U8 16#usize) :
 blockOf (blockBytes block) = block := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro i
 have hn : block.val.length = 16 := by simpa using block.property
 by_cases h : i < 16
 · simp [blockOf, blockBytes, List.getElem?_map, List.getElem?_range, h, hn]
 · have hnone : block.val[i]? = none := List.getElem?_eq_none (by omega)
   simp [blockOf, h, hnone]

theorem generator_actual (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Array U8 16#usize) :
 FixedCtrGenerator.CtrBackend.gen_ks_block
  ⟨zeroNonce counter, ⟨AesKeyRanges.keyArray keys⟩⟩ old =
 .ok (⟨zeroNonce (core.num.U32.wrapping_add counter (1#u32)),
         ⟨AesKeyRanges.keyArray keys⟩⟩,
       (fun value => ⟨value.ctr_nonce, ⟨AesKeyRanges.keyArray keys⟩⟩),
       blockOf (encrypted keys (embed (blockBytes (CtrState.expected counter))) 0)) := by
 simp only [FixedCtrGenerator.CtrBackend.gen_ks_block, actual_next,
  FixedCtrGenerator.make_inout, bind_tc_ok]
 simp only [uncurry_apply_pair, bind_tc_ok]
 have hc := single_actual keys (blockBytes (CtrState.expected counter)) old
 rw [block_bytes_roundtrip] at hc
 rw [hc]
 rfl

theorem generator_counter_no_wrap (counter : U32) (bound : counter.val < 4294967295) :
 (zeroNonce (core.num.U32.wrapping_add counter (1#u32))).ctr.val = counter.val + 1 := by
 exact CtrState.increment_no_wrap counter bound

end LibSignalReference.Candidate.FixedCtr
