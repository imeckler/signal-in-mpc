import SkipTranslatorWork.Generated.skip.FunsExternal

namespace LibSignalReference.Candidate.ProstSkipBuf
open Aeneas Aeneas.Std LoopSupportSkip
set_option maxHeartbeats 200000

def drop (bytes : Slice U8) (count : Nat) : Slice U8 :=
  ⟨bytes.val.drop count, by have h := bytes.property; simp only [List.length_drop]; omega⟩

def remaining (bytes : Slice U8) : Result Usize := .ok bytes.len

def chunk (bytes : Slice U8) : Result (Slice U8) := .ok bytes

def advance (bytes : Slice U8) (count : Usize) : Result (Slice U8) :=
  if bytes.length < count.val then .fail .panic else .ok (drop bytes count.val)

def getByte (bytes : Slice U8) : Result (U8 × Slice U8) := do
  let count ← remaining bytes
  if count < 1#usize then .fail .panic else do
    let view ← chunk bytes
    let value ← Slice.index_usize view 0#usize
    let next ← advance bytes 1#usize
    .ok (value,next)

/-- Exact four-slot byte-slice Buf instance; get_u8 is the pinned default body. -/
def sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  ⟨remaining,chunk,advance,getByte⟩

theorem default_getByte (bytes : Slice U8) :
    LoopSupportSkip.bytes.buf.buf_impl.Buf.get_u8.default sliceBuf bytes = getByte bytes := rfl

theorem remaining_spec (bytes : Slice U8) :
    Mut0T.Insts.BytesBufBuf_implBuf.remaining sliceBuf bytes = .ok bytes.len := rfl

theorem chunk_spec (bytes : Slice U8) :
    Mut0T.Insts.BytesBufBuf_implBuf.chunk sliceBuf bytes = .ok bytes := rfl

theorem advance_spec (bytes : Slice U8) (count : Usize) (h : count.val ≤ bytes.length) :
    sliceBuf.advance bytes count = .ok (drop bytes count.val) := by
  exact if_neg (by omega)

theorem drop_length (bytes : Slice U8) (count : Nat) :
    (drop bytes count).length = bytes.length-count := List.length_drop

theorem drop_add (bytes : Slice U8) (a b : Nat) : drop (drop bytes a) b = drop bytes (a+b) := by
  apply Subtype.ext
  exact List.drop_drop

theorem getByte_spec (bytes : Slice U8) (h : 0 < bytes.length) :
    sliceBuf.get_u8 bytes = .ok (bytes.val[0]'h,drop bytes 1) := by
  obtain ⟨value,hv,he⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes 0#usize h)
  have hn : ¬bytes.len < 1#usize := by scalar_tac
  have ha := advance_spec bytes 1#usize (by scalar_tac)
  change getByte bytes = _
  unfold getByte remaining chunk
  simp only [bind_tc_ok,if_neg hn,hv]
  change (do let next ← sliceBuf.advance bytes 1#usize; .ok (value,next)) = _
  rw [ha]
  simp only [bind_tc_ok,he]
  rfl

theorem getByte_empty (bytes : Slice U8) (h : bytes.length = 0) :
    sliceBuf.get_u8 bytes = .fail .panic := by
  change getByte bytes = _
  unfold getByte remaining
  simp only [bind_tc_ok]
  exact if_pos (by scalar_tac)

end LibSignalReference.Candidate.ProstSkipBuf
