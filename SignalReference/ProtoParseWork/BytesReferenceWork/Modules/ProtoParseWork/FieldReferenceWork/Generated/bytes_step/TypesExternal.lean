import Aeneas

/-! Candidate content abstraction for immutable Bytes. Allocation, reference counts,
addresses and Drop are not observed by this bounded parsing reference. UninitSlice
occurs only in the unused BufMut/append_to dictionary; no uninitialized read or
mutation operation is modeled or invoked in this extraction. -/
@[rust_type "bytes::bytes::Bytes"]
structure bytes.bytes.Bytes where
  contents : Aeneas.Std.Slice Aeneas.Std.U8

@[rust_type "bytes::buf::uninit_slice::UninitSlice"]
structure bytes.buf.uninit_slice.UninitSlice where
  cells : Aeneas.Std.Slice (Option Aeneas.Std.U8)
