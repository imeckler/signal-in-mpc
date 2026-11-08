Actual pinned Prost bytes::Bytes field reference. Rust/src/lib.rs is a concrete
wrapper around the unchanged public field merger, returning the result, native
Bytes and exact borrowed input suffix. Charon includes the actual sealed Bytes
replacement body, wire check/equality, error constructors and merge control.
It leaves varint and contiguous Bytes storage/copy operations at the existing
accepted executable reference boundaries. No source body is patched.

Generated declarations reproduce byte-for-byte from the extracted LLBC using
the scoped loop translator and existing declaration-name normalization. Replayed
changes imports and colliding discriminant instance names only. Actual
replace_with computes remaining then copy_to_bytes, and Reference proves it
replaces the old Bytes with the exact content. FullReference composes it with
actual varint, underflow/cast bounds and exact contiguous copying. All outcomes
and exact suffixes are retained; wrong wire reads no input, duplicate field
replacement retains no previous contents, failed prefix/underflow preserves old.

The immutable Bytes allocation/reference-count/pointer representation remains
the accepted content model. Generic copy_to_bytes default is used only for the
explicit contiguous slice receiver. The unobserved encode-only append_to fails
closed. No arbitrary segmented Buf or unsafe-memory correctness claim is made.
This component does not establish response schema/default/submessage/header or
streaming/correlation/compiler agreement. check.py checks unchanged generation,
pinned source checksums, affected six-module kernel closure and source hashes.
