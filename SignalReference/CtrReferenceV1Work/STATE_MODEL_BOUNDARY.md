# Unified CTR state-machine source checkpoint

`check_state_models.py` replays the retained named LLBC with unchanged pinned Aeneas, byte-compares generated Types/Funs/template, regenerates authored external bindings, builds the isolated proof closure and audits thirty endpoints against the foundational whitelist. Raw and named graphs differ only in deterministically replayed names. Computational Rust/LLBC/Funs bodies are unchanged.

The unified graph retains all actual Ctr32BE<U16> types and the actual current_block, next_block, from_nonce and remaining bodies. It avoids the pinned discriminant exporter's co-import collision between separately specialized Option types; canonical libraries and generated bodies are not patched.

## Proven composition

* All four current-block mutable slice writes and their writebacks produce twelve zero bytes followed by the U32 counter in big endian, agreeing with the concrete sealed-sender circuit.
* Actual next_block produces that current block, increments the U32 counter modulo 2^32, and preserves the nonce. The no-wrap and exact wrap cases are proved separately; this is not a 128-bit increment model.
* Actual from_nonce on zero16 executes four fixed-four-byte conversion/expect success paths and returns exactly zeroNonce0. All generated writes and constructor fields are retained.
* Actual remaining's extracted arithmetic/control body, relative to the explicitly typed Std value models below, returns Some(MAX32-counter); zero is exactly exhaustion. The widening operation reuses the unchanged actual generated u32→usize leaf.
* An authored sequential driver of unchanged actual next_block calls produces the circuit counter sequence and final counter under counter+n≤MAX32. Actual remaining authorizes this domain. This driver is NOT an extraction of Rust StreamCipherCore, its buffering/XOR closure, or the AES backend.

## Explicit standard-value boundaries

Official pinned Aeneas Array/Slice/Range models provide valid fixed-array content, checked indexing and writeback. Hybrid raw views/defaults bind to those content models. Successful allocation/resources, addresses/layout, Drop, erasure and native endian remain external. The target is pinned aarch64 little endian; zero-nonce bytes are endian-independent.

The pinned translator cannot analyze the included generic Result::expect/ok owned branches and blanket slice TryInto path. Instead, narrowly typed external value definitions are used: four-byte slice conversion forwards to official Aeneas TryFromArrayCopySlice; expect(Ok array) returns the array; Result<usize,TryFromIntError>::ok(Ok n) returns Some n. `StdSuccessReference` checks these exact success contracts and actual widening reuse. These are stated Std-model boundaries, not new actual-source theorems for generic Result, owned Drop, panic formatting, Err-path cleanup or the blanket TryInto implementation. The proved caller never reaches those Err branches; no supplied validity or assumed crypto primitive replaces a computation.

The standard toStr default proof used native reflection for a diagnostic literal. A scoped CtrStateV1.toStr delegates to the EXACT official value with an explicitly kernel-computed bound proof. `literal_same` is rfl for any bound; generated source remains byte-identical. All thirty endpoints now exclude native reflection/sorry/custom axioms.

Actual StreamCipherCore/cipher buffering and bounds/error wrappers, portable AES encryption round/key/layout composition, HMAC/KDF and whole sealed-sender source refinement remain required. No full AES/CTR/HMAC, cryptographic security, runtime throughput or application-readiness claim follows from this checkpoint.
