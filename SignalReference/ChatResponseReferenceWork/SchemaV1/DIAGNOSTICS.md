This is an explicit executable diagnostic-stack model, not a completed native
static-reference source bridge. DiagnosticModel executes the existing bounded
Vec.push model, preserving its allocation/capacity failure and divergence before
observation. Theorems retain exact error constructor/parameters and cursor,
prove bounded append and inner-before-outer mutation order, and hide only stack
contents on successful callback execution. No failing computation becomes an
ordinary decoder Err by applying that observation.

The actual pinned caller matters: chat/ws.rs:1389 wraps native owned decode Err
as InvalidProtobuf; line 1339 wraps it as DataError; the received-message handler
at line 1268 warns and continues without changing pending requests or emitting an
application event for DataError. Thus stack contents are irrelevant to this
functional request-state/event observation. Actual warning log text DOES contain
the diagnostics and is explicitly excluded; no log-trace equivalence is claimed.
Mux's stricter abort policy remains a separate application profile.

The four-line stamp_error Rust wrapper independently reproduces the native
DecodeError.push translator failure. All original LLBC/source remains available
by hash and extraction scripts. Literal-only operand retagging fails because
body erasure removes static; a scoped translator prototype moves the failure to
callee inputs. Exact-body literal specialization and one-use safe Box-place
reborrow normalization move it to Vec storage. A separate one-line candidate
corrects InterpPaths' existing comparison of updated_ty against v.ty instead of
its already-computed v_ty; this still exposes static Vec receiver versus shorter
generic reference types. None of these candidates is accepted as a complete
push bridge, and no blanket lifetime compatibility rule is introduced.

Literal specialization rejects dynamic/local, mutable and nonliteral arguments;
the Box pass rejects extra uses, shared reborrow and raw receiver. Native Rust
also rejects the dynamic-to-static borrow regression. A private scoped copy of
pinned Prost adds exact-body literal helpers, leaving the original method
unchanged: 4,368 native comparisons preserve exact error state and append order
for the 13 schema message/field pairs. Test-only Cargo dev/bench metadata is
omitted; runtime dependencies/features and original computation are unchanged.
These native tests do not replace the still-open kernel source bridge.
