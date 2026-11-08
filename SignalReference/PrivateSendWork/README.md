# Private canonical counter widths (candidate)

One circuit accepts every uint32 counter/previous value. Canonical varints
are packed with private lengths, one AES-CBC computation produces the
ciphertext, and one private-length HMAC authenticates the resulting Signal
wire. Output is validity8 || private lengthBE16 || public-capacity data.
No public canonical width is supplied or changed at127→128.

The two audited kernel endpoints establish compiler agreement with the
concrete composition. Buffer/varint/hash integer semantics remain unproved.
The13 fixture comparisons use actual pinned libsignal0.106.1 and the same
artifact across every width boundary. These are message construction checks,
not repeated ratchet-state transitions, native MPC delivery, or sealed-service
integration. Authenticated state binding, variable PQ/epoch selection and
recoverable persistence remain dependencies.
