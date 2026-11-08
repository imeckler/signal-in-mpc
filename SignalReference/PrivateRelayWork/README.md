# Private-length actual relay encoder candidate

Canonical base64 padding, decimal widths, protobuf length/uint64 ID fields
and masked RFC6455 binary-frame length are shared. The output is a typed
validity8 || BE16 private length || public-capacity frame, suitable for the
TLS private-length interface. Public metadata format is unchanged57 bytes;
ciphertext is a bounded private buffer. No plaintext HTTP/gRPC substitute.

Seven public cases use the actual pinned generated Signal protobuf decoder
and JSON/base64 implementation across changing numeric/ciphertext lengths;
three invalid-status/bounds cases reject to zeros. Six standard-axiom kernel
endpoints establish compiler agreement with the concrete model. Integer
packing/base64/decimal semantics remain unproved. Device-store membership,
authenticated UUID/UAK binding, all-device fanout, fresh mask generation,
response correlation, native MPC and service delivery are separate gaps.
