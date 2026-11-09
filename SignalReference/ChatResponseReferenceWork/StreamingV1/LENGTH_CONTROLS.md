# Native copied-field lexer controls

`OpaqueControls` proves actual opaque payload bytes preserve positions/value, with the exact list shape needed by zipWith select. It inducts through arbitrary bounded opaque prefixes, including previously rejected records and invalid UTF8 bytes.

`LengthControls` derives actual zero/nonzero key/opaque mode selection for every length kind whose kind0 bit is zero; it does not assume body/message-specific cache correctness. `native_length_field_controls` composes actual native length success, terminal lexer reset and exact copy/payload count, deriving positions0/value0 after one exact consumed prefix/native suffix. Empty and nonempty payloads, body/message/header/unknown non-response kinds are covered; validity and UTF acceptance are not premises.

These facts close the next-key scratch-state boundary after successful physical copy; full known-field loop relation and actual schema scan still must join them to source/cache/scope/validity, handle length errors/child overrun/headers/groups/outer schema/correlation/compiler. Explicit std UTF8/static diagnostic push/content boundaries remain unchanged. No runtime/generated computation edits.
