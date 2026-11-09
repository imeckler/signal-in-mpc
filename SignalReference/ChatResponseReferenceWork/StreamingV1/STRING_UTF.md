# Actual streaming String UTF state

`string_utf_reset` proves the actual Core length terminal resets the validator for all string kinds, empty and duplicate fields included. `string_utf_step` identifies the actual Core payload update with the byte-state validator, including already rejected records.

`string_utf_prefix` proves exact UTF state equality with the executable grammar over arbitrary payload prefixes no longer than the bounded opaque count. It derives actual mode/count/kind preservation while further bytes remain. There is no valid255 or accepted-UTF8 hypothesis: malformed and truncated byte strings are included. `string_utf_complete` gives the exact grammar acceptance mask at the end.

This reuses the three source/object hashes for Utf8Spec/ByteMasks/Utf8Machine from frozen component-audit.json, verifying those exact dependencies, and checks only the new integration modules in a separate output directory. The receipt records the original component receipt hash, exact reused source/object hashes and new clean combined kernel log. No std raw-pointer validator body bridge is claimed. Actual String merge/control/content and error-clear source references remain separate; full field/headers/schema/HTTP/compiler integration remains open. No runtime/generated computation edits.
