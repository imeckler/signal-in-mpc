# Actual supported key validity

`actualKeyGood` is the exact executable keyGood expression of actual Core.step. `known_inner_native_key_good` derives it from actual native key acceptance, current depth0/inner response and actual supported schema wire relation: tags1/2 Varint or tags3/4/5 LengthDelimited. Native range/tag/wire validation, schema recognition and recursion clause are proved, not supplied as an assumed validity mask.

`key_terminal_valid` factors actual Core validity with exact key guard, strict varint/tenth/budget and nonclosing child conditions. `native_known_key_valid` derives those facts and exact consumed prefix/suffix from actual native decode_key success, initial numeric key entry, bounded counters, and a key leaving at least one child byte for its value. The exact-child-end pending-key case is separately rejected in length-errors-audit.json.

Full known-key entry must still join cached data, modes/positions/value/tag/kinds and scope counters on one prefix; full scan must derive those initial conditions and compose all errors, repeated HTTP headers/unknown groups/outer schema/correlation/compiler. Std optimized UTF8/static diagnostic push/content-allocation boundaries remain explicit. No runtime/generated computation edits.
