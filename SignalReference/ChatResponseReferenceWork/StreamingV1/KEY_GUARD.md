# Common key rejection component

`KeyGuard` reuses the accepted common key circuit lemma to derive an exact
range/nonzero-tag/wire-kind mask from actual native key validation. Its only new
accepted dependency, `FullParserV3Work.KeyCircuit`, is pinned to its historical
source hash and rechecked in the isolated output before the new modules.

`CoreKeyGuard` proves every native key-validation Err forces actual Core validity
to zero at its terminal byte, and remains zero through arbitrary tails and
finish. Actual Core known-field and recursion conditions remain present: the
proof factors only the failed common guard and does not replace the computation.
Native error constructor/precedence and exact suffix are preserved in the prior
key bridge.

Known-field wire/depth guards, full schema/private-end state induction, and HTTP/
correlation/compiler composition remain open, along with inherited explicit
std/content/allocation/static diagnostic push trust boundaries.
