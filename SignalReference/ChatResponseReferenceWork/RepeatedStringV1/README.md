Actual pinned Prost repeated String/header primitive, extracted from the unchanged
prost crate. Generated computational declarations reproduce byte-for-byte.
Replayed shares identical primitive Rust types with the proved String extraction
and its existing String byte-content interpretation; only imports change in the
computational module. Named constructor aliases preserve the original interface.

Reference composes the actual generated body with the full String/varint/copier
reference. Wrong wire rejects before reads/default construction. Malformed or
invalid String preserves the old header vector and exact suffix; success appends
one value after all old values, executing the actual existing Vec.push model.
Allocation/capacity failure and divergence are retained before any observation.
No primitive correctness or termination assumption is supplied by the caller.
Native comparisons cover 9,504 exact errors, header vectors and suffixes across
all six wire kinds, old arrays, malformed lengths/overflow, invalid UTF8 and
empty/multiple header values.

Inherited executable UTF8/std unsafe-body, bounded successful allocation and
Take/raw loan content boundaries remain explicit. Local failed String cleanup is
unobservable to this repeated field; the existing owned-error bridge applies.
The separate static-reference diagnostic-stack bridge remains open/trusted.
This primitive does not claim full response schema, HTTP header validation,
private-end streaming/correlation or compiler agreement. check.py verifies the
inherited source chain and affected 22-module kernel closure in a fresh output.
