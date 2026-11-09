# Scoped FnMut borrowed-triple projection regression

The six-line original Rust regression reproduces an existing ABI gap: the
standalone actual closure helper returns `(output,left,right,closure)`, while
the generic caller restores `(output,closure,left,right)`. The ordinary Aeneas
FnMut model also lacks the borrowed-argument returns. This is an extraction
representation issue, not permission to discard any restored value.

The replay specializes only the two explicit borrowed-U32 argument types and
nonborrowed U32 argument at trait type annotations. It moves the original raw
helper to a namespace without modifying its computational body. A tagged
`LoanOp` gives direct calls the raw view and the trait field its precise
permutation. Generated caller and closure computations remain unchanged.

`Projection` proves inverse permutations for every Result outcome, including
outer fail/div and arbitrary output contents. All closure/left/right values are
retained. No coercion is installed for arbitrary functions. `actual_reference`
kernel checks the original generated caller against exact Rust values; 8192
native cases also cover output, both mutable arguments and captured closure
restoration. The unchanged unadapted replay must fail kernel type checking.

This is a scoped model/ABI boundary, not a verified Rust unsafe-memory model.
It is not yet instantiated for the actual Prost submessage merger. The generic
projection is reusable there only after exact type/call/body provenance checks.
