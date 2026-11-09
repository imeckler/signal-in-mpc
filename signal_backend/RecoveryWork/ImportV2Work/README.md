# Raw-field import private-container candidate

`prepare.py` derives `RawFieldReadmitV2.h` from the unchanged V1 helper. Its exact
listed substitutions change the private local vector allocator and scope/name,
not field arithmetic, masked checks, input ordering or rejection flow. V1 native
receipts remain historical V1 evidence; V2 has not run an MPC import yet.

The allocator clears each complete allocation before release, including vector
growth, destruction and exception cleanup. Only trivially destructible pinned
field/share value types are supported. Nine public local checks verify the wipe
before deallocation, vector-growth value preservation and share-move behavior
at capacities1/17/4096. The full V2 helper typechecks against the actual runtime.
This is C++ source/test evidence with sodium's memory-clearing call trusted;
it is not a mechanized memory-erasure theorem.

This is necessary but insufficient for restore admission. Independent Input,
SubProcessor, Beaver, preprocessing and PRNG owners may retain other secret heap
copies. Machine epoch retirement does not own these helpers. Their concrete
teardown/wipe must finish before machine retirement and the completed erased
host-call barrier; Player references must outlive them. No provider or Session
is activated by this candidate. Full account semantic/certificate checks and
fresh-TLS-only bootstrap are separate requirements.
