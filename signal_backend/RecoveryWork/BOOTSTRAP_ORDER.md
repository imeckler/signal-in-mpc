# Pre-Session bootstrap order candidate

`BootstrapOrder` is an embedding-only one-shot coordinator. Even a local load
failure reaches the public collective readiness step; no import runs unless both
local load and the collective succeed. Import returns fresh move-owned state,
its call frame and local quarantine are destroyed, then retirement must finish
before state escapes. Every failure consumes the coordinator and destroys any
fresh state. It has no Session, provider, RPC or TLS-state restore API.

The callbacks are explicit incomplete integration boundaries: the concrete load
must compose CertifiedArchiveGate, CiphertextStore and OwnShareBox; readiness
must be the existing five-party collective; import must scope RawFieldReadmit;
retirement must implement the TLS owner's completed ErasedHostCall/epoch barrier.
The ordering class cannot prove arbitrary callbacks honor those contracts.
Production admission remains closed. It is not evidence of helper-constructor
exception safety or actual native trace retirement.

The 15 sanitizer checks cover success and interruptions at local load, collective
readiness, private import and retirement, exact stage ordering and refusal to
reuse either successful or failed attempts. Tests use no actual account secrets
and make no native MPC or complete recovery claim. A concrete versioned full
account/session/outbox serializer remains necessary before runtime admission.
