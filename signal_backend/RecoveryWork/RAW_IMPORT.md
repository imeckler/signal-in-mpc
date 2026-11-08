# Raw GF128 value re-admission candidate

The archived128-bit LOCAL evaluations are entered as arbitrary fullGF128 private
inputs through ShamirInput<StrongShamirShare<gf2n_long>>. They are never relabeled
as secret bits and never pass a bit-only input mask. Exact pinned source paths:
ShamirInput.hpp::add_mine ignoresn_bits, samples fullScalar random values, and
constructs degree2 sharing; Scalar/open_type here aregf2n_long. SemiInput.h uses
SeededPRNG and SemiInput.hpp exchanges its pairwise seeds. gf2n.cpp::randomize
fills the full128-bit field value. The own16-byte archive codec is polynomial
little-endian, matching the pinnedx128+x7+x2+x+1 field and points1..5.

The candidate privately checksD4=y4+7y1+9y2+15y3 andD5=y5+7y1+8y2+14y3. The
secret decoded value isf0=y1+y2+y3. Bitness is checked with RAW field multiplication
f0(f0+1) through fullfield Beaver/sacrificed triples. It is not a Boolean AIG
expression that a bit optimizer may erase. StrongShamirShare's clear/open_type/
random_type are staticallyGF128 here; MaliciousRepPrep samples fullfield triples.
MaliciousShamirMC uses all5 evaluations and checks3/4/5 reconstructions.

Only a secret-random linear combination of all constraints is opened after
input exchange. Each coefficient is a secret sum of all5 fresh fullfield private
contributions; honest entropy remains unknown to at most2corrupt participants.
The underlying private-input protocol, PRNG, multiplication/sacrifice and checked
opening are explicit trusted MPC boundaries. Conditional on those contracts, any
nonzero constraint is hidden by a uniform field element and false acceptance is
at most2^-128 per batch. No evaluation, constant term or unmasked bitness product
is opened. After a checkedzero result only, fresh degree2 GF128 evaluations are
wrapped in the identical CCD representation; that boundary is not an arbitrary
embedding Bits factory.

This is VALUE re-sharing, not complete restore admission. Certificate/fresh-head
phase agreement, fullSignal schema/immutableintent/outbox, collective readiness,
constructor-exception safety and post-import runtime retirement still gate any
normal provider use. A consistent polynomial alone cannot prove it is the latest
certified snapshot. Current functional probes use public disposable polynomials,
not actualSignal account data, and do not claim full Byzantine-MPC security or
mobile-adversary/proactive-refresh guarantees. The sharing_refresh task stays
paused. Successful import must use a fresh runtime/sharing context; TLS always
starts a fresh connection.
