# Root review of the standalone main-height arithmetic and coverage

The root proof agent read the complete independent C++ checker and its
Python wrapper before acceptance. This review concerns the finished
local main-height theorem; it does not close the fixed 010/11 mask.

The reviewed C++ SHA-256 is
`3366f6870300d6fe0d7bd71acf8238d590cb8526bb2ebfeb309e5e6fc6cba40b`.
The wrapper SHA-256 is
`4499ab6164ce779ed75e86071e533815b17dfd05b4b7d14d93cc3a9f86577169`.

## Directed arithmetic

All interval numerators have scale 2^48. The signed quotient routines
correct C++ truncation toward zero by the sign of the remainder, giving
true floor and ceiling for positive denominators. Products inspect all
four endpoint products; quotients inspect all four signed endpoint
quotients. The guarded narrowing routine excludes the minimum signed
64-bit value, so subsequent negations and absolute values are defined.
Products of signed 64-bit endpoints fit the signed 128-bit workspace;
scaled division numerators also fit. Every result is range checked.

The Newton integer square-root routine ends only after checking
r²≤n<(r+1)². Radicals round their lower and upper endpoints outward.
The radicands used here are nonnegative; the main-distance lower bound
19/100 and the clipped endpoint-load radical have separate geometric
justifications in the physical review. No floating arithmetic is used.

The exact root-coordinate numerators are below 2^78, including every
coordinate after at most 70 midpoint subdivisions. Multiplication by
2^48 therefore remains below 2^126. Root denominators and dyadic indices
remain within the same 128-bit workspace. The accepted forest reaches
only depth 44.

## Physical expression reconstruction

The frame ranges follow the proved monotonicities of a,b,h,k on [0,1]
and of the main frame on [1/2,13/20]. Endpoint computations use directed
radicals. Clipping a≤1, b≥0, k≥0 and eta≥0 retains proved physical
identities. The curved tilt toll has its sole interior maximum at t=4/9,
where its value is sqrt(873/4)−27/2. The endpoint minima and this maximum
give its complete interval range.

All four original signed corners are reconstructed through the exact
(±h,±k) vertex identities. This retains correlation within a corner.
The support intersection combines two algebraically identical formulas;
the support≥1 clamp is a physical identity. The denominator floors and
endpoint-load clamp are justified in the independent physical review.
The same original P frame is used in both selected pairs.

## Finite coverage and byte identity

The sixteen roots have the exact rational bounds printed in the theorem.
A midpoint is reconstructed by a binary integer index, never from a
producer float. The preorder parser retains both children of every split,
checks every split axis and scalar channel, rejects premature or trailing
nodes, and verifies the forest identity nodes=2*leaves−16. The wrapper
checks exact metadata types, counts, per-root totals and per-channel
totals. Every accepted leaf requires a newly computed strict negative
upper bound; printed producer margins are not trusted.

The full independent replay passed 9,688,640 leaves and 19,377,264 nodes
with least positive reserve 3012203/2^48. The root inspected the complete
acceptance report and its matching forest counts. Eighteen malformed or
false controls were separately rejected. The deterministic gzip expands
byte-for-byte to the JSON used in that completed arithmetic replay; both
hashes and the identity report are preserved.

The original physical reduction was independently audited by another
proof agent. The root also reviewed the unconditional routing and the
high-floor caller, including the unchanged 6,302-leaf position-table
transfer. Its two existing arithmetic helper files are byte-identical to
the pinned DDAD versions (Git blob hashes 877dfc51168edfc9f178ad7bca126dba4c480c7c
and 56fb16ee498240e272bec65ba4375cc329deeb9f). No accepted table was
silently substituted or widened.

This is a complete local computer-assisted proof with an analytic
physical reduction and independent arithmetic replay. It is not a Lean,
kernel, human-review, global-mask, or unrestricted-equality claim.
