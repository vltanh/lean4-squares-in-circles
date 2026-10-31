# Independent review: occupied-arc metric budget and complete cycle bound

Date: October 30, 2026 UTC.

Reviewer: annular-capacity research agent, independent of the assembly
author. The reviewer suggested the radial projection of an actual
outer circle corner into its square's inner arc before the assembly
was frozen. The full proof, its other inputs and all callers were
subsequently reconstructed independently as recorded below.

**Result: PASS at the complete stated scope. No repair requested.**

## 1. Literal source and reconstructed input

The entire 18,761-byte source
`OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md`
was read. Its recomputed SHA256 is

    369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403

The original arc input in Sections 1--4 of
`CYCLIC_GLOBAL_CONTINUATION.md` was also read and reconstructed. Its
SHA256 agrees with the imported pin

    e319e541254f50aceff0d72775386187f1505a5edf817d7f3e5b10ce27bc4984

The new manuscript supplies the full required proof again, with
outward own axes, actual closed-circle intersection and the precise
relative-interior statement. It does not merely import an existence
claim about two points or an unspecified arc.

## 2. Full intersection and strict occupied length

In the outward own frame, the square is [a-1,a] times [b-1,b],
with a>=b>=1/2 and a^2+b^2=R^2. Every numerical bound used to reduce
its radius-5/4 intersection was independently checked. In particular
a>5/4 makes the outer first-coordinate constraint redundant, while
A=a-1>0 fixes a single angular chart. The inequality
A^2+B^2<(5/4)^2 gives beta>-alpha, including B<0. Thus the entire
closed intersection is exactly one connected arc

    [beta,min(alpha,gamma)].

The convex-in-a+b estimate for E=A^2+B^2+sqrt(2)AB is valid on the
complete actual orientation interval. Both endpoint calculations
are strict at the full allowed radius endpoints. The positive-sign
check before squaring is supplied, and beta+pi/4 is on the required
strictly monotone cosine branch. The parallel-strip derivative and
its b=5/4 endpoint are handled correctly. Both possible limiting
faces therefore leave angular length strictly greater than pi/4.

Every point of the relative interior satisfies all actual square
face inequalities strictly. The limiting arc endpoints are only
asserted to belong to the closed square, so corner or side-boundary
incidences have not been silently promoted to interior points.

## 3. Radial directions, trimming and choice-independent order

For every actual outer circle corner z, the point (rho/R)z has both
own-coordinate inward amounts strictly between zero and one. This
uses R-rho<5/6 and the actual positive outward corner coordinates.
Thus the radial point is strictly in the square and in the relative
interior of its full connected inner arc, for either possible circle
corner and regardless of selected weight.

The center-direction inclusion is also correct: a boundary center
has radius greater than rho, and its inward radial displacement to
rho is less than M-rho=4/15<1/2. The point is in its open incircle.

Because the full arc has length greater than pi/4 and the specified
directions are strictly interior, one can trim both ends by positive
amounts while retaining those directions in the relative interior
and retaining length greater than pi/4. The resulting compact arcs
are pairwise disjoint, with all their endpoints inside the original
open squares. This remains true when the original untrimmed arcs
have touching boundary endpoints.

Their order is the order of the chosen outer-corner directions and
of the center directions. An alternative circle-corner direction
lies in the same full connected arc and cannot pass across a
different square's interior arc. The corner-choice independence is
therefore valid; no small angular offset assumption is needed.

## 4. Force-free metric inequality

Consecutive trimmed arcs and their positive intervening directed gaps
partition the whole inner circle. The endpoints of each gap are actual
points of the two respective physical squares. Their chord is at
least the set distance between those squares, and the full directed
circular arc length is at least that chord. This holds also for a
gap larger than pi and for the two complementary gaps when t=2.
No minor-angle replacement or empty-physical-region claim is made.

Summing the real occupied lengths gives the strict inequality

    sum dist(S_i,S_(i+1)) < (5*pi/16)*(8-t).

Other physical squares can occupy portions of the intervening gaps;
the proof does not remove them. Every selected occupied arc is
strictly longer than pi/4, so strictness survives all allowed circle,
square-face and contact endpoints.

The displayed integral identity proving pi<22/7 was checked by
polynomial division and integration. It yields 5*pi/16<55/56<1.

## 5. Compatible cycle order and actual width reserves

The cycle-order argument uses exactly the stated compatible physical
embedding, not abstract planarity. An actual circle point has a
unique physical owner. Each center-to-circle spoke lies in its own
square interior until its outer endpoint and misses every contact
strand except at its own center. Its direction differs from every
contact direction there. Finitely many sufficiently small junction
and tube changes can therefore preserve all marked spokes, even
when a marked body has additional incident edges.

The embedded simple cycle is a Jordan curve strictly inside the
containing circle. A spoke cannot enter its bounded component and
then reach the circle without another intersection, so the open
spokes lie in the exterior annulus. Their disjointness gives the
marked cyclic order, up to common reversal. No assertion about
whether the disk origin lies inside the cycle is used.

The actual support telescope on a common-normal run gives, for all
points x,y of its two endpoint squares,

    n.(y-x)>=W_i,

where W_i is the sum of the actual internal support widths. Hence
the true set distance satisfies D_i>=W_i>=j_i. Neither collinearity
of means nor a side/diagonal width classification is inserted.

The continuous reserve sum is therefore less than
(5*pi/16)(8-t). Its nonnegative left side first gives t<8. Only
then is the strict factor 5*pi/16<1 used to obtain

    m-t=sum j_i<8-t,
    m<=7.

This checks the sign of the factor 8-t and avoids a hidden assumption
on the number of marks or on the run lengths.

## 6. Full force callers and remaining graph scope

The force caller uses genuinely unloaded true-degree-two vertices of
the full same stress. Their complete two-force equations propagate
the common normal and positive magnitude. All endpoint edges,
weights and original means remain. Torque is unnecessary.

For an entire positive simple-cycle component, the center-dotted
force sum proves that some circle load is positive. The unweighted
force sum gives sum lambda*z=0. A single loaded boundary body cannot
support that zero sum, because its center radius exceeds rho and
its center has strictly positive dot product with every circle
corner. Thus there are at least two marked bodies and the theorem
applies at every possible load count.

For the broader marked chorded-cycle caller, every unmarked circle-
clear vertex is unloaded by the physical circle-atom condition.
If all such vertices have full degree two, zero marks or one mark
would give a positive common-normal support telescope around an
entire loop, which is impossible. This establishes the two-mark
entry condition rather than presupposing it. The final necessary
branch is correct: a surviving compatible cycle of eight or more
bodies must contain a circle-clear vertex with another positive
edge beyond its two cycle edges.

The result does not assert that every large biconnected block has a
cycle satisfying this full-degree premise. A simple outer-face
boundary is a valid caller only after that premise is verified at
each unmarked boundary vertex. A general outer-face walk may repeat
vertices and physical arcs and cannot be charged as a distinct-body
cycle by this proof.

## 7. Exact checks and verification boundary

Direct rational recomputation checked all displayed constants used
in the reconstructed arc proof, including 2081/1600, 933/1600,
the positive square reserve 3937, M-rho=4/15, the center reserve
31/57600, and the rational bound 5*(22/7)/16=55/56. The two literal
source pins were checked after the full reads.

This is a complete independent mathematical review of the force-free
metric theorem, compatible-cycle assembly and full force callers.
No original source bytes, graph or ledger flags, or remote state
were changed. No numerical pose certificate, Lean compilation or
CI run is a premise or claimed verification.
