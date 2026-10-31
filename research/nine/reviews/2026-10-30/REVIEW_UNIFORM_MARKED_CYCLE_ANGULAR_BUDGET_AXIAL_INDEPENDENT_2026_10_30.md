# Independent full review: the marked-cycle angular budget

**Date:** October 30, 2026 UTC. **Reviewer:** axial-chain agent, separate
from the author. The whole current source, the complete inner-arc
dependency, and the cited alternative physical embedding constructions
were read and reconstructed.

Reviewed source:

`UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md`

* Bytes: 17899.
* SHA256: `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.
* Git blob: `172ffd399e67a199fba9249d449a0a29fef5fd4e`.

## Conclusion

**PASS at the entire printed scope, with no repair required.** A simple
compatible physical cycle whose unmarked runs have actual common signed
support normals, and whose marked bodies physically touch the circle,
satisfies body count plus two-internal-body run count at most eight.
This includes arbitrary additional positive edges at marked bodies.
The full-force caller correctly requires true degree two and zero
selected circle load at every unmarked body in the same certificate.

The all-load-count simple-nine-cycle exclusion and the eight-cycle
long-run exclusion follow. The record seven-body orbit remains.
The two actual annular-order arguments establish the required order
without a corner-angle estimate, convex force polygon, angular
stationarity, or an assertion that the origin is inside the cycle.

## 1. Complete reconstruction of the inner-arc dependency

The pinned `CENTERED_INNER_ARC.md` was read in full, including its
continuous interior proof, not merely the forty-degree corollary.
Let r be a circle-touching square's center radius and let its angle
to one own axis be phi in [0,pi/4], with s=sin(phi), c=cos(phi).
The circle condition is

`r^2+r(s+c)+1/2=R^2`.

Completing the square and using `(s+c)^2<=2` gives
`r<=R-(s+c)/2<133/64-(s+c)/2`. The lower radius window gives
`r>=R-1/sqrt(2)>5/4`. Both strict comparisons are valid throughout
the closed printed radius window.

For alpha=pi/9, monotonic triple-angle polynomials give
`cos(alpha)>15/16` and `sin(alpha)<11/32`. The test polynomial
values are `495/1024<1/2` and `7117/8192>sqrt(3)/2`; the latter
positive square comparison is correct. For any point on the entire
closed radius-5/4 arc of halfwidth alpha around the center direction,
its radial inward displacement K and transverse displacement L have
the strict upper bounds

`K<29/32-(s+c)/2`, `|L|<55/128`.

The resulting two own-coordinate absolute deviations are bounded
by the printed F1,F2. Their difference is
`(c-s)((s+c)/2-61/128)>=0`, so it suffices to bound F1 below 1/2.
The estimates `1-3*s^2/5<=c<=1-s^2/2` are valid over the whole
interval and give the printed cubic P(s) as a lower bound for
`1-2*F1`.

After `z=s-3/8`, the cubic expansion is exact. Since `|z|<=3/8`,
its quadratic coefficient is at least `339/640>0`, and the
constant and linear terms give the strict reserve `117/40960`.
Thus both own-coordinate deviations are strictly below one half,
including the two angular endpoints. The full closed arc is in
the square's open interior. If two boundary center directions had
minor separation at most forty degrees, the midpoint direction
would put the same radius-5/4 point in both open squares. Hence
every such minor separation is strictly greater than forty degrees.

This dependency is physical: it does not discard a boundary square
or circle corner whose selected multiplier happens to vanish.

## 2. Common-normal runs and true-degree scope

The actual farthest-corner formula gives `|c|<M=91/60`, with reserve
`31/57600` at M. Distinct actual centers have distance at least one
by the open incircles. Actual supported contacts along a run
telescope to

`n.(c_B-c_A)=h_A+h_B+sum 2*h_internal >= j+1`.

For j>=3 this exceeds the center diameter, so j is zero, one or
two. Counting each run's starting mark plus its internal bodies
gives `m=k0+2*k1+3*k2`.

For the stress caller, each unmarked body's only two positive
pair forces are equal and opposite, because it is unloaded and
has true positive degree two in the full retained graph. These
balances propagate the common signed normal through the run.
No moment equation or side/diagonal width classification is used.
Marked endpoint forces and degrees are irrelevant to this
telescoping identity and are all retained.

## 3. Actual radial arcs and actual cycle spokes establish center order

The first annular-order argument is fully geometric. A circle point
has a unique actual square owner: at an owning square corner z,
both inward side axes u,v have `z.u,z.v<=-1/2`, so nearby points
`z-epsilon*z` lie in that square's open interior. Two owners would
overlap there. A circle touch occurs at a square corner by strict
convexity of the disk.

For each marked body set `P=(5/4)c/|c|` and choose any one of its
actual circle corners z. The complete inner-arc lemma puts P in
its open interior. Every circle corner is a farthest corner, so

`z.(c/|c|)=|c|+(|c.u|+|c.v|)/(2|c|)>=|c|+1/2>7/4`.

Consequently the straight segment from P to z is a proper arc in
the annulus from radius 5/4 to radius R: every point after P has
projection on c/|c| greater than 5/4 and hence lies outside the
inner circle; every point before z lies strictly inside the outer
disk. Convexity of the actual square puts all those points in its
open interior. These segments are disjoint for different marked
bodies, with unique outer endpoints. Cutting the annulus along one
arc and applying Jordan separation shows that their cyclic orders
on its two boundary circles agree. Thus the chosen physical circle
corners have the same cyclic order as the center directions.

The second annular-order argument uses the explicit compatibility
premise on the actual contact drawing. Each marked center-to-circle-
corner spoke lies inside its own square except at the circle endpoint.
It cannot share a ray with an actual contact point: a ray from an
interior center meets the square boundary at only one point, and
the chosen circle corner belongs to no other square. Thus it
meets the initial contact drawing only at its own center.

There are finitely many junctions and strands, all strictly inside
the containing disk. Their local disks and tubes can be chosen to
avoid all marked spokes, with separate angular sectors near marked
centers. The compatible drawing therefore retains the spokes even
when marked vertices have extra positive edges. Its simple cycle
is a Jordan curve Gamma strictly inside the circle. The interior
of each spoke must be outside Gamma: its other endpoint reaches
the containing circle without crossing Gamma.

The annular-order fact between Gamma and the containing circle now
identifies marked cycle order with the chosen circle-corner order,
and the first application identifies this with actual center
angular order. Reversing cycle orientation if necessary, its
successive positive center gaps sum to `2*pi`. Each directed gap
is at least its endpoint minor separation. The argument does not
replace a directed gap by the minor gap, and works with two marks
as the two complementary angular gaps. The origin need not lie
inside Gamma.

The imported alternatives have the needed scope. Section 4 of
`PLANAR_STRESS_CORE.md` constructs local noncrossing routes in the
physical square-sector order after removing simultaneous opposite
pairs. Section 5 of `PHYSICAL_BODY_GRAPH_UNCROSSING.md` gives the
corresponding construction with actual aggregate means. The present
theorem uses one such compatible drawing on its own retained
certificate; it does not identify independent selections.

## 4. The eighty- and one-hundred-sixty-degree estimates are exact

The comparison `cos(80 degrees)=sin(10 degrees)>1/6` follows from
strict monotonicity of `3s-4s^3` on (0,1/2) and its test value
`13/27<1/2`. If a one-internal-body run's endpoint minor angle
were at most eighty degrees, its squared center distance would be
less than

`r^2+s^2-(1/3)rs <=(5/3)M^2=8281/2160<4`.

The maximum over `[0,M]^2` is at a corner because the expression
is convex in each variable separately. The four corner values
listed in the source are correct, and the final reserve is
`359/2160`. This contradicts supported center distance at least two.

Similarly `cos(20 degrees)<19/20` follows from the monotonic
triple-angle cosine polynomial and its value `1159/2000>1/2` at
19/20. An endpoint minor angle at most 160 degrees therefore gives
squared distance less than

`(39/10)M^2=107653/12000<9`,

with exact reserve `347/12000`. This contradicts a long run's
supported center distance at least three. Both comparisons include
all endpoint poses and physical circle-mask cases.

The successive angular gaps are therefore strictly larger than
40, 80, or 160 degrees for runs of length zero, one, or two.
Summing gives `360>40(k0+2*k1+4*k2)=40(m+k2)`. The integer
conclusion `m+k2<=8` follows with no endpoint equality exception.

## 5. Complete component and chorded-cycle callers

For an entire simple positive component, the source proves that
there are at least two distinct positive-circle-weight bodies.
The center-dotted force sum has positive right-hand contact work,
so at least one circle atom is positive. The ordinary force sum
has `sum lambda*z=0`. It cannot be supported on one boundary body,
because dotting with that body's center gives strictly positive
contributions for all its corners, using `|c|>5/4>1/sqrt(2)`.
Thus marking the positive-loaded bodies supplies at least two marks,
and every remaining body is truly unloaded of full degree two.

The all-load-count nine-cycle exclusion follows. For eight-body
four-load cycles it excludes both `(2,2,0,0)` and `(2,1,1,0)`,
retaining `(1,1,1,1)`. All nine-body four-load patterns are covered.
The seven-body record `(2,0,1,0)` has `m+k2=8` and is correctly
retained.

In a chorded graph, marking every physical boundary vertex is also
valid when every remaining circle-clear vertex on the cycle has
full true degree two. Zero or one mark is impossible by common-
normal support telescoping around the cycle or the single return
run. Thus every surviving nine-body cycle in this compatible scope
has a circle-clear vertex with an additional positive edge. The
source explicitly preserves that branch and does not claim a
closure of all chorded nine-body blocks.

## Verification record

All displayed exact arithmetic and the three frozen dependency
SHA256 hashes were recomputed. The full inner-arc positivity proof,
both actual annular-order joins, and all full-degree/zero-load
callers were checked without pose sampling. No original ledger
flag, selected normal, actual mean, circle mask, repository metadata,
Lean file, CI state, or remote publication was changed by this review.
