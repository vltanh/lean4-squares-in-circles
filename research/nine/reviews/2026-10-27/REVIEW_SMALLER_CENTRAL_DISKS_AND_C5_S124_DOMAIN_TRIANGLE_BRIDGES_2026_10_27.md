# Independent review: smaller central-disk capacities and the original C5 S124 root domain

Date: October 27, 2026.
Reviewer: triangle_bridges, separate from author hexagon.

**Result: ACCEPTED in the full stated scopes, with no correction.**
The two physical capacity theorems are whole all-orientation results.
The C5 manuscript is an exhaustive domain reduction with its stated
aligned-low and tilted-high remainders; this review does not close
the original S124 family. Full root review remains separate.

## 1. Complete texts read and pinned

    SMALLER_CENTRAL_DISKS_NINE_UNIT_CAPACITY.md
    SHA-256 b0b2858252d2a3bee205d40f97958da445ece0a3a4e05bd693340b2e94884257;

    S_LEAF_C5_124_ORDERED_ROOT_DOMAIN.md
    SHA-256 bfe1f2ddf5cb01be048d38d134c88668c3cc36f0c707806546132db53e1a1204.

I read both entire sources. I also read the complete actual-coordinate
arc proof in GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, the exact
physical-order and common-moment sections of
D_LEAF_BOUNDARY_ROOTS_CYCLE_EDGE_EXCLUSION.md, the degree-free
boundary-pair moment proof in FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md,
and the relevant full root threshold calculation in
FOUR_CYCLE_TILTED_S_ARTICULATION_EXCLUSION.md.

The 23/100 threshold was suggested in discussion; I independently
rederived the full square-coordinate argument, both weak-clearance
cases and every displayed estimate in the new proof. The ordered
high-coordinate source used by the caller is my own source, so
this review does not call my rechecking that source independent.
Its separate physical-screen audit is the hexagon review, and its
complete U>=1 scope extension was separately checked by rooted_blocks
in REVIEW_ORDERED_S_ROOT_HIGH_COORDINATE_EXTENDED_DOMAIN_ROOTED_BLOCKS_2026_10_27.md.

## 2. The complete actual-square arc cover

The actual sign/order changes of own axes preserve the original
origin and give E=[A,A+1] times [B,B+1], A>=B>=-1/2, with
the stated far-corner constraint and exact nearest-point distance.
No orientation is replaced by an aligned model in global coordinates.

For a>rho, A>h is correct, and the enlarged coordinate bounds
A<41/40, |B|<=1/2 imply the strict inner-corner inclusion.
At fixed q the expansion of
A^2+B^2+sqrt(2)AB in t=a+b is correct and convex. The full
fixed-q endpoint cover is precisely b=1/2 and a=b; those endpoints
need not satisfy the original a>rho condition because they are used
only to upper-bound the expression.

I rechecked both scalar endpoint calculations. At b=1/2 the enlarged
A interval begins at 1/5 and its larger convex endpoint value is
933/1600. At a=b, the first radius uses v<147/100 and the second
v<35/24. The stated reserves 1564/700000 and 557/201600 are
positive and exact. Consequently the inner-face inequality is
strict for both target inner circles.

The conversion of that inequality to alpha-beta>pi/4 has the correct
sign even when sqrt(2)A+B is negative. The relevant angle
beta+pi/4 lies in (0,pi/2). The other candidate interval length is
the full unit-strip difference, whose minimum is the centered strip.
Its endpoint b=rho is retained, and b>rho gives the stated strict
half-circle comparison. Thus the complete inner-face open interval,
not a selected subarc, has length greater than pi/4.

## 3. The weak-clearance outer-face cases

The B<=0 case is essential and is correctly included. Since A<=h,
the weak distance premise forces A=h and a=rho. All eligible circle
points with B<y<b lie on the positive-x branch with x>h. The
outer-side condition removes only the zero-angle point, when present.
The resulting one or two open pieces have exactly the full strip
measure. Their total measure remains strictly greater than pi/4;
connectedness and an interior radial-center point are not asserted.

For B>0 the comparison path at fixed k stays in 0<B<=A<=h,
including k=h and the infinite-derivative endpoint A=h by continuity.
I independently expanded the derivative comparison. Its squared
numerator is

    (A-B)[S^2-(2h+h^2)S+k^2(1+S)],       S=A+B,

which is exactly

    (A-B)[(S-h)^2+(k^2-h^2)(S+1)].

It is nonnegative in the whole stated domain. The minimum of the
outer-outer arc difference is therefore at A=B, and subsequently
at k=h. The final comparison with h=1/4 has the correct direction:
(1+h/sqrt(2))/(1+h) decreases in h. Its strict pi/4 reserve is
positive. The inner-inner and both strip comparisons retain every
side and corner endpoint.

These are all actual-square cases. In particular the proof does not
repeat the false inference that clearance 1/5 alone supplies a
connected 123/100 arc in the larger radius-Q disk.

## 4. Same-nine capacity and literal root consequences

An actual root containing the closed D_h forces every other closed
unit to have distance at least h; the proof handles a contact point
on its boundary by the open-neighborhood argument. All eight other
open unit interiors then contribute pairwise disjoint measurable
circle sets of measure greater than pi/4. Their sum exceeds 2pi.
This proves both full physical capacity statements without a stress
or physical-boundary assumption on any of those eight units.

The tilted-root corollaries are literal. U<=77/100 gives all four
actual own margins at least 23/100, while R^2<=17/4 and U<=4/5
give all four at least 1/5. The lower V bounds follow from the
unchanged d^2-U^2 identity and d>14/15. The weak equalities at the
shallow root side are included by the new measure proof.

## 5. Original S124 graph and exact moment transport

The full positive graph is 0-1-2-3-4-0 plus the genuine S leaf at 0.
The loaded set is exactly 1,2,4 and body 3 is its true unloaded
degree-two transmitter. All original units, applications, widths,
circle masks and forces remain. The source never calls 2-3-4 a
physical boundary edge.

The imported exterior-access argument is genuinely independent of
the D chart in its earlier source. It uses the actual selected cycle
embedding, real boundary spokes and real leaf access. Compact
interior strands and the original compatible weak-junction routing
preserve that order. No circle access is supplied to body 3.

The actual boundary edge 1-2 therefore supplies the strict positive
origin moment. At each original degree-two body, loaded or unloaded,
its actual torque transports the same moment. Radial corner forces
and the real leaf have zero origin moment. The resulting two root
moment signs and full three-force equation are exactly the displayed
ones. This is a valid full-cycle transfer, not a contraction.

For a tilted root, its real leaf point is unshareable by the explicit
tangent-sector argument. The convex normal order cut there gives the
precise lifts required by the complete ordered-root theorem. Both
actual root neighbors are physical boundary units. Thus the
high-coordinate join keeps every original degree and mask.

## 6. Exact remaining domain and complete root feature cover

After the two physical-capacity joins and the high-coordinate exit,
the surviving tilted range is exactly

    1<d<61/60,       77/100<U<=4/5,       3/5<V<2/3.

I checked each strict and weak endpoint directly from the original
radius identity. Its southwest root vertex is physically ineligible,
and the northeast point is the real unshareable leaf midpoint.
Parallel negative leaf-direction forces would act at that ineligible
southwest point; the positive leaf direction is likewise unavailable.

For the nonparallel pair, the actual lift order and full transverse
balance give opposite transverse signs. The first original moment
then gives q>0. The q>d exclusion is a complete normal-line feature
check: a point beyond both upper own coordinates cannot lie on an
own-side normal line, and the two mixed vertices have the wrong
normal cones. Only the ineligible southwest and unshareable northeast
vertices remain. Equality q=d is correctly retained.

The positive-transverse first normal is West or strict Northwest:
a North first force would require a strict Southwest last force by
the full root components. The negative-transverse last normal is
South or strict Southeast: an East last force cannot cancel the
strictly positive vertical leaf component and the nonnegative first
component. All displayed side means remain qV/d and qU/d, rather
than being moved to corners.

The first original boundary-point norm gives exactly U<=u_0, with
equality retained. The cited threshold proof is a radius-only
calculation and is not an isolated C4 equation. Finally U,V>1/2
makes the real leaf midpoint the unique farthest root point at
norm d. A physical two-circle-corner unit has all points of norm
at least d, so neither actual root neighbor can have that mask.
This is a physical-mask exclusion, independent of individual
corner weights.

The source correctly avoids assigning the first/last labels to a
particular loaded or unloaded successor. The actual reflection
changes load124 to load134, and the true location of the transmitter
stays explicit.

For an aligned root only d>=1 is joined to the complete existing
aligned-S3 theorem. The strict-low aligned family remains open
with its full equations. The source does not claim a fine-family
closure, alter shared metadata or suppress a remaining original case.

## 7. Verdict

Both full physical capacity theorems and the exact original S124
domain reduction pass. No mathematical correction was found.
The arc measure endpoints, all actual contact features, the entire
moment transport and every literal source join were checked.
The stated remaining domains remain obligations, and a separate
root review is still required.

