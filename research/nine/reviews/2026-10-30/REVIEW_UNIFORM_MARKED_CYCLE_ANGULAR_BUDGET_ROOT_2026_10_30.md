# Root review: the complete marked-cycle angular budget

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete theorem m+ell<=8 and all stated callers.**
I read the entire frozen source, reconstructed its geometric and graph
joins, and read its three named drawing/arc inputs in their current form.
This review includes the whole centered-arc proof, not just its statement.

## Frozen source and direct inputs

| Source | SHA256 |
| --- | --- |
| UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` |
| CENTERED_INNER_ARC.md | `fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5` |
| PLANAR_STRESS_CORE.md | `0cbdd5d2c6236e0a1407776963f71d64df4b822d20380a91cc1eabb14f2bbf26` |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |

The radius window remains 79/40<=R<=sqrt(1105/256). The theorem is not
presented as a new proof of that window or of every minimizer-to-stress
input. Its compatible physical embedding and all full-degree predicates
refer to one chosen certificate.

## 1. The marked-cycle statement has the necessary physical scope

Each mark is an actual square touching the containing circle; its degree
and its additional forces are unrestricted. Each run has one actual
signed supporting normal on all its consecutive contacts. This is a
geometric premise, supplied in the stress caller by translational
balance on every unmarked true unloaded degree-two body.

Tight support equations telescope to the exact endpoint projection
h_A+h_B+sum 2h_i. Since all halfwidths are at least one half, j internal
bodies give center distance at least j+1. The universal strict center
radius 91/60 excludes j>=3. Counting each run's initial mark and its
internals gives exactly m=k_0+2k_1+3k_2. No unrecorded force is discarded
at an endpoint or at a purported transmitter.

## 2. The complete centered forty-degree arc input is valid

For a circle-touching square, in its own-frame polar chart the exact
corner equation is r^2+r(s+c)+1/2=R^2. It gives
r<133/64-(s+c)/2 and r>5/4 throughout the stated window.
The triple-angle comparisons establish cos(pi/9)>15/16 and
sin(pi/9)<11/32 with the displayed strict rational reserves.

I checked both own-coordinate deviations for every point of the closed
radius-5/4 centered arc. The larger bound is F_1; the difference
(c-s)((s+c)/2-61/128) is nonnegative. The bounds
1-(3/5)s^2<=sqrt(1-s^2)<=1-s^2/2 have the required signs in the
resulting cubic lower bound for 1-2F_1.

Writing z=s-3/8 gives the exact cubic identity

    P(s)=219/40960+(17/2560)z+(483/640-(3/5)z)z^2.

On the full interval |z|<=3/8 its quadratic coefficient is positive,
and P(s)>=117/40960>0. Both own-coordinate deviations are therefore
strictly below one half, including the closed angular endpoints and
both extreme own-axis orientations. This puts the entire closed arc
in the actual open square. Overlapping centered arcs of two squares
would violate interior disjointness, proving strict separation greater
than forty degrees. A zero selected circle coefficient has no effect
on this physical fact.

## 3. The two order arguments use actual disjoint arcs

The proof correctly distinguishes circle-corner order from center order.
For a chosen physical circle corner z of a square with center c, set
n=c/|c| and P=(5/4)n. The arc theorem places P in the open square.
The farthest-corner formula gives

    z.n=|c|+(|c.u|+|c.v|)/(2|c|)>=|c|+1/2>7/4.

Consequently the segment from P to z has norm strictly greater than
5/4 after P, and norm strictly less than R before z. It is a proper
annular arc in the actual square. Such arcs from different squares
are disjoint. The proof that a containing-circle point has a unique
square owner is complete: both inward side coordinates of the radial
direction are strictly positive, so two owners would share nearby
interior radial points.

The annular-order lemma therefore transfers the center order on the
inner circle to the chosen physical corner order on the outer circle.
This avoids any unstated bound on the corner's angular displacement
from its center.

For the second order argument, the compatible center/contact drawing
can preserve the actual center-to-circle-corner spokes. A contact point
on the same ray would have to be the same square-boundary point as the
circle corner, which is impossible. Finitely many contact-junction disks
and strand tubes can be chosen disjoint from the spokes away from the
incident centers; their distinct local directions handle those centers.
Extra edges at marked vertices are retained in this construction.

The embedded selected cycle is a Jordan curve strictly inside the disk.
Its marked spokes go through its exterior to the outer circle without
meeting the curve again. Applying annular order a second time transfers
the original marked cycle order to the physical center order. The
successive positive angular gaps therefore sum to exactly 2*pi.
The proof includes two marks with complementary angular gaps. It does
not assume the origin is inside the embedded cycle, identify a winding
from a few local inequalities, or invoke a loaded force polygon.

## 4. The eighty- and one-hundred-sixty-degree estimates are exact

For a singleton run, endpoint distance is at least two. If its minor
center angle were at most eighty degrees, then cos(theta)>1/6. The
triple-angle polynomial at 1/6 is 13/27<1/2, proving this exact sine
comparison. The center-distance quadratic is separately convex on the
closed radius rectangle [0,M]^2; its maximum is (5/3)M^2. This is
41405/10800<4, with reserve 359/2160. Thus the minor angle exceeds
eighty degrees.

For a long run, endpoint distance is at least three. The triple-angle
polynomial at 19/20 is 1159/2000>1/2, so cos(twenty degrees)<19/20.
An endpoint angle at most one hundred sixty degrees would therefore
give squared distance below (39/10)M^2=107653/12000<9, with reserve
347/12000. Thus this minor angle exceeds one hundred sixty degrees.

Each consecutive marked gap is at least its endpoint minor angle,
even if it is the major arc. This is the correct direction for using
these estimates in the physical angular sum. No discrete transmitter
width or angular-stationarity equation appears.

## 5. The single budget and all complete-family consequences

The strict per-run bounds are forty, eighty and one hundred sixty
degrees for zero, one and two internals. Their sum gives

    360>40(k_0+2k_1+4k_2)=40(m+k_2).

Integrality gives m+ell<=8. This proves all nine-body marked-cycle
exclusions at once, every eight-body marked-cycle exclusion with a
long run, and the one-long-run bound for seven bodies. There is no
separate enumeration whose omitted cyclic placement could escape.

For an entire simple positive component the source proves that at
least two positive-circle-weight bodies exist. Summing center-dotted
force equations gives a positive tight-support sum, so some circle
weight is positive. Summing the force equations gives zero total
circle resultant, which cannot be supported on only one boundary
body because all its actual circle corners have positive dot product
with its nonzero center. Marking the positive-load bodies is therefore
valid, and all remaining cycle vertices are truly unloaded degree two.

The broader caller marks every physical boundary vertex on a cycle.
If every circle-clear vertex has full true degree two, it is unloaded
and transmits as required. Zero or one mark would give a closed
positive-width normal telescoping path, which is impossible. Thus every
nine-body cycle that survives this theorem must have a circle-clear
vertex with an additional positive edge beyond its cycle edges.
Extra chords and attachments at marked boundary vertices are fully
allowed. Chords at a circle-clear vertex are not silently removed.

For eight-body four-load simple components, all placements of (2,2,0,0)
and (2,1,1,0) are excluded; only (1,1,1,1) remains beyond this source.
Every nine-body simple component is excluded for every load count.
The seven-body record pattern (2,0,1,0) satisfies m+ell=8 and survives,
as it must. No coarse parent is incorrectly identified with its simple
cycle portion.

## 6. Same-certificate compatibility and verification limits

I read PLANAR_STRESS_CORE.md, including its normal selection, force-only
uncrossing, physical local drawing, circle spokes and sparsification.
The drawing is genuinely compatible with actual square sectors. The
new angular theorem uses precisely the translational quantities that
this construction retains; it makes no claim that torque survives.
Degrees and unloaded status are correctly read after uncrossing and
thinning. PHYSICAL_BODY_GRAPH_UNCROSSING.md supplies an alternative
compatible physical drawing for a force-and-torque certificate. These
two certificates are not identified.

The new theorem therefore does not require the unresolved joint
force-polygon/selection audit. This does not close that audit for other
manuscripts, the remaining chorded and smaller-component families,
their completion obligations, equality classification or unrestricted
nine-square optimality. All rational identities were checked exactly;
no Lean compilation, CI, pose search or mesh was used.
