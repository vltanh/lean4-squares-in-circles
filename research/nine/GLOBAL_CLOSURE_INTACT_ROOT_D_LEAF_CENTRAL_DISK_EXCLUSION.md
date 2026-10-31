# An intact triangle root with a D leaf isolates the central disk

Date: October 26, 2026.

**Status: accepted after full root and independent rooted-blocks review.**
See `REVIEW_INTACT_ROOT_D_LEAF_CENTRAL_DISK_ROOT_2026_10_26.md` and
`REVIEW_INTACT_ROOT_D_LEAF_CENTRAL_DISK_ROOTED_BLOCKS_2026_10_26.md`, both
of which pin the unchanged mathematical source before this acceptance-only
status edit. No ledger is changed.

Keep all original physical squares, the common compatible selected
certificate, and

    79/40<=R<=sqrt(1105)/16,
    r=R-sqrt(2), s=1-r,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

The accepted bounds give

    67/120<r<7/10,       3/10<s<53/120.                 (1)

An intact petal at H is an actual positive triangle H,T1,T2 whose
tips have true degree two and positive circle loads. H keeps its full
original degree and every other force.

## 1. A radius-free contact-triangle barrier on a common side

Let H,T1,T2 be three pairwise interior-disjoint actual unit squares
with pairwise physical contacts. Suppose two chosen actual H-to-tip
contacts lie on the same H side at

    P_-=(P,y_-), P_+=(P,y_+),       y_-<0<y_+.

Assume H lies to the left of this side, and let W be a distinct actual
unit, interior-disjoint from all three, such that

    p=(P,0) in W,        W subset {x>=P}.                 (2)

**Barrier lemma.** These conditions are impossible.

Choose any actual common point Q of T1,T2. The two segments from Q
to P_-,P_+ lie in the corresponding actual convex tips. If Q_x<P,
one such segment immediately enters H's open interior: use the lower
port when Q_y>=0 and the upper port when Q_y<=0. This gives physical
overlap, including when a port is a side endpoint.

If Q_x=P and Q_y!=0, one of those segments has p in its relative
interior. That tip must occupy the right local half-plane beside H
at p, and consequently overlaps W near p. If Q=p, the three distinct
units T1,T2,W all contain p on the right side of H. Their tangent cones
each have angle at least pi/2 and cannot be interior-disjoint in one
semicircle. Thus every collinear or coincident case is excluded.

Otherwise Q_x>P. The triangle with vertices P_-,P_+,Q has its entire
boundary in the three closed actual units. Some interior points of W
near p lie inside it, because p is in the relative interior of its
base. Convexity of the open interior of W and avoidance of the whole
occupied boundary force every W interior point inside. The triangle's
base has length at most one, and its height at most sqrt(2), since
Q and each base endpoint belong to one unit. Its area is at most
sqrt(2)/2<1, contrary to area(W)=1.

This is the complete physical contact-enclosure argument already used
in Sections 5--6 of
`GLOBAL_CLOSURE_LONG_ARM_AND_DIRECT_LEAF_TRIANGLE_EXCLUSION.md`, with
its geometric hypotheses stated separately. It uses no force equation
or radius assumption. Both p and Q may be genuine side means or their
endpoints; no normal is chosen anew.

## 2. An intact petal and a genuine D leaf force strict central-disk containment

Suppose H has an intact petal and also a genuine direct D leaf L.
Rotate its actual leaf direction east. The true radial leaf geometry is

    H=[-s,r] times [l,l+1],       -1<l<0,
    p_L=(r,0),                  L subset {x>=r}.         (3)

The application lies in an H side interior by the original nonradial
point-only vertex/vertex convention. Keep all other H forces.

The accepted end-triangle origin theorem gives O in the open interior
of H, and the actual common petal side has height P<39/40 and two ports
whose transverse coordinates strictly straddle zero. One such coordinate
has magnitude at most 1/2. Since its boundary-tip port has norm >67/120,

    P^2>(67/120)^2-1/4=889/14400>1/25.

Therefore every actual common petal side has

    1/5<P<39/40.                                        (4)

**Central-disk theorem.** The entire closed disk D_epsilon belongs to
the open interior of H.

For epsilon=0 this is already the origin theorem. Suppose epsilon>0.
Both horizontal margins in (3) exceed epsilon by (1). If the conclusion
failed, at least one transverse margin would be at most epsilon.
Reflect vertically to put the upper margin at

    eta=l+1,             0<eta<=epsilon,
    H=[-s,r] times [eta-1,eta].                          (5)

There are exactly four actual sides which could be the common petal
side. We exclude each, retaining its actual applications.

The top side has height eta<=epsilon<1/5, contrary to (4). The bottom
side has height 1-eta>=1-epsilon>59/60>39/40, also contrary to (4).

The right side is the D-leaf side. Its actual petal ports straddle
p_L=(r,0). The genuine distinct leaf L satisfies (2), so the barrier
lemma excludes this entire common-side alternative, including all
owned-side means and their endpoints.

On the left side, with height s, one petal port has positive vertical
coordinate y satisfying 0<y<=eta<=epsilon. That actual point belongs
to a physical boundary tip. But

    |p|^2=s^2+y^2<=s^2+epsilon^2<r^2,

because

    r^2-s^2=2r-1>7/60>epsilon^2.                       (6)

Every point of a boundary unit has norm at least r=R-sqrt(2), by its
diameter. This is a contradiction. The four side alternatives are
exhaustive, so no small transverse margin exists. Both transverse
margins, as well as both horizontal margins, are strictly greater than
epsilon. This proves the closed-disk containment in H's open interior.

The conclusion retains the D leaf's original force and any other
positive forces at H. It does not replace the D leaf by an artificial
radial load or assume that the common petal face is its leaf face.

## 3. Other leaf roots and bridge-only internal bodies are impossible

Every genuine leaf root K meets D_epsilon. For a D leaf this follows
from O in its root's open interior. For an S leaf with application d v,
the inward unit segment gives epsilon v in K when d>1, and gives O in
K when d<=1. These are the full orientation-uniform radial leaf facts.

By Section 2, every point of D_epsilon lies in H's open interior. No
distinct actual unit can even meet that closed disk without overlapping
H. Therefore

    every genuine leaf root is H.                       (7)

Now use the common minimum-support selected scope and named small-core
joins of `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`. Every loaded
bridge-only body is a genuine leaf. A positive unloaded bridge-only
body U must avoid O, since H contains O openly. The complete off-origin
transmitter theorem then gives an actual incoming application of norm
in (0,epsilon], belonging to U. This is impossible by strict central-
disk containment. Consequently

    there is no bridge-only internal body.              (8)

These conclusions concern every original positive branch, not merely
the branches chosen for a smaller diagram.

## 4. Complete exclusion for any all-triangle cyclic block tree

Assume the entire selected positive component has only triangles as its
cyclic blocks, arbitrary bridges, at most nine bodies, and contains an
intact petal at H together with the genuine D leaf in (3). All actual
physical squares and all original forces remain.

By (7)--(8), every genuine leaf bridge is attached directly at H, and
there is no bridge-only internal vertex. Use the exact block-cut tree,
treating each bridge as a two-vertex block, and root this tree at H.

Every terminal triangle block has two vertices which belong to no other
block. They have their true degree two and are loaded by the touching-
neighbor obstruction. It is therefore an intact petal, whose root must
be H: the end-triangle origin theorem would otherwise put O in the open
interiors of two distinct actual units.

There can be no block or articulation at distance at least two from H.
Indeed a farthest descendant branch has a terminal block. If it is a
triangle, its root is not H, contradicting the preceding paragraph.
If it is a bridge, its private endpoint is a genuine leaf and its root
is not H, contradicting (7). A terminal bridge cannot end in an
unstressed isolated extra: every vertex in this block-cut tree belongs
to the positive component, and a true degree-one positive body is a
loaded genuine leaf. Thus the argument exhausts every terminal type.

Consequently all triangle blocks and all leaf bridges meet directly
at H. H is physically circle-clear, and its full force equation is

    sum_j M_j + sum_i alpha_i v_i=0,                     (9)

where every M_j is a true intact-petal resultant and every alpha_i v_i
comes from a genuine direct leaf. The complete end-triangle pressure
gives c_H.M_j>0. Direct leaves also have positive center pressure:
an S leaf gives c_H.v_i=d-H_H(v_i)>=d-1/sqrt(2)>0, while a D leaf gives
c_H.v_i=r-1/2>0. Taking scalar product of (9) with c_H contradicts its
strictly positive left side.

**Whole-family conclusion.** No selected all-triangle cyclic block tree
with arbitrary bridge forests can contain an intact-petal root which
also carries a genuine D leaf.

For the C2.33 bridge inventory this covers both shared-hub and separated-
triangle layouts, with every attachment retained. It does not cover an
S leaf at that root, or a graph with no intact petal. Those remain part
of the original full coarse obligations. A terminal cyclic block of
size four or more is also outside the graph theorem in Section 4; no
intact-triangle pressure is assigned to it.

No circle force, actual mean, original normal or physical square is
changed. No numerical pose, Lean compilation, CI, remote action, or
shared-ledger edit is used.
