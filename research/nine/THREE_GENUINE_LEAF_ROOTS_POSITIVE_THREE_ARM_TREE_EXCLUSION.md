# Three genuine leaf roots cannot be the ends of a positive three-arm tree

Date: October 27, 2026.

**Status: accepted complete uniform physical theorem and three whole
original C2.34.b3 attachment exits after full root and separate independent
reviews.** See REVIEW_THREE_GENUINE_ROOTS_POSITIVE_TREE_ROOT_2026_10_27.md
and REVIEW_THREE_GENUINE_ROOTS_POSITIVE_TREE_LEAF_PAIR_2026_10_27.md.
Both pin the complete mathematical source before this acceptance-only
header. No original gate, coarse-cell count, or shared ledger is changed.

Keep all nine original physical unit squares, the common compatible
selected positive graph, and

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Let R_1,R_2,R_3 be three distinct actual genuine leaf roots, each
of true positive degree at least two, with its distinct actual leaf
L_i. Suppose the original positive graph contains a tree consisting
of three positive paths

    V ... R_1,       V ... R_2,       V ... R_3,          (1)

whose only common vertex is V. The three roots are the three ends
of this tree: no R_i occurs inside another path, and V is different
from all three roots. No genuine L_i is a tree vertex. All other
tree vertices, all original forces, and every root's additional
positive edges remain unrestricted. Extra positive edges between
the R_i, including contacts inside the small central disk, are allowed.

**Theorem.** This entire original configuration is impossible.

Only a subgraph is used for the topological contradiction. No force
or true degree is deleted from the physical certificate. The proof
does not promise an embedding of every omitted root-to-root edge
through the auxiliary disk; none is needed.

## 1. The three actual roots are high S and every other square avoids the disk

THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md applies at the actual
arbitrary root degrees. Its complete D, low-radius and critical
capacity cover gives

    1<d<61/60,       epsilon=d-1>0,
    all three genuine leaves are S.                    (2)

Write e_i for L_i's original outward radial direction. Its real
contact is d*e_i and its occupied square is

    L_i=[d,d+1]e_i+[-1/2,1/2]Je_i.

The original root contains its whole inward radial unit segment

    [epsilon*e_i,d*e_i] subset R_i.                    (3)

In particular each R_i meets the closed disk D=D_epsilon.

FOUR_NEAR_ORIGIN_UNITS_NINE_CAPACITY_EXCLUSION.md says that a fourth
actual unit meeting D would make at most eight units possible: all
four then meet D_(1/60). Therefore

    every actual unit other than R_1,R_2,R_3
    is disjoint from closed D.                         (4)

This includes V, every internal vertex of (1), all three genuine
leaves, and every other original physical square. Since the units
are compact, each has positive distance from D. The full nine-square
hypothesis is retained in this step; no unused completion unit is
removed.

Each root center is outside D. Indeed its genuine point d*e_i is
at distance at most 1/sqrt(2) from its actual center c_i, so

    |c_i|>=d-1/sqrt(2)>epsilon.

Every kept tree application incident to R_i belongs also to a
different tree body, which is outside D by (4). The real leaf
application d*e_i is outside D as well. Thus all applications used
at the roots in the retained tree and leaf edges are strictly
outside D, including their original shared-side mean endpoints.

## 2. Exact clipped-root connectivity and accessible distinct disk ports

The genuine-S clipping result in Sections 2--3 of
THREE_GENUINE_LEAF_ROOTS_NO_COMMON_NEIGHBOR.md gives

    Omega_i=int R_i minus D is path connected.          (5)

That local result needs the actual genuine S support, not a root
degree or a common-neighbor premise. Its full side/vertex and disk-
tangency proof is retained. Briefly, a disk of diameter below one
cannot meet opposite sides. A disconnected square-boundary cut would
require two adjacent side intersections with their common corner
excluded, forcing an actual chart [-a,1-a] times [-b,1-b] with
0<a,b<=epsilon. All near support sides and three near vertices have
radial support below d, while the last vertex has norm squared at
least 2(1-epsilon)^2>d^2. That chart cannot be a genuine S root.
The connected boundary complement and inward perturbations of its
compact arcs give (5), including all exact disk tangencies.

Use the actual disk port

    q_i=epsilon*e_i.

It is accessible from Omega_i even when (3) lies on an actual root
side. Here is an explicit endpoint justification. For sufficiently
small t>0, p(t)=(epsilon+t)*e_i belongs to the segment (3).
The convex combination

    gamma_i(t)=(1-t^2)p(t)+t^2*c_i

lies in int R_i. Its norm is at least

    epsilon+t-t^2*|c_i-p(t)|>epsilon

for sufficiently small t. Hence gamma_i(t) is in Omega_i and tends
to q_i as t decreases to zero. It can be joined to c_i within
Omega_i by (5). This proves actual outside access at a tangency
or corner without assuming q_i is interior to the root.

The three q_i are distinct. Otherwise two e_i would agree, and
their two distinct genuine radial S leaves would have exactly the
same occupied square in (2)--(3), impossible. Also epsilon>0 makes
every q_i different from O; the epsilon=0 alternative has already
been excluded by the complete original high-S reduction.

No q_i is an application of a retained original tree or leaf edge,
by Section 1. A q_i may be a physical zero-stress contact with
another root; that other root's retained paths do not end there.

## 3. One auxiliary plane drawing of the retained tree and all three genuine leaves

First restrict the drawing, only topologically, to the actual
positive tree (1) and the three actual positive leaf edges R_i-L_i.
All their original applications and the common selected compatible
contact routing are retained. Extra positive edges remain in every
original force equation but need not appear in this proof drawing.

In particular a positive edge between two of the near roots may
have its original application inside D. Such an edge is omitted
from this topological subgraph, not altered, moved, or deleted
from the certificate. The argument imposes no disk-clearance
hypothesis on an omitted application.

For every internal tree body use its usual actual center/contact
star. Its entire square avoids D by (4). At R_i join its actual
center to its kept tree application and its genuine leaf application
through the connected open Omega_i. Add a third half-edge through
Omega_i approaching q_i as in Section 2. A finite three-pronged
tree with these ends and branch point c_i can be chosen without
self-crossing in that connected open region. One can first take
a simple finite tree through the ends, then move its finite branch
points along its edges to the designated center and separate the
parallel strands inside small open tubes. At each actual old port
the final approach stays within the original root sector.

If the two kept old applications at R_i coincide, their inherited
compatible ordering is maintained in parallel strands to that old
junction, exactly as in PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section 5.
The new disk port is distinct from that junction. With distinct old
ports, their two cyclic positions at the root are retained. No
additional prescribed root order is needed for a three-pronged star.

All weak old junctions are routed by restricting the original
compatible selected junction drawings to the kept positive edges.
That includes a possible multiway contact between different paths.
Changing an interior route inside a root does not change the physical
sector order at its old junctions. The other retained strands lie in
different actual square interiors, which are disjoint.

Now add the auxiliary disk vertex O and three edges O-q_i-R_i.
Their O-to-q_i portions are the three distinct radial segments in D,
meeting only at O. All retained old paths avoid D. The three outside
root portions are in the corresponding disjoint Omega_i. Small
neighborhoods of the three distinct q_i can be chosen disjoint from
all retained old compact paths and from the other two disk ports.
Each new junction has just its one disk edge and its one root
half-edge. Even if another physical root contains q_i, none of its
retained paths uses q_i; those paths lie in its open clipped region
and have their own distinct endpoint q_j. Thus the new local routing
has no unresolved opposite-pair or interlacing matching.

We obtain a plane embedding of the retained actual tree, all three
genuine leaf edges, and the three auxiliary disk edges. The auxiliary
edges have no positive force, selected normal, or physical degree.
The original full certificate has not been replaced by a certificate
on this drawing.

## 4. Each genuine physical boundary leaf retains protected exterior access

For each actual L_i choose one of its physical circle corners z_i.
The center-to-z_i spoke lies in int L_i except for its circle end,
and it can be continued radially outside the containing circle to
infinity. A containing-circle point cannot belong to two physical
units, as proved in PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section 6.
The old genuine leaf application is not z_i, so its center/contact
strand and this spoke meet only at the leaf center.

All new disk portions are a positive distance from the closed L_i
by (4). All root portions lie in actual different root interiors,
and the kept internal-body paths lie in their respective original
units. Thus the compact leaf spokes have positive clearance from
every nonincident path. The retained physical weak-junction disks
and parallel strand tubes can be chosen small enough to preserve
all three spokes simultaneously, precisely as in the full original
exterior-face construction. The new root/disk junctions lie strictly
inside the containing disk and do not affect these spokes.

Consequently each L_i is incident to the unbounded face of this
single augmented embedding. This conclusion needs only actual
physical circle contact, not a positive multiplier at the chosen
individual corner. No original leaf body is identified with a
theta-path body; they are distinct by the stated original graph
roles and genuine degree-one hypotheses.

## 5. The three possible inner paths all trap a real boundary leaf

The three paths (1), extended by R_i-O, form three internally
vertex-disjoint paths between V and O. The augmented subgraph is
a subdivision of K2,3. Its unbounded face is bounded by two of
these paths. The third path has all its internal vertices strictly
inside that simple outer cycle; in particular its genuine root
R_i is strictly inside.

The actual L_i is not a vertex of that outer cycle. Its unchanged
positive edge R_i-L_i is present in the same plane embedding and
cannot cross the cycle. Hence L_i lies strictly inside it as well.
This contradicts the protected access of that physical boundary
leaf to infinity.

This works for each of the three possible inner paths. It does
not require any internal tree body to be physically boundary, and
it does not require any private load mask. All placements are
excluded, proving the uniform theorem.

## 6. Three complete C2.34.b3 shared-root attachment exits

Use the exact labels in
TRIANGLE_FOUR_BLOCK_THREE_BRIDGES_COMPLETE_ATTACHMENT_REMAINDER.md.
Every row below has its three distinct genuine roots and all nine
original component units. The common high-S reduction is part of
the theorem, so the full original S/D and radius domains are covered.

| Original graph domain | Root triple | Original positive three-arm tree |
| --- | --- | --- |
| C4 with direct leaves ABK | A,B,K | H-A; H-B; H-P-K |
| C4 with direct leaves AKP | A,K,P | H-A; H-P; H-Q-K |
| Page-rooted diamond with direct leaves AKP | A,K,P | H-A; H-P; H-Q-K |

The center V of (1) is the actual H, different from the three named
roots. In the first row the original AB edge is not a tree edge;
its application may be inside D and is left entirely unrestricted.
In the last two rows the original KP edge is likewise omitted only
from the topological tree. The page-diamond PQ chord and every
other original cyclic edge remain in the force system as well.

For ABK C4, the original degrees are A3,B3,K3,H4,P2,Q2 and the
three genuine leaves degree one. P need not be loaded: its whole
original square avoids D by the four-near capacity theorem, and
the inner-path contradiction uses K's real boundary leaf. No
degree-two boundary equation is imposed on either A or B.

For AKP C4, the original degrees are A3,K3,P3,H4,B2,Q2 and three
degree-one leaves. Q need not be loaded. The actual positive tree
still has its distinct H-to-K path through that real Q.

For AKP page diamond, the original degrees are A3,K3,P4,H4,B2,Q3
and the same three genuine leaf degrees. P keeps every one of its
four positive forces, Q keeps its full degree three, and the
positive hub chord PQ is retained in every equation. The clipped
root theorem requires no smaller equation at the degree-four P.

All three named leaf bodies lie outside their respective actual
trees, as their genuine degree-one identities require. Thus the
uniform theorem excludes each entire original graph domain,
including every private four-block load, original force ratio,
shared-side mean, normal owner and individual zero circle weight.

After full acceptance these are exactly three exits from the current
thirteen-domain b3 remainder, giving ten. The hub-diamond ABK/AKP
and page-diamond ABK domains were already excluded by other complete
theorems and are not counted again. No AHP, shared arm, disjoint
domain, or whole coarse cell is claimed closed here.

No actual physical unit, original force, selected normal, side mean,
circle atom or pose is changed. No numerical packet, additional
selection, Lean compilation, CI, remote action, or shared-ledger
mutation is used.
