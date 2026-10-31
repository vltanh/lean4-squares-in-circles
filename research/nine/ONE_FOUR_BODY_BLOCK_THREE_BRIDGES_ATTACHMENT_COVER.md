# Exact one-four-block / three-bridge cover: seventeen complete exits and seven remaining placements

Date: October 27, 2026.

**Status: complete proposed graph cover and original-source join, frozen
for full root and separate independent review. C1.4.b3 remains OPEN.**
The numbering in the tables is only a finite graph inventory, not new
roadmap IDs or a new parameter subdivision. No original gate or ledger
has been changed.

Keep all nine original physical unit squares, the common canonical
radius/Phi-minimizing pose and compatible selected certificate, with
minimum positive support counted on the original scalar atoms before
shared-side aggregation. Work in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

The actual positive component has one four-body biconnected block and
exactly three bridge blocks. The block identity gives seven distinct
positive bodies. The other two original physical units remain arbitrary
and present. All actual force degrees, original circle masks, individual
zero weights, applications, means, selected normals and extra physical
zero-stress contacts remain.

## 1. Exact original block and forest cover

Every simple biconnected graph on four vertices is a C4, a diamond or
K4. NO_POSITIVE_K4_SUBGRAPH.md excludes the selected K4, retaining
arbitrary further root forces. The remaining block labels are:

    C4: A--B--C--D--A;
    diamond: hubs H,K, tips B,C, edges HK,HB,HC,KB,KC.

The complement of the block consists of trees, each joined to the
block at exactly one root. A second block attachment would create
another cycle and contradict the stipulated bridge status. The
three actual bridge edges add exactly three distinct outside bodies.

GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md supplies the exact
branch inequality k+ell<=3. A block-root articulation already has
one branch containing the remaining block. It therefore has at most
two outside tree branches. At an outside all-bridge vertex, every
incident edge is a separate branch, so its degree is at most three.
Every outside nonleaf is genuinely unloaded in this same canonical
minimum-atom certificate. These are statements about the unchanged
actual graph; no selected force is deleted for the cover.

The possible forest partitions are consequently exactly:

| Bridge partition | Actual forest shape | C4 orbits | Diamond orbits |
| --- | --- | ---: | ---: |
| 1+1+1 | Three direct leaves, with at most two at one block root | 3 | 6 |
| 2+1 | A genuine two-edge arm and one direct leaf at a block root | 3 | 6 |
| 3 | One three-edge path or one degree-three fork outside the block | 2 | 4 |
| Total |  | 8 | 16 |

For three direct leaves the allowed multiplicities are (2,1,0,0)
and (1,1,1,0). Three leaves at one root would give four components
after deleting that root, contradicting k+ell<=3. This removes one
C4 and two diamond root orbits before the displayed 24-orbit cover.
Those removed placements also have independent same-root bouquet
exits; they are not counted as new exits in the table.

For 2+1, the two-edge tree is necessarily a path. Its root and the
direct-leaf root are an ordered pair because the arm and leaf are
different actual trees. C4 gives same, adjacent and opposite roots.
A diamond gives three choices for a hub arm root (same hub, other
hub, tip) and three for a tip arm root (same tip, other tip, hub).
No reflection identifies the two hub/tip orders.

For one three-edge tree, the block root has one outside neighbor.
The outside shape is either a path R--U--V--L or a fork with edges
R--U,U--L,U--M. There is one C4 root orbit and two diamond root
orbits for each shape. A fork at the block root belongs to 2+1;
three children at one outside vertex would need four bridge edges.
This proves that every original forest is in exactly one row below.

## 2. Complete repeated-root direct-leaf exits

The full recovered source
TWO_GENUINE_LEAVES_AT_ONE_ROOT_AND_A_DISTINCT_GENUINE_ROOT_EXCLUSION.md
has frozen SHA256

    c810d66cb1babc60dc759364692ca5ba8ef4cdfa78875c56d859ae7a58fc9783.

It keeps two genuine leaves at an actual root A and a genuine leaf
at a distinct actual root K, with arbitrary other forces and degrees
at both roots and no assumption of a positive A--K edge. Its full
noncritical central-disk overlap proof and critical P/Y/sector-capacity
and full unchanged K torque proof exclude every genuine S/D choice,
all original angular and side endpoints, and every nine-square
completion. In particular the critical reflex sector is not omitted:
the full K equation supplies a fourth actual radial square, whose
physical shape follows from sharp support equality without a new
degree-one equation.

This full source is freshly recovered for the present publication;
its complete original-domain review is required before acceptance.
It supplies the following six whole graph exits, without using an
older two-leaf theorem at a newly increased root degree.

| Row | Original direct leaves | True block degrees in the displayed order | Full source exit |
| --- | --- | --- | --- |
| 1 | C4: two at A, one at B | A4,B3,C2,D2 | Repeated-root theorem |
| 2 | C4: two at A, one at C | A4,B2,C3,D2 | Repeated-root theorem |
| 3 | Diamond: two at H, one at K | H5,K4,B2,C2 | Repeated-root theorem |
| 4 | Diamond: two at H, one at B | H5,K3,B3,C2 | Repeated-root theorem |
| 5 | Diamond: two at B, one at C | H3,K3,B4,C3 | Repeated-root theorem |
| 6 | Diamond: two at B, one at H | H4,K3,B4,C2 | Repeated-root theorem |

All three actual leaf bodies in each row have degree one. The
original seven positive bodies and both completion units are kept.

## 3. The complete three-distinct-root cover and its one whole exit

There is one C4 orbit of three marked vertices. For a diamond the
unmarked vertex is a hub or a tip, giving exactly two orbits.

| Row | Original direct leaves | True block degrees | Status |
| --- | --- | --- | --- |
| 7 | C4: at A,B,C | A3,B3,C3,D2 | OPEN |
| 8 | Diamond: at H,B,C | H4,K3,B3,C3 | Complete positive-three-arm-tree exit |
| 9 | Diamond: at H,K,B | H4,K4,B3,C2 | OPEN |

For row 8 apply the full accepted
THREE_GENUINE_LEAF_ROOTS_POSITIVE_THREE_ARM_TREE_EXCLUSION.md.
The three genuine leaf roots are H,B,C, the actual tree center is K,
and its three original positive arms are K--H,K--B,K--C. Their only
common vertex is K; no marked root is internal to another path, and
none of the genuine leaves is on the tree. Every additional positive
edge HB and HC remains in the original force system. The theorem
requires no smaller equation at decorated H4, B3 or C3 and covers
all original leaf types and radii through its full high-S reduction.

The fresh force-free
BOUNDARY_UNIT_THREE_NEAR_NEIGHBORS_FRESH_EXCLUSION.md supplies a
separate complete exit for this same row: actual K3 is loaded by
NO_UNLOADED_DIAMOND_HUB.md, whereas all three actual genuine roots
H,B,C meet D_(1/60). Its three actual contacts contradict the complete
closed-lens diameter proof. The positive-tree exit is sufficient
here and does not depend on that fresh alternative being accepted.

For rows 7 and 9 the complete
THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md gives the necessary
original restriction

    d>1 and all three genuine leaves are S.              (1)

No low or critical endpoint, or genuine D choice, is left implicit
by that reduction. Each true root meets the same closed D_epsilon.
In row 7, D must be loaded: if its true D2 were unloaded, its actual
normal channel would separate the near endpoints A,C by width w>=1.
Writing its support levels h,h+w, the actual near points give

    h>=-epsilon, h+w<=epsilon, w<=2epsilon<1,

which is impossible. In row 9 the true C2 must be loaded because
its actual neighbors H,K touch. Thus each remaining direct-leaf
placement has its single unmarked block body genuinely loaded.
These are necessary restrictions, not a proof of either whole row.

## 4. Every same-root short-arm/direct-leaf placement has a whole exit

Write a genuine short arm at R as R--X--L and its direct leaf as
R--E. The new complete source
FOUR_BODY_BLOCK_SHORT_ARM_AND_SAME_ROOT_LEAF_EXCLUSION.md gives
the exact all-radius join at the original degrees below.

| Row | Actual roots of arm and direct leaf | True block degrees | Status |
| --- | --- | --- | --- |
| 10 | C4: both at A | A4,B2,C2,D2 | Complete same-root arm/leaf exit |
| 11 | Diamond: both at H | H5,K3,B2,C2 | Complete same-root arm/leaf exit |
| 12 | Diamond: both at B | H3,K3,B4,C2 | Complete private boundary-triangle exit; also joined in the same-root source |

The source first uses the full terminal-four closed-origin theorem
to force the genuine X off the closed origin. The actual off-origin
bridge theorem gives an S/side arm at d>1, its unchanged application
epsilon e, and O in closed R. The separate real direct leaf rules
out every boundary-origin R chart. Its actual arm application is then
on a real epsilon-shallow own face of the open-origin R, with norm
epsilon<3/8, and R--X--L is an original path to the circle.

Every C4 mask is explicitly covered. In particular the source proves
the sole-opposite mask geometrically from the real two-channel chart
and the two distinct actual leaves. It does not add an atom/body
tie-break selector. Only the already proved all-three C4 or hub
diamond remains for the complete shallow-strip/path/circle-order
negative-moment contradiction, with the full private diamond hub
degree three retained. The tip-rooted row has its original three
private loaded-body boundary triangle.

X remains true degree two, both genuine leaves degree one, and R
keeps its degree four or five. These new complete joins retain their
separate original-source and parent-review gates before acceptance.

## 5. The complete distinct-root short-arm/direct-leaf cover

The arm is R--X--L and the direct leaf is S--E with R!=S. The
ordered-root orbits and their unchanged block degrees are exactly:

| Row | Actual arm root / direct-leaf root | True block degrees | Status |
| --- | --- | --- | --- |
| 13 | C4: A / B | A3,B3,C2,D2 | OPEN |
| 14 | C4: A / C | A3,B2,C3,D2 | OPEN |
| 15 | Diamond: H / K | H4,K4,B2,C2 | OPEN |
| 16 | Diamond: H / B | H4,K3,B3,C2 | OPEN |
| 17 | Diamond: B / H | H4,K3,B3,C2 | OPEN; different ordered forest from row 16 |
| 18 | Diamond: B / C | H3,K3,B3,C3 | Complete boundary-edge/common-neighbor exit |

In row 18 the actual H and K retain true degree three and are
loaded by NO_UNLOADED_DIAMOND_HUB.md. Thus HK is an actual positive
boundary-to-boundary edge with two distinct actual common neighbors
B,C. BOUNDARY_EDGE_OUTER_FACE_AND_DIAMOND_EXCLUSION.md excludes that
complete physical configuration independently of the increased B/C
degrees, their arm/leaf forces, masks, actual means or circle weights.
Neither arm root B nor leaf root C is assigned a true degree-two
equation. The extra arm body X is kept at its actual degree two.

There is also a degree-free necessary restriction in every remaining
distinct-root row: its direct genuine leaf E must be S. If E were D,
the actual S-root contains O openly. If O belongs to the closed X,
the two actual units overlap. Otherwise the complete off-origin
bridge-transmitter theorem supplies an incoming neighbor of X
containing O. Its boundary leaf L cannot be that incoming neighbor,
so it is the distinct block root R. This also overlaps int(S).
Every possibility is covered; no original force is removed.

This restriction alone does not close an original arm width, radius
interval or graph placement. A putative D or diagonal arm puts its
actual X at O and must be checked against the remaining genuine S
root by the full physical equations; a high S/side arm has a distinct
near R, X and S and must retain all three. Those domains are not
declared impossible by the two-bridge source.

## 6. Every single three-edge outside tree is excluded

For both tree shapes every private block body has exactly its
unchanged block degree. Thus the entire block is a terminal block
at its actual attachment root R, in the precise scope of
ROOTED_TERMINAL_FOUR_BLOCK_CLOSED_ORIGIN_EXCLUSION.md. We prove an
actual closed-origin outside unit separately for each shape.

### 6.1. The three-edge path R--U--V--L

The actual U,V are all-bridge nonleaves and hence genuinely unloaded
in the selected canonical certificate. Their true degrees are two.
Each meets D_epsilon: if it contains O this is immediate; otherwise
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md gives its actual
inner point rho e with 0<rho<=d-1. At d<=1 that theorem instead
forces closed origin containment.

Let e be the genuine radial direction of L. The unchanged V equations
give the actual U--V application and support

    p_UV=(r_L-w_V)e,
    r_L in {r,d}, w_V in {1,sqrt(2)},
    U subset {z:e.z<=r_L-w_V}.                         (2)

A genuine D leaf gives r_L-w_V<=r-1<-1/3<-epsilon,
contradicting the real near point of U. An S/diagonal V gives
d-sqrt(2)<-epsilon, since sqrt(2)>1+2epsilon. Therefore the full
original type cover leaves S/side, with p_UV=(d-1)e.

If d<1, U contains O closed but its displayed support is negative,
again impossible. For d>=1 put epsilon=d-1. The true U2 equations
give

    p_RU=(epsilon-w_U)e, w_U in {1,sqrt(2)},
    R subset {z:e.z<=epsilon-w_U}.                     (3)

The sharp contained-unit supporting-height bound gives
w_U-epsilon<=d, so w_U<=1+2epsilon<sqrt(2). Thus w_U=1. Both
actual radial applications in (2)--(3) have transverse coordinate
zero. Consequently the whole unchanged U is

    U=[epsilon-1,epsilon]e+J_U Je,
    0 belongs to its original closed unit interval J_U.

It contains O closed, including epsilon=0 and both original slider
endpoints. U is distinct from all four block units. The full
terminal-four closed-origin theorem now excludes the original
configuration, with R's possible original circle force retained.

### 6.2. The fork R--U, U--L, U--M

The actual U is an all-bridge body of true degree three. The branch
inequality makes its circle load zero. If it avoided O, the full
off-origin bridge theorem and the original atom-minimal selection
would force its actual degree to be exactly two. Hence O belongs
to the original closed U.

The same terminal-four closed-origin theorem excludes this U outside
the unchanged block. No sign is imposed on the R--U radial support;
in particular its critical zero application is covered directly,
not inserted into a strict negative-support theorem by continuity.
Both actual S/D terminal types and every original mask remain.

These two proofs supply all six whole root orbits:

| Row | Block/root | Outside tree | True root degree and other outside degrees |
| --- | --- | --- | --- |
| 19 | C4 at A | Path A-U-V-L | A3; U2,V2,L1 |
| 20 | Diamond at H | Path H-U-V-L | H4; U2,V2,L1 |
| 21 | Diamond at B | Path B-U-V-L | B3; U2,V2,L1 |
| 22 | C4 at A | Fork A-U, U-L,U-M | A3; U3,L1,M1 |
| 23 | Diamond at H | Fork H-U, U-L,U-M | H4; U3,L1,M1 |
| 24 | Diamond at B | Fork B-U, U-L,U-M | B3; U3,L1,M1 |

Every row keeps the other three block vertices at their genuine
block degrees and the two original arbitrary completion units.

## 7. Exact whole-placement remainder and verification boundary

The complete graph partition has 24 rows. Seventeen have complete
source-level exits: rows 1--6,8,10--12,18--24. This count includes
fresh joins still requiring full root and separate independent
reviews; it is not an assertion that all corresponding gates were
already accepted or published.

The exact seven original graph domains without a complete exit in
this source are:

| Remaining placement | Whole original forces that must remain |
| --- | --- |
| Three leaves at three C4 vertices | Three true degree-three genuine roots, true loaded unmarked degree-two body, all four cycle forces and all three leaf forces |
| Three leaves at both diamond hubs and one tip | Both true degree-four hubs, true degree-three genuine tip root, true loaded other tip2, the full hub chord and all three leaf forces |
| C4 adjacent arm root / leaf root | Both true degree-three cyclic roots, actual X2 arm transmitter, both other true cycle degrees2 and all their load masks |
| C4 opposite arm root / leaf root | Both true degree-three cyclic roots, actual X2 arm transmitter, both other true cycle degrees2 and all their load masks |
| Diamond arm at one hub / leaf at other hub | Both true degree-four hubs, both actual loaded tip2 stars, actual X2 and the full hub chord |
| Diamond arm at a hub / leaf at a tip | True arm hub4, other hub3, genuine tip root3, other tip2, actual X2 and every chord force |
| Diamond arm at a tip / leaf at a hub | True arm tip3, genuine hub root4, other hub3, other tip2, actual X2; this is not the preceding ordered forest |

For the first two, (1) is a complete necessary high-S restriction.
For the last five, the direct leaf is S by Section 5, but the remaining
arm type, radius, force, owner and mean domains retain their full
obligations until a complete additional proof covers them.

No two-bridge theorem is applied after adding a force to one of its
old private bodies. No whole C1.4.b3 closure, new fine ID, proof
percentage, unrestricted bound, equality result, Lean compilation
or CI result follows from this graph cover. The declared older global
prerequisite-chain audit remains distinct from the exact joins here.
